//! `sable test`: the tree-walking interpreter with trap semantics
//! (design §9). Every partial operation is checked exactly where the
//! verifier would emit a VC — overflow, bounds, division — and every
//! monitorable contract (pre, post, invariant, variant) is evaluated
//! dynamically via `speceval`. Unmonitorable clauses are reported as
//! skipped, never guessed.
//!
//! This is a dev tool in the sanitizer category: its results are not a
//! verification claim, and test functions are never verified.

use crate::ast::*;
use crate::span::LineMap;
use crate::speceval::{self, GhostDefs, SpecEnv, SpecVal};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum RtVal {
    Int(i128),
    Bool(bool),
    Arr(Rc<RefCell<Vec<i128>>>),
    Opt(Option<i128>),
    Unit,
}

pub struct TestReport {
    pub name: String,
    /// Err carries a rendered failure message.
    pub outcome: Result<(), String>,
    /// Clauses that could not be checked dynamically (text, reason).
    pub skipped: Vec<(String, String)>,
}

struct Trap {
    message: String,
    span: crate::span::Span,
}

type IResult<T> = Result<T, Trap>;

const FUEL: u64 = 50_000_000;

pub fn run_tests(program: &Program, source: &str, path: &str) -> Vec<TestReport> {
    let lines = LineMap::new(source);
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();

    program
        .fns
        .iter()
        .filter(|f| f.name.starts_with("test_"))
        .map(|test| {
            let mut interp = Interp {
                fns: &fns,
                ghosts: &ghosts,
                source,
                fuel: FUEL,
                skipped: Vec::new(),
            };
            let outcome = interp.call(test, Vec::new()).map(|_| ()).map_err(|trap| {
                let (line, col) = lines.line_col(trap.span.start);
                format!("{} ({path}:{line}:{col})", trap.message)
            });
            TestReport {
                name: test.name.clone(),
                outcome,
                skipped: interp.skipped,
            }
        })
        .collect()
}

enum Flow {
    Normal,
    Return(RtVal),
}

struct Interp<'a> {
    fns: &'a HashMap<&'a str, &'a Fn>,
    ghosts: &'a GhostDefs,
    source: &'a str,
    fuel: u64,
    skipped: Vec<(String, String)>,
}

struct Frame {
    vars: HashMap<String, RtVal>,
    /// Entry-state scalar params (post clauses mean entry values for
    /// by-value params) and entry snapshots of &mut arrays (`old a`).
    entry_scalars: HashMap<String, RtVal>,
    old_arrays: HashMap<String, Vec<i128>>,
}

impl<'a> Interp<'a> {
    fn call(&mut self, f: &'a Fn, args: Vec<RtVal>) -> IResult<RtVal> {
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            old_arrays: HashMap::new(),
        };
        for (p, v) in f.params.iter().zip(args) {
            if let RtVal::Arr(a) = &v {
                if matches!(p.ty, Ty::Array(_, Mutability::Mut)) {
                    frame.old_arrays.insert(p.name.clone(), a.borrow().clone());
                }
            } else {
                frame.entry_scalars.insert(p.name.clone(), v.clone());
            }
            frame.vars.insert(p.name.clone(), v);
        }

        for pre in &f.pres {
            self.check_clause(&frame, pre, None, &format!("pre of `{}`", f.name))?;
        }

        let flow = self.exec_block(&f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };

        for post in &f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}`", f.name),
            )?;
        }
        Ok(result)
    }

    /// Contract-clause check with the right environment: entry values for
    /// by-value params, current contents for arrays, snapshots for `old`.
    fn check_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        result: Option<&RtVal>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            let val = if let Some(entry) = frame.entry_scalars.get(name) {
                entry
            } else {
                v
            };
            if let Some(sv) = spec_of(val) {
                vars.insert(name.clone(), sv);
            }
        }
        if let Some(r) = result {
            if let Some(sv) = spec_of(r) {
                vars.insert("result".into(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.old_arrays.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped
                    .push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    /// Loop-clause check in the *current* frame (invariants speak about
    /// current values, including mutated by-value params).
    fn check_loop_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.old_arrays.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped
                    .push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    fn exec_block(&mut self, stmts: &[Stmt], frame: &mut Frame) -> IResult<Flow> {
        for stmt in stmts {
            match self.exec_stmt(stmt, frame)? {
                Flow::Normal => {}
                ret => return Ok(ret),
            }
        }
        Ok(Flow::Normal)
    }

    fn exec_stmt(&mut self, stmt: &Stmt, frame: &mut Frame) -> IResult<Flow> {
        self.burn(stmt_span(stmt))?;
        match stmt {
            Stmt::Decl { name, init, .. } => {
                if let Some(e) = init {
                    let v = self.eval(e, frame)?;
                    frame.vars.insert(name.clone(), v);
                }
                Ok(Flow::Normal)
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval(value, frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::ExprStmt(e) => {
                self.eval(e, frame)?;
                Ok(Flow::Normal)
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval_int(value, frame)?;
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!()
                };
                let len = a.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        message: format!(
                            "store index out of bounds: index {idx}, length {len}"
                        ),
                        span: *array_span,
                    });
                }
                a.borrow_mut()[idx as usize] = val;
                Ok(Flow::Normal)
            }
            Stmt::Return { value, .. } => {
                let v = match value {
                    Some(e) => self.eval(e, frame)?,
                    None => RtVal::Unit,
                };
                Ok(Flow::Return(v))
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                if self.eval_bool(cond, frame)? {
                    self.exec_block(then_block, frame)
                } else if let Some(eb) = else_block {
                    self.exec_block(eb, frame)
                } else {
                    Ok(Flow::Normal)
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                kw_span,
                body,
            } => {
                let mut prev_variant: Option<i128> = None;
                loop {
                    self.burn(*kw_span)?;
                    for inv in invariants {
                        self.check_loop_clause(frame, inv, "loop invariant")?;
                    }
                    if !self.eval_bool(cond, frame)? {
                        break;
                    }
                    if let Some(v) = variant {
                        if let Some(val) = self.variant_value(frame, v) {
                            if val < 0 {
                                return Err(Trap {
                                    message: format!(
                                        "loop variant is negative ({val}): {}",
                                        v.text
                                    ),
                                    span: v.span,
                                });
                            }
                            if let Some(prev) = prev_variant {
                                if val >= prev {
                                    return Err(Trap {
                                        message: format!(
                                            "loop variant did not decrease ({prev} → {val}): {}",
                                            v.text
                                        ),
                                        span: v.span,
                                    });
                                }
                            }
                            prev_variant = Some(val);
                        }
                    }
                    match self.exec_block(body, frame)? {
                        Flow::Normal => {}
                        ret => return Ok(ret),
                    }
                }
                Ok(Flow::Normal)
            }
        }
    }

    /// Evaluate a variant measure numerically by evaluating the program
    /// expression through the spec evaluator (variants are Int-valued).
    fn variant_value(&mut self, frame: &Frame, clause: &crate::scan::Clause) -> Option<i128> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.old_arrays.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_int_expr(&clause.text, &env) {
            Ok(n) => Some(n),
            Err(um) => {
                self.skipped
                    .push((clause.text.replace('\n', " "), um.0));
                None
            }
        }
    }

    fn eval_int(&mut self, e: &Expr, frame: &mut Frame) -> IResult<i128> {
        match self.eval(e, frame)? {
            RtVal::Int(n) => Ok(n),
            _ => unreachable!("checked: int expression"),
        }
    }

    fn eval_bool(&mut self, e: &Expr, frame: &mut Frame) -> IResult<bool> {
        match self.eval(e, frame)? {
            RtVal::Bool(b) => Ok(b),
            _ => unreachable!("checked: bool expression"),
        }
    }

    fn eval(&mut self, e: &Expr, frame: &mut Frame) -> IResult<RtVal> {
        self.burn(e.span)?;
        match &e.kind {
            ExprKind::IntLit(n) => Ok(RtVal::Int(*n)),
            ExprKind::BoolLit(b) => Ok(RtVal::Bool(*b)),
            ExprKind::Var(name) => Ok(frame.vars[name.as_str()].clone()),
            ExprKind::Len { array } => {
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                Ok(RtVal::Int(a.borrow().len() as i128))
            }
            ExprKind::Index { array, index, .. } => {
                let idx = self.eval_int(index, frame)?;
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                let arr = a.borrow();
                if idx < 0 || idx >= arr.len() as i128 {
                    return Err(Trap {
                        message: format!(
                            "index out of bounds: index {idx}, length {}",
                            arr.len()
                        ),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(arr[idx as usize]))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg, frame),
            ExprKind::SomeE(inner) => {
                let v = self.eval_int(inner, frame)?;
                Ok(RtVal::Opt(Some(v)))
            }
            ExprKind::NoneE => Ok(RtVal::Opt(None)),
            ExprKind::ArrayLit(elems) => {
                let mut v = Vec::with_capacity(elems.len());
                for el in elems {
                    v.push(self.eval_int(el, frame)?);
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(v))))
            }
            ExprKind::Borrow { array, .. } => Ok(frame.vars[array.as_str()].clone()),
            ExprKind::Unary { op, operand } => match op {
                UnOp::Not => {
                    let b = self.eval_bool(operand, frame)?;
                    Ok(RtVal::Bool(!b))
                }
                UnOp::Neg => {
                    let v = self.eval_int(operand, frame)?;
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    self.check_range(-v, it, e, "negation")?;
                    Ok(RtVal::Int(-v))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let l = self.eval_bool(lhs, frame)?;
                    // Short-circuit, matching the VC semantics.
                    return Ok(RtVal::Bool(match op {
                        BinOp::And => l && self.eval_bool(rhs, frame)?,
                        BinOp::Or => l || self.eval_bool(rhs, frame)?,
                        _ => unreachable!(),
                    }));
                }
                let a = self.eval_int(lhs, frame)?;
                let b = self.eval_int(rhs, frame)?;
                if op.is_comparison() {
                    return Ok(RtVal::Bool(match op {
                        BinOp::Lt => a < b,
                        BinOp::Le => a <= b,
                        BinOp::Gt => a > b,
                        BinOp::Ge => a >= b,
                        BinOp::Eq => a == b,
                        BinOp::Ne => a != b,
                        _ => unreachable!(),
                    }));
                }
                let Ty::Int(it) = e.ty.unwrap() else {
                    unreachable!()
                };
                let val = match op {
                    BinOp::Add => a + b,
                    BinOp::Sub => a - b,
                    BinOp::Mul => a.checked_mul(b).ok_or_else(|| Trap {
                        message: "multiplication exceeds i128 (ghost width)".into(),
                        span: e.span,
                    })?,
                    BinOp::Div | BinOp::Rem => {
                        if b == 0 {
                            return Err(Trap {
                                message: "division by zero".into(),
                                span: rhs.span,
                            });
                        }
                        if *op == BinOp::Div && it.signed() && a == it.min() && b == -1 {
                            return Err(Trap {
                                message: format!(
                                    "Euclidean quotient overflows: {}.min / -1",
                                    it.name()
                                ),
                                span: e.span,
                            });
                        }
                        if *op == BinOp::Div {
                            a.div_euclid(b)
                        } else {
                            a.rem_euclid(b)
                        }
                    }
                    _ => unreachable!(),
                };
                if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    self.check_range(val, it, e, op.symbol())?;
                }
                Ok(RtVal::Int(val))
            }
            ExprKind::Call { callee, args, .. } => {
                let f = self.fns[callee.as_str()];
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval(a, frame)?);
                }
                self.call(f, vals)
            }
        }
    }

    fn check_range(&self, val: i128, it: IntTy, e: &Expr, what: &str) -> IResult<()> {
        if val < it.min() || val > it.max() {
            let src = &self.source[e.span.start..e.span.end.min(self.source.len())];
            return Err(Trap {
                message: format!(
                    "overflow: `{src}` = {val} does not fit in `{}` ({what})",
                    it.name()
                ),
                span: e.span,
            });
        }
        Ok(())
    }

    fn burn(&mut self, span: crate::span::Span) -> IResult<()> {
        if self.fuel == 0 {
            return Err(Trap {
                message: "fuel exhausted (runaway loop or recursion?)".into(),
                span,
            });
        }
        self.fuel -= 1;
        Ok(())
    }
}

fn spec_of(v: &RtVal) -> Option<SpecVal> {
    Some(match v {
        RtVal::Int(n) => SpecVal::Int(*n),
        RtVal::Bool(b) => SpecVal::Bool(*b),
        RtVal::Arr(a) => SpecVal::Arr(a.borrow().clone()),
        RtVal::Opt(o) => SpecVal::Opt(*o),
        RtVal::Unit => return None,
    })
}

fn stmt_span(stmt: &Stmt) -> crate::span::Span {
    match stmt {
        Stmt::Decl { name_span, .. } | Stmt::Assign { name_span, .. } => *name_span,
        Stmt::If { cond, .. } => cond.span,
        Stmt::While { kw_span, .. } => *kw_span,
        Stmt::Return { span, .. } => *span,
        Stmt::Store { array_span, .. } => *array_span,
        Stmt::ExprStmt(e) => e.span,
    }
}

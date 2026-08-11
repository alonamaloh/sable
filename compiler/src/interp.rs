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
    Obj {
        class: usize,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
    },
    /// A raw pointer: allocation id plus byte offset (ADR 0025/0026).
    Ptr(i128, i128),
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
    /// This failure is the machine's `undef`, not a trap. The interpreter
    /// is allowed to be *more precise* than the machine — it says which
    /// rule was broken — as long as it agrees on the classification, which
    /// is what the differential harness compares (ADR 0025).
    undef: bool,
}

type IResult<T> = Result<T, Trap>;

const FUEL: u64 = 50_000_000;

pub fn run_tests(program: &Program, mods: &crate::modules::ModuleSet) -> Vec<TestReport> {
    let source = mods.combined_source.as_str();
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let classes = &program.classes;

    program
        .fns
        .iter()
        .filter(|f| f.name.starts_with("test_"))
        .map(|test| {
            let mut interp = Interp {
                fns: &fns,
                classes,
                ghosts: &ghosts,
                source,
                fuel: FUEL,
                skipped: Vec::new(),
                raw: RawHeap::default(),
            };
            let outcome = interp.call(test, Vec::new()).map(|_| ()).map_err(|trap| {
                let (file, line, col) = mods.locate(trap.span.start);
                format!("{} ({file}:{line}:{col})", trap.message)
            });
            TestReport {
                name: test.name.clone(),
                outcome,
                skipped: interp.skipped,
            }
        })
        .collect()
}

/// Run one zero-argument function, returning its value or the raw trap
/// message (no source location) — the interpreter side of the SVM
/// differential harness.
pub fn run_fn(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let f = fns[name];
    let mut interp = Interp {
        fns: &fns,
        classes: &program.classes,
        ghosts: &ghosts,
        source: mods.combined_source.as_str(),
        fuel: FUEL,
        skipped: Vec::new(),
        raw: RawHeap::default(),
    };
    interp.call(f, Vec::new()).map_err(|trap| {
        if trap.undef {
            format!("undef: {}", trap.message)
        } else {
            trap.message
        }
    })
}

enum Flow {
    Normal,
    Return(RtVal),
}

struct Interp<'a> {
    fns: &'a HashMap<&'a str, &'a Fn>,
    classes: &'a [ClassDecl],
    ghosts: &'a GhostDefs,
    source: &'a str,
    fuel: u64,
    skipped: Vec<(String, String)>,
    raw: RawHeap,
}

/// The interpreter's raw heap. It mirrors the SVM's: a fresh-provenance
/// counter and allocations that are marked dead rather than removed, so a
/// stale pointer stays distinguishable from a fresh one (ADR 0025).
///
/// Exposure is modelled the way the SVM models it — copy the array's
/// bytes into a fresh loan allocation, run the body, copy the final bytes
/// back — because that is what makes the escape rules observable: a
/// pointer that outlived its exposure would name a dead allocation.
#[derive(Default)]
struct RawHeap {
    next: i128,
    allocs: HashMap<i128, RawAlloc>,
}

struct RawAlloc {
    live: bool,
    /// `None` is uninitialized: distinct from any byte value.
    bytes: Vec<Option<i128>>,
}

impl RawHeap {
    fn fresh(&mut self, bytes: Vec<Option<i128>>) -> i128 {
        let id = self.next;
        self.next += 1;
        self.allocs.insert(id, RawAlloc { live: true, bytes });
        id
    }

    fn live_at(&self, alloc: i128, off: i128) -> Option<&RawAlloc> {
        let al = self.allocs.get(&alloc)?;
        if al.live && off >= 0 && (off as usize) < al.bytes.len() {
            Some(al)
        } else {
            None
        }
    }
}

struct Frame {
    vars: HashMap<String, RtVal>,
    /// Entry-state scalar params (post clauses mean entry values for
    /// by-value params) and entry snapshots of &mut state (`old a`,
    /// `old self`).
    entry_scalars: HashMap<String, RtVal>,
    olds: HashMap<String, SpecVal>,
    /// Member context: the class index and its field storage.
    self_ctx: Option<(usize, Rc<RefCell<HashMap<String, RtVal>>>)>,
}

impl<'a> Interp<'a> {
    /// The deterministic test shims. An extern has no Sable body, so
    /// `sable test` has to supply one — and it is keyed on the *audit id*,
    /// not the name, because the id is what names the contract version the
    /// program was verified against (ADR 0027).
    ///
    /// An unknown id traps. Running the body as a no-op would let a
    /// contract appear to hold because nothing happened, which is the one
    /// outcome a monitor must never produce.
    fn call_extern(&mut self, f: &'a Fn, args: Vec<RtVal>, span: crate::span::Span)
        -> IResult<RtVal> {
        let info = f.extern_info.as_ref().expect("checked: extern");
        match info.audit_id.as_str() {
            "test.fill.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n), RtVal::Int(v)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                else {
                    unreachable!("checked: (raw<u8>, u64, u8)")
                };
                for i in 0..n {
                    if self.raw.live_at(a, off + i).is_none() {
                        return Err(Trap {
                            undef: true,
                            message: format!(
                                "`{}` writes out of bounds: {a}+{}",
                                f.name,
                                off + i
                            ),
                            span,
                        });
                    }
                    self.raw
                        .allocs
                        .get_mut(&a)
                        .expect("live_at checked")
                        .bytes[(off + i) as usize] = Some(v);
                }
                Ok(RtVal::Unit)
            }
            "test.checksum.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n)) = (args[0].clone(), args[1].clone())
                else {
                    unreachable!("checked: (raw<u8>, u64)")
                };
                let mut sum: i128 = 0;
                for i in 0..n {
                    match self.raw.live_at(a, off + i).map(|al| al.bytes[(off + i) as usize]) {
                        Some(Some(b)) => sum += b,
                        _ => {
                            return Err(Trap {
                                undef: true,
                                message: format!(
                                    "`{}` reads out of bounds or uninitialized: {a}+{}",
                                    f.name,
                                    off + i
                                ),
                                span,
                            });
                        }
                    }
                }
                Ok(RtVal::Int(sum))
            }
            other => Err(Trap {
                undef: false,
                message: format!(
                    "no test shim for audited extern `{}` (audit id `{other}`)",
                    f.name
                ),
                span,
            }),
        }
    }

    fn call(&mut self, f: &'a Fn, args: Vec<RtVal>) -> IResult<RtVal> {
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        };
        for (p, v) in f.params.iter().filter(|p| !p.ty.is_resource()).zip(args) {
            match (&v, p.ty) {
                (RtVal::Arr(a), Ty::Array(_, Mutability::Mut)) => {
                    frame
                        .olds
                        .insert(p.name.clone(), SpecVal::Arr(a.borrow().clone()));
                }
                // `&mut C`: the borrow shares storage with the caller, so
                // the bare name reads the current state and `old p` needs
                // the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                (RtVal::Arr(_), _) => {}
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
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
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        if let Some(r) = result {
            if let Some(sv) = spec_of(r) {
                vars.insert("result".into(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
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
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    fn exec_block(&mut self, stmts: &[Stmt], frame: &mut Frame) -> IResult<Flow> {
        let mut class_locals: Vec<String> = Vec::new();
        let mut out = Flow::Normal;
        for stmt in stmts {
            if let Stmt::VarDecl { name, .. } = stmt {
                class_locals.push(name.clone());
            }
            match self.exec_stmt(stmt, frame)? {
                Flow::Normal => {}
                ret => {
                    out = ret;
                    break;
                }
            }
        }
        // RAII: drop block-local class values in reverse declaration
        // order; the class invariant is assumed at deinit entry
        // (design §7) — check it dynamically here.
        for name in class_locals.iter().rev() {
            if let Some(RtVal::Obj { class, fields }) = frame.vars.get(name).cloned() {
                self.check_invariants_at(&self.classes[class].clone(), &fields, name)?;
                frame.vars.remove(name);
            }
        }
        Ok(out)
    }

    fn check_invariants_at(
        &mut self,
        class: &ClassDecl,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        let obj = RtVal::Obj {
            class: 0,
            fields: fields.clone(),
        };
        if let Some(sv) = spec_of(&obj) {
            vars.insert("self".into(), sv);
        }
        for (k, v) in fields.borrow().iter() {
            if let Some(sv) = spec_of(v) {
                vars.insert(k.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: self.ghosts,
        };
        for inv in &class.invariants {
            match speceval::eval_clause(&inv.text, &env) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "class invariant of `{}` violated at `{what}`: {}",
                            class.name,
                            inv.text.replace('\n', " ")
                        ),
                        span: inv.span,
                    });
                }
                Err(um) => {
                    self.skipped.push((inv.text.replace('\n', " "), um.0));
                }
            }
        }
        Ok(())
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
                // Reassigning a class local drops the old value: its
                // invariant is checked exactly as at scope-end RAII.
                if let Some(RtVal::Obj { class, fields }) = frame.vars.get(name).cloned() {
                    self.check_invariants_at(&self.classes[class].clone(), &fields, name)?;
                }
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            // `unsafe { ... }` is a marker: the block runs like any other.
            Stmt::Unsafe { body, .. } => self.exec_block(body, frame),
            // Exposure: copy the array's bytes into a fresh loan
            // allocation, run the body, copy the final bytes back, and
            // kill the allocation. Modelling it as a real copy is what
            // makes a leaked pointer observable at runtime rather than
            // silently fine (ADR 0026).
            Stmt::Expose {
                kw_span,
                array,
                mutable,
                ptr,
                res,
                body,
                ..
            } => {
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!("checked: u8 array")
                };
                let bytes: Vec<Option<i128>> = a.borrow().iter().map(|v| Some(*v)).collect();
                let n = bytes.len();
                let alloc = self.raw.fresh(bytes);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                // The resource has no runtime representation (ADR 0024);
                // the binding exists so the body's names resolve.
                frame.vars.insert(res.clone(), RtVal::Unit);
                let flow = self.exec_block(body, frame)?;
                let final_bytes = self
                    .raw
                    .allocs
                    .get(&alloc)
                    .map(|al| al.bytes.clone())
                    .expect("the loan allocation is ours");
                if *mutable {
                    for (i, b) in final_bytes.iter().enumerate().take(n) {
                        match b {
                            Some(v) => a.borrow_mut()[i] = *v,
                            None => {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "exposure of `{array}` ends with byte {i} \
                                         uninitialized"
                                    ),
                                    span: *kw_span,
                                });
                            }
                        }
                    }
                }
                if let Some(al) = self.raw.allocs.get_mut(&alloc) {
                    al.live = false;
                }
                frame.vars.remove(ptr.as_str());
                frame.vars.remove(res.as_str());
                Ok(flow)
            }
            Stmt::ExprStmt(e) => {
                self.eval(e, frame)?;
                Ok(Flow::Normal)
            }
            Stmt::Assert(clause) => {
                self.check_clause(frame, clause, None, "inline assert")?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl { name, init, .. } => {
                let v = self.eval(init, frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldAssign { field, value, .. } => {
                let v = self.eval(value, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                fields.borrow_mut().insert(field.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval_int(value, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field initialized"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
                        span: *field_span,
                    });
                }
                arr.borrow_mut()[idx as usize] = val;
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
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
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
                                    undef: false,
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
                                        undef: false,
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
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_int_expr(&clause.text, &env) {
            Ok(n) => Some(n),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                None
            }
        }
    }

    fn construct(
        &mut self,
        ci: usize,
        init_name: &str,
        args: Vec<RtVal>,
        span: crate::span::Span,
    ) -> IResult<RtVal> {
        self.burn(span)?;
        let class = self.classes[ci].clone();
        let ifn = class
            .inits
            .iter()
            .find(|i| i.name == init_name)
            .expect("checked: init exists")
            .clone();
        let fields = Rc::new(RefCell::new(HashMap::new()));
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        for (p, v) in ifn.params.iter().zip(args) {
            match (&v, p.ty) {
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &ifn.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.exec_block(&ifn.body, &mut frame)?;
        for post in &ifn.posts {
            self.check_clause(
                &frame,
                post,
                None,
                &format!("post of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.check_invariants_at(
            &class,
            &fields,
            &format!("{}::{} exit", class.name, ifn.name),
        )?;
        Ok(RtVal::Obj { class: ci, fields })
    }

    fn invoke(
        &mut self,
        ci: usize,
        method: &str,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
        args: Vec<RtVal>,
    ) -> IResult<RtVal> {
        let class = self.classes[ci].clone();
        let m = class
            .methods
            .iter()
            .find(|m| m.f.name == method)
            .expect("checked: method exists")
            .clone();
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        // Entry snapshot for `old self` (and post-checking of by-value
        // params).
        let entry_obj = RtVal::Obj {
            class: ci,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        };
        if let Some(sv) = spec_of(&entry_obj) {
            frame.olds.insert("self".into(), sv);
        }
        for (p, v) in m.f.params.iter().zip(args) {
            match (&v, p.ty) {
                // `&mut C`: the borrow shares storage with the caller, so
                // `old p` needs the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &m.f.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{method}`", class.name),
            )?;
        }
        let flow = self.exec_block(&m.f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };
        if m.self_kind == SelfKind::Mut {
            self.check_invariants_at(&class, &fields, &format!("{}::{method} exit", class.name))?;
        }
        for post in &m.f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}::{method}`", class.name),
            )?;
        }
        Ok(result)
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
            // Resource transformations redistribute authority, which is
            // a static notion: at runtime there is nothing to move and
            // nothing to return (ADR 0024).
            ExprKind::ResOp { .. } => Ok(RtVal::Unit),
            // The raw operations. Each classification here must match the
            // machine's: a trap is a trap, and everything the SVM calls
            // `undef` is a trap with a precise message — the reference
            // interpreter may say *which* rule was broken while agreeing
            // on the outcome class (ADR 0025).
            ExprKind::RawOp { op, args, .. } => {
                let vals: Vec<RtVal> = {
                    let mut vs = Vec::with_capacity(args.len());
                    for a in args {
                        vs.push(self.eval(a, frame)?);
                    }
                    vs
                };
                let ptr_at = |i: usize| match vals[i] {
                    RtVal::Ptr(a, o) => (a, o),
                    _ => unreachable!("checked: raw<u8> argument"),
                };
                let int_at = |i: usize| match vals[i] {
                    RtVal::Int(n) => n,
                    _ => unreachable!("checked: integer argument"),
                };
                // Every way a raw operation can fail is the machine's
                // `undef`: the static semantics is what makes these
                // unreachable, so there is no defined runtime behavior to
                // trap into (ADR 0025).
                let bad = |msg: String| Trap {
                    undef: true,
                    message: msg,
                    span: e.span,
                };
                match op {
                    RawOp::Offset => {
                        let (a, o) = ptr_at(0);
                        Ok(RtVal::Ptr(a, o + int_at(1)))
                    }
                    RawOp::Load8 => {
                        let (a, o) = ptr_at(0);
                        match self.raw.live_at(a, o).map(|al| al.bytes[o as usize]) {
                            Some(Some(b)) => Ok(RtVal::Int(b)),
                            Some(None) => Err(bad(format!(
                                "raw_load8 reads uninitialized byte {o} of allocation {a}"
                            ))),
                            None => Err(bad(format!(
                                "raw_load8 out of bounds or after free: {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::Store8 => {
                        let (a, o) = ptr_at(0);
                        let w = int_at(1);
                        if self.raw.live_at(a, o).is_none() {
                            return Err(bad(format!(
                                "raw_store8 out of bounds or after free: {a}+{o}"
                            )));
                        }
                        self.raw
                            .allocs
                            .get_mut(&a)
                            .expect("live_at checked")
                            .bytes[o as usize] = Some(w);
                        Ok(RtVal::Unit)
                    }
                    RawOp::Copy => {
                        let (sa, so) = ptr_at(0);
                        let (da, do_) = ptr_at(1);
                        let n = int_at(2);
                        for i in 0..n {
                            let b = match self
                                .raw
                                .live_at(sa, so + i)
                                .map(|al| al.bytes[(so + i) as usize])
                            {
                                Some(Some(b)) => b,
                                Some(None) => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping reads uninitialized byte \
                                         {} of allocation {sa}",
                                        so + i
                                    )));
                                }
                                None => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping source out of bounds: \
                                         {sa}+{}",
                                        so + i
                                    )));
                                }
                            };
                            if self.raw.live_at(da, do_ + i).is_none() {
                                return Err(bad(format!(
                                    "raw_copy_nonoverlapping destination out of bounds: \
                                     {da}+{}",
                                    do_ + i
                                )));
                            }
                            self.raw
                                .allocs
                                .get_mut(&da)
                                .expect("live_at checked")
                                .bytes[(do_ + i) as usize] = Some(b);
                        }
                        Ok(RtVal::Unit)
                    }
                }
            }

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
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(arr[idx as usize]))
            }
            ExprKind::IsSome { operand } => {
                let RtVal::Opt(o) = self.eval(operand, frame)? else {
                    unreachable!("checked: option operand")
                };
                Ok(RtVal::Bool(o.is_some()))
            }
            ExprKind::OptValue { operand } => {
                let RtVal::Opt(o) = self.eval(operand, frame)? else {
                    unreachable!("checked: option operand")
                };
                match o {
                    Some(v) => Ok(RtVal::Int(v)),
                    None => Err(Trap {
                        undef: false,
                        message: "`.value` of an empty option".into(),
                        span: e.span,
                    }),
                }
            }
            ExprKind::TraitCall { .. } => {
                unreachable!("trait calls exist only in templates, never executed")
            }
            ExprKind::ClassField { obj, field, .. } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let v = fields.borrow()[field.as_str()].clone();
                Ok(v)
            }
            ExprKind::ClassFieldLen { obj, field } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let n = a.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::ClassFieldIndex {
                obj, field, index, ..
            } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let idx = self.eval_int(index, frame)?;
                let arr = a.borrow();
                if idx < 0 || idx as usize >= arr.len() {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(arr[idx as usize]))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg, frame),
            ExprKind::Narrow { target, arg } => {
                let v = self.eval_int(arg, frame)?;
                if v < target.min() || v > target.max() {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "narrow out of range: {v} does not fit in `{}`",
                            target.name()
                        ),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(v))
            }
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
            ExprKind::Borrow { array, field, .. } => {
                let base = if array == "self" {
                    let (class, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                    RtVal::Obj { class, fields }
                } else {
                    frame.vars[array.as_str()].clone()
                };
                match field {
                    // `&x.f` — borrow the field's value, not the base
                    // (ADR 0020). Sharing the Rc is the borrow.
                    Some(f) => {
                        let RtVal::Obj { fields, .. } = base else {
                            unreachable!("checked: class base")
                        };
                        let v = fields.borrow()[f.as_str()].clone();
                        Ok(v)
                    }
                    None => Ok(base),
                }
            }
            ExprKind::AllocArray { len, init, .. } => {
                let n = self.eval_int(len, frame)?;
                let v0 = self.eval_int(init, frame)?;
                // Defined allocation-failure behavior: the named OOM trap.
                if n < 0 || n > 50_000_000 {
                    return Err(Trap {
                        undef: false,
                        message: format!("OOM trap: alloc_array of length {n}"),
                        span: e.span,
                    });
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(vec![v0; n as usize]))))
            }
            ExprKind::SelfField { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let v = fields
                    .borrow()
                    .get(field.as_str())
                    .cloned()
                    .expect("checked: field initialized");
                Ok(v)
            }
            ExprKind::SelfFieldLen { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let n = arr.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::SelfFieldIndex { field, index } => {
                let idx = self.eval_int(index, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {len}"),
                        span: e.span,
                    });
                }
                let v = arr.borrow()[idx as usize];
                Ok(RtVal::Int(v))
            }
            ExprKind::CtorCall {
                class, init, args, ..
            } => {
                let ci = self
                    .classes
                    .iter()
                    .position(|c| c.name == *class)
                    .expect("checked: class exists");
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval(a, frame)?);
                }
                self.construct(ci, init, vals, e.span)
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let RtVal::Obj { class, fields } = frame.vars[recv.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval(a, frame)?);
                }
                self.invoke(class, method, fields, vals)
            }
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
                        undef: false,
                        message: "multiplication exceeds i128 (ghost width)".into(),
                        span: e.span,
                    })?,
                    BinOp::Div | BinOp::Rem => {
                        if b == 0 {
                            return Err(Trap {
                                undef: false,
                                message: "division by zero".into(),
                                span: rhs.span,
                            });
                        }
                        if *op == BinOp::Div && it.signed() && a == it.min() && b == -1 {
                            return Err(Trap {
                                undef: false,
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
                // Resource arguments are erased: authority is a static
                // notion, so it has no runtime representation to pass and
                // the callee's runtime signature does not have the
                // parameter at all (ADR 0024). Both sides drop the same
                // positions, so the remaining ones still line up.
                let mut vals = Vec::with_capacity(args.len());
                for (a, p) in args.iter().zip(&f.params) {
                    if p.ty.is_resource() {
                        continue;
                    }
                    vals.push(self.eval(a, frame)?);
                }
                if f.extern_info.is_some() {
                    // The foreign implementation receives only ABI values:
                    // resources were already dropped above.
                    return self.call_extern(f, vals, e.span);
                }
                self.call(f, vals)
            }
        }
    }

    fn check_range(&self, val: i128, it: IntTy, e: &Expr, what: &str) -> IResult<()> {
        if val < it.min() || val > it.max() {
            let src = &self.source[e.span.start..e.span.end.min(self.source.len())];
            return Err(Trap {
                undef: false,
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
                undef: false,
                message: "fuel exhausted (runaway loop or recursion?)".into(),
                span,
            });
        }
        self.fuel -= 1;
        Ok(())
    }
}

fn deep_copy(v: &RtVal) -> RtVal {
    match v {
        RtVal::Arr(a) => RtVal::Arr(Rc::new(RefCell::new(a.borrow().clone()))),
        RtVal::Obj { class, fields } => RtVal::Obj {
            class: *class,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        },
        other => other.clone(),
    }
}

fn spec_of(v: &RtVal) -> Option<SpecVal> {
    Some(match v {
        RtVal::Int(n) => SpecVal::Int(*n),
        RtVal::Bool(b) => SpecVal::Bool(*b),
        RtVal::Arr(a) => SpecVal::Arr(a.borrow().clone()),
        RtVal::Opt(o) => SpecVal::Opt(*o),
        RtVal::Obj { fields, .. } => SpecVal::Obj(
            fields
                .borrow()
                .iter()
                .filter_map(|(k, v)| spec_of(v).map(|sv| (k.clone(), sv)))
                .collect(),
        ),
        // A pointer has no specification value: contracts speak about
        // views, and a view is not something the monitor can see.
        RtVal::Ptr(..) => return None,
        RtVal::Unit => return None,
    })
}

fn stmt_span(stmt: &Stmt) -> crate::span::Span {
    match stmt {
        Stmt::Unsafe { kw_span, .. } | Stmt::Expose { kw_span, .. } => *kw_span,
        Stmt::Decl { name_span, .. } | Stmt::Assign { name_span, .. } => *name_span,
        Stmt::Assert(c) => c.line_span,
        Stmt::If { cond, .. } => cond.span,
        Stmt::While { kw_span, .. } => *kw_span,
        Stmt::Return { span, .. } => *span,
        Stmt::Store { array_span, .. } => *array_span,
        Stmt::ExprStmt(e) => e.span,
        Stmt::VarDecl { name_span, .. } => *name_span,
        Stmt::FieldAssign { field_span, .. } => *field_span,
        Stmt::FieldStore { field_span, .. } => *field_span,
    }
}

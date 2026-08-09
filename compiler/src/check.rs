//! Typechecking for the M0 subset: exact-width integer types with no
//! implicit conversions, expected-type propagation into literals, definite
//! initialization (both-branches rule), all-paths-return, and call-graph
//! acyclicity (recursion needs measures — M1).
//!
//! The checker writes types into the AST (`Expr::ty`) for the VC generator.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{HashMap, HashSet};

pub struct FnSig {
    pub params: Vec<Param>,
    pub ret: Ty,
}

pub struct CheckResult {
    pub sigs: HashMap<String, FnSig>,
}

type CResult<T> = Result<T, Diagnostic>;

struct VarInfo {
    ty: Ty,
    initialized: bool,
}

struct Ctx<'a> {
    sigs: &'a HashMap<String, FnSig>,
    vars: HashMap<String, VarInfo>,
    /// All names ever declared in this function (M0 rule: locals and
    /// parameters must have pairwise-distinct names — keeps path-splitting
    /// in the VC generator scope-free).
    declared: HashSet<String>,
    /// Callees referenced by the current function (for cycle detection).
    calls: Vec<String>,
}

pub fn check(program: &mut Program) -> CResult<CheckResult> {
    // Pass 1: collect signatures (contracts come along on the Fn itself).
    let mut sigs: HashMap<String, FnSig> = HashMap::new();
    for f in &program.fns {
        if sigs.contains_key(&f.name) {
            return Err(Diagnostic {
                name: "type.duplicate_function".into(),
                title: format!("function `{}` is defined twice", f.name),
                span: f.name_span,
                label: "second definition here".into(),
                notes: vec![],
            });
        }
        if f.ret == Ty::Bool {
            return Err(Diagnostic {
                name: "type.m0_bool_return".into(),
                title: format!("function `{}` returns `bool`", f.name),
                span: f.name_span,
                label: "bool-valued functions are not supported in M0".into(),
                notes: vec![("note".into(), "see docs/PLAN.md, M0 scope".into())],
            });
        }
        sigs.insert(
            f.name.clone(),
            FnSig {
                params: f.params.clone(),
                ret: f.ret,
            },
        );
    }

    // Pass 2: check bodies.
    let mut call_graph: HashMap<String, Vec<String>> = HashMap::new();
    for f in &mut program.fns {
        let mut ctx = Ctx {
            sigs: &sigs,
            vars: HashMap::new(),
            declared: HashSet::new(),
            calls: Vec::new(),
        };
        for p in &f.params {
            if !ctx.declared.insert(p.name.clone()) {
                return Err(Diagnostic {
                    name: "type.duplicate_name".into(),
                    title: format!("duplicate parameter name `{}`", p.name),
                    span: p.span,
                    label: "already declared".into(),
                    notes: vec![],
                });
            }
            ctx.vars.insert(
                p.name.clone(),
                VarInfo {
                    ty: p.ty,
                    initialized: true,
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret)?;
        if !returns {
            return Err(Diagnostic {
                name: "type.missing_return".into(),
                title: format!("not all paths in `{}` return a value", f.name),
                span: f.name_span,
                label: "this function must return on every path".into(),
                notes: vec![],
            });
        }
        call_graph.insert(f.name.clone(), ctx.calls);
    }

    // Pass 3: recursion is an M1 feature (needs measures).
    if let Some(cycle_member) = find_cycle(&call_graph) {
        let f = program.fns.iter().find(|f| f.name == cycle_member).unwrap();
        return Err(Diagnostic {
            name: "type.m0_recursion".into(),
            title: format!("`{}` is (mutually) recursive", f.name),
            span: f.name_span,
            label: "recursion requires a decreasing measure (M1)".into(),
            notes: vec![("note".into(), "see docs/PLAN.md, M0 scope".into())],
        });
    }

    Ok(CheckResult { sigs })
}

/// Returns whether every path through the block returns.
fn check_block(ctx: &mut Ctx, stmts: &mut [Stmt], ret_ty: Ty) -> CResult<bool> {
    let mut returned = false;
    for stmt in stmts.iter_mut() {
        if returned {
            let span = stmt_span(stmt);
            return Err(Diagnostic {
                name: "type.unreachable".into(),
                title: "unreachable statement".into(),
                span,
                label: "every path above has already returned".into(),
                notes: vec![],
            });
        }
        match stmt {
            Stmt::Decl {
                ty,
                name,
                name_span,
                init,
            } => {
                if !ctx.declared.insert(name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_name".into(),
                        title: format!("duplicate variable name `{name}`"),
                        span: *name_span,
                        label: "already declared in this function".into(),
                        notes: vec![(
                            "note".into(),
                            "M0 requires all locals in a function to have distinct names".into(),
                        )],
                    });
                }
                if let Some(e) = init {
                    check_expr(ctx, e, Some(*ty))?;
                }
                ctx.vars.insert(
                    name.clone(),
                    VarInfo {
                        ty: *ty,
                        initialized: init.is_some(),
                    },
                );
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let ty = match ctx.vars.get(name.as_str()) {
                    Some(v) => v.ty,
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("assignment to undeclared variable `{name}`"),
                            span: *name_span,
                            label: "not declared".into(),
                            notes: vec![],
                        })
                    }
                };
                check_expr(ctx, value, Some(ty))?;
                ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                check_expr(ctx, cond, Some(Ty::Bool))?;
                let before: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                let then_ret = check_block(ctx, then_block, ret_ty)?;
                let after_then: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                for (name, init) in &before {
                    if let Some(v) = ctx.vars.get_mut(name.as_str()) {
                        v.initialized = *init;
                    }
                }
                let else_ret = match else_block {
                    Some(b) => check_block(ctx, b, ret_ty)?,
                    None => false,
                };
                // A variable is initialized after the `if` iff it is
                // initialized on every path that falls through to here.
                // A returning branch contributes no fall-through path;
                // "no else" contributes the pre-`if` state.
                let after_else: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                for (name, v) in ctx.vars.iter_mut() {
                    let was = before.get(name).copied().unwrap_or(false);
                    let mut reaching_inits = Vec::new();
                    if !then_ret {
                        reaching_inits.push(after_then.get(name).copied().unwrap_or(false));
                    }
                    if !else_ret {
                        reaching_inits.push(match else_block {
                            Some(_) => after_else.get(name).copied().unwrap_or(false),
                            None => was,
                        });
                    }
                    v.initialized = if reaching_inits.is_empty() {
                        was // join unreachable; state is irrelevant
                    } else {
                        reaching_inits.iter().all(|b| *b)
                    };
                }
                returned = then_ret && else_ret;
            }
            Stmt::Return { value, span } => {
                check_expr(ctx, value, Some(ret_ty)).map_err(|d| d)?;
                let _ = span;
                returned = true;
            }
        }
    }
    Ok(returned)
}

fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Decl { name_span, .. } => *name_span,
        Stmt::Assign { name_span, .. } => *name_span,
        Stmt::If { cond, .. } => cond.span,
        Stmt::Return { span, .. } => *span,
    }
}

/// Typecheck an expression. `expected` propagates into integer literals
/// (design: literals adopt the type context demands; no implicit
/// conversions anywhere else).
fn check_expr(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>) -> CResult<Ty> {
    let ty = infer_expr(ctx, e, expected)?;
    if let Some(exp) = expected {
        if ty != exp {
            return Err(Diagnostic {
                name: "type.mismatch".into(),
                title: format!("type mismatch: expected `{}`, found `{}`", exp.name(), ty.name()),
                span: e.span,
                label: format!("this has type `{}`", ty.name()),
                notes: vec![(
                    "note".into(),
                    "Sable has no implicit conversions; use `widen<T>` (M1) for widening".into(),
                )],
            });
        }
    }
    Ok(ty)
}

fn infer_expr(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>) -> CResult<Ty> {
    let ty = match &mut e.kind {
        ExprKind::IntLit(n) => {
            let t = match expected {
                Some(Ty::Int(t)) => t,
                Some(Ty::Bool) => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: "expected `bool`, found an integer literal".into(),
                        span: e.span,
                        label: "integer literal".into(),
                        notes: vec![],
                    })
                }
                None => {
                    return Err(Diagnostic {
                        name: "type.ambiguous_literal".into(),
                        title: format!("cannot infer the type of literal `{n}`"),
                        span: e.span,
                        label: "no type context".into(),
                        notes: vec![(
                            "note".into(),
                            "give the literal context, e.g. bind it to a typed variable".into(),
                        )],
                    })
                }
            };
            if *n < t.min() || *n > t.max() {
                return Err(Diagnostic {
                    name: "type.literal_out_of_range".into(),
                    title: format!("literal `{n}` does not fit in `{}`", t.name()),
                    span: e.span,
                    label: format!("`{}` holds {}..={}", t.name(), t.min(), t.max()),
                    notes: vec![],
                });
            }
            Ty::Int(t)
        }
        ExprKind::BoolLit(_) => Ty::Bool,
        ExprKind::Var(name) => match ctx.vars.get(name.as_str()) {
            Some(v) => {
                if !v.initialized {
                    return Err(Diagnostic {
                        name: "type.uninitialized".into(),
                        title: format!("`{name}` may be read before initialization"),
                        span: e.span,
                        label: "not initialized on every path to this point".into(),
                        notes: vec![(
                            "note".into(),
                            "there is no default zero (design §2.3); initialize on all paths".into(),
                        )],
                    });
                }
                v.ty
            }
            None => {
                return Err(Diagnostic {
                    name: "type.unknown_variable".into(),
                    title: format!("unknown variable `{name}`"),
                    span: e.span,
                    label: "not declared".into(),
                    notes: vec![],
                })
            }
        },
        ExprKind::Unary { op, operand } => match op {
            UnOp::Neg => {
                let t = check_expr(ctx, operand, expected)?;
                match t {
                    Ty::Int(it) if it.signed() => t,
                    Ty::Int(_) => {
                        return Err(Diagnostic {
                            name: "type.neg_unsigned".into(),
                            title: "unary minus on an unsigned value".into(),
                            span: e.span,
                            label: "operand is unsigned".into(),
                            notes: vec![(
                                "note".into(),
                                "unsigned negation is modular; use `wrap()` when it lands (M1)"
                                    .into(),
                            )],
                        })
                    }
                    Ty::Bool => {
                        return Err(Diagnostic {
                            name: "type.mismatch".into(),
                            title: "unary minus on a `bool`".into(),
                            span: e.span,
                            label: "expected an integer".into(),
                            notes: vec![],
                        })
                    }
                }
            }
            UnOp::Not => {
                check_expr(ctx, operand, Some(Ty::Bool))?;
                Ty::Bool
            }
        },
        ExprKind::Binary { op, op_span, lhs, rhs } => {
            let op = *op;
            let op_span = *op_span;
            if op.is_arith() {
                let expected_int = match expected {
                    Some(Ty::Int(_)) => expected,
                    Some(Ty::Bool) => None, // will fail the outer expected check
                    None => None,
                };
                let t = infer_int_pair(ctx, lhs, rhs, expected_int, op_span)?;
                if matches!(op, BinOp::Div | BinOp::Rem) && t.signed() {
                    return Err(Diagnostic {
                        name: "type.m0_signed_div".into(),
                        title: "signed division/remainder is not supported in M0".into(),
                        span: op_span,
                        label: "signed `/` and `%` land in M1".into(),
                        notes: vec![(
                            "note".into(),
                            "C truncation semantics need Int.tdiv/Int.tmod on the Lean side \
                             (see docs/PLAN.md, M0 simplifications)"
                                .into(),
                        )],
                    });
                }
                Ty::Int(t)
            } else if op.is_comparison() {
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    // Allow int == int only in M0 (bool equality would need
                    // Prop-level iff in the VC encoding).
                }
                let _t = infer_int_pair(ctx, lhs, rhs, None, op_span)?;
                Ty::Bool
            } else {
                // && ||
                check_expr(ctx, lhs, Some(Ty::Bool))?;
                check_expr(ctx, rhs, Some(Ty::Bool))?;
                Ty::Bool
            }
        }
        ExprKind::Call {
            callee,
            callee_span,
            args,
        } => {
            let sig = match ctx.sigs.get(callee.as_str()) {
                Some(s) => s,
                None => {
                    return Err(Diagnostic {
                        name: "type.unknown_function".into(),
                        title: format!("call to unknown function `{callee}`"),
                        span: *callee_span,
                        label: "not defined in this module".into(),
                        notes: vec![],
                    })
                }
            };
            if args.len() != sig.params.len() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{callee}` takes {} argument(s), {} given",
                        sig.params.len(),
                        args.len()
                    ),
                    span: e.span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            let param_tys: Vec<Ty> = sig.params.iter().map(|p| p.ty).collect();
            let ret = sig.ret;
            for (arg, pty) in args.iter_mut().zip(param_tys) {
                if pty == Ty::Bool {
                    return Err(Diagnostic {
                        name: "type.m0_bool_arg".into(),
                        title: "bool-typed call arguments are not supported in M0".into(),
                        span: arg.span,
                        label: "bool argument".into(),
                        notes: vec![("note".into(), "see docs/PLAN.md, M0 scope".into())],
                    });
                }
                check_expr(ctx, arg, Some(pty))?;
            }
            ctx.calls.push(callee.clone());
            ret
        }
    };
    e.ty = Some(ty);
    Ok(ty)
}

/// Infer a same-typed integer pair, letting a literal side adopt the other
/// side's type (or the expected type when both need context).
fn infer_int_pair(
    ctx: &mut Ctx,
    lhs: &mut Expr,
    rhs: &mut Expr,
    expected: Option<Ty>,
    op_span: Span,
) -> CResult<IntTy> {
    let lhs_literal = is_literal_only(lhs);
    let rhs_literal = is_literal_only(rhs);
    let t = if lhs_literal && !rhs_literal {
        let t = int_of(ctx, rhs, expected, op_span)?;
        check_expr(ctx, lhs, Some(Ty::Int(t)))?;
        t
    } else {
        let t = int_of(ctx, lhs, expected, op_span)?;
        check_expr(ctx, rhs, Some(Ty::Int(t)))?;
        t
    };
    Ok(t)
}

fn int_of(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>, op_span: Span) -> CResult<IntTy> {
    match check_expr(ctx, e, expected)? {
        Ty::Int(t) => Ok(t),
        Ty::Bool => Err(Diagnostic {
            name: "type.mismatch".into(),
            title: "arithmetic/comparison on a `bool`".into(),
            span: op_span,
            label: "operands must be integers".into(),
            notes: vec![],
        }),
    }
}

fn is_literal_only(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::IntLit(_) => true,
        ExprKind::Unary {
            op: UnOp::Neg,
            operand,
        } => is_literal_only(operand),
        ExprKind::Binary { op, lhs, rhs, .. } if op.is_arith() => {
            is_literal_only(lhs) && is_literal_only(rhs)
        }
        _ => false,
    }
}

fn find_cycle(graph: &HashMap<String, Vec<String>>) -> Option<String> {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Unvisited,
        InProgress,
        Done,
    }
    let mut state: HashMap<&str, State> =
        graph.keys().map(|k| (k.as_str(), State::Unvisited)).collect();

    fn dfs<'a>(
        node: &'a str,
        graph: &'a HashMap<String, Vec<String>>,
        state: &mut HashMap<&'a str, State>,
    ) -> Option<String> {
        state.insert(node, State::InProgress);
        if let Some(callees) = graph.get(node) {
            for c in callees {
                match state.get(c.as_str()).copied() {
                    Some(State::InProgress) => return Some(c.clone()),
                    Some(State::Unvisited) => {
                        if let Some(found) = dfs(c.as_str(), graph, state) {
                            return Some(found);
                        }
                    }
                    _ => {}
                }
            }
        }
        state.insert(node, State::Done);
        None
    }

    let keys: Vec<&str> = graph.keys().map(|k| k.as_str()).collect();
    for k in keys {
        if state.get(k) == Some(&State::Unvisited) {
            if let Some(found) = dfs(k, graph, &mut state) {
                return Some(found);
            }
        }
    }
    None
}

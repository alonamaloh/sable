//! The compiler side of the SVM differential harness: lower a checked
//! function body in the machine's core subset to a Lean `List Stmt`
//! term over `lean/Sable/SVM.lean`, and canonicalize `interp.rs`
//! outcomes into the harness's wire format — which must match
//! `Config.render` on the Lean side character for character.
//!
//! Lowering is deliberately strict: anything outside the formalized
//! subset — calls, classes, option accessors, array literals, loop
//! invariants — is a hard error, never a silent skip, so the harness
//! cannot compare less than it claims to. The mandatory loop `variant`
//! is the one asymmetry: erased here (ghost, design §4) but monitored
//! by the interpreter, so a diff program's variants must hold.

use crate::ast::*;
use crate::interp::RtVal;

/// Lower a zero-argument function's body to a Lean `List Stmt` term.
pub fn lower_fn(f: &Fn) -> Result<String, String> {
    if !f.params.is_empty() {
        return Err("differential subjects must take no parameters".into());
    }
    lower_block(&f.body)
}

/// Lower any function to a `Prog.ofList` entry: `("name", ⟨[params],
/// body⟩)`. Parameters must be scalars — borrows are outside the
/// machine (arrays are owned values; `&mut` reflection back to the
/// caller has no machine analog yet).
pub fn lower_fn_entry(f: &Fn) -> Result<String, String> {
    for p in &f.params {
        match p.ty {
            Ty::Int(_) | Ty::Bool => {}
            _ => {
                return Err(format!(
                    "parameter `{}`: only scalar parameters are inside the SVM                      core subset (borrows are scoped out)",
                    p.name
                ));
            }
        }
    }
    let params: Vec<String> = f.params.iter().map(|p| format!("\"{}\"", p.name)).collect();
    Ok(format!(
        "(\"{}\", ⟨[{}], {}⟩)",
        f.name,
        params.join(", "),
        lower_block(&f.body)?
    ))
}

fn lower_block(stmts: &[Stmt]) -> Result<String, String> {
    let mut out = Vec::new();
    for s in stmts {
        if let Some(t) = lower_stmt(s)? {
            out.push(t);
        }
    }
    Ok(format!("[{}]", out.join(", ")))
}

fn lower_stmt(s: &Stmt) -> Result<Option<String>, String> {
    Ok(match s {
        // A ⊥ slot: the machine conflates "undeclared" with ⊥, and
        // definite initialization guarantees assignment-before-read.
        Stmt::Decl { init: None, .. } => None,
        Stmt::Decl {
            name,
            init: Some(e),
            ..
        } => Some(lower_bind(name, e)?),
        Stmt::VarDecl { name, init, .. } => Some(lower_bind(name, init)?),
        // `unsafe { ... }` is a marker with no machine step of its own.
        Stmt::Unsafe { body, .. } => {
            let inner = lower_block(body)?;
            // Splice the body in place: the block does not scope.
            Some(
                inner
                    .trim_start_matches('[')
                    .trim_end_matches(']')
                    .to_string(),
            )
        }
        Stmt::Expose { .. } => {
            return Err(
                "`unsafe expose` has no machine lowering yet: the loan-allocation model                  is normative but not wired into the differential harness"
                    .into(),
            )
        }
        Stmt::Assign { name, value, .. } => Some(lower_bind(name, value)?),
        Stmt::Store {
            array,
            index,
            value,
            ..
        } => Some(format!(
            "(.store \"{array}\" {} {})",
            lower_expr(index)?,
            lower_expr(value)?
        )),
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let els = match else_block {
                Some(b) => lower_block(b)?,
                None => "[]".into(),
            };
            Some(format!(
                "(.ite {} {} {})",
                lower_expr(cond)?,
                lower_block(then_block)?,
                els
            ))
        }
        Stmt::While {
            cond,
            invariants,
            body,
            ..
        } => {
            if !invariants.is_empty() {
                return Err(
                    "loop invariants are outside the differential subset (interp monitors \
                     them; the machine does not)"
                        .into(),
                );
            }
            Some(format!(
                "(.while {} {})",
                lower_expr(cond)?,
                lower_block(body)?
            ))
        }
        Stmt::Return { value: Some(e), .. } => Some(format!("(.ret {})", lower_expr(e)?)),
        Stmt::Return { value: None, .. } => {
            return Err("bare `return;` has no SVM form (fall off the end instead)".into());
        }
        // A call for effect: `f(args);` — the discarded-result form of
        // the machine's A-normal call.
        Stmt::ExprStmt(e) => match &e.kind {
            ExprKind::Call { callee, args, .. } => Some(lower_call(&None, callee, args)?),
            _ => {
                return Err("expression statements are outside the SVM core subset".into());
            }
        },
        Stmt::Assert(_) => {
            return Err("`/// assert` is outside the SVM core subset".into());
        }
        Stmt::FieldAssign { .. } | Stmt::FieldStore { .. } => {
            return Err("class members are outside the SVM core subset".into());
        }
    })
}

/// `x = e;` — an assign, or (A-normalized, ADR 0005) a call when `e`
/// is exactly a call; calls nested deeper stay outside the subset.
fn lower_bind(name: &str, e: &Expr) -> Result<String, String> {
    match &e.kind {
        ExprKind::Call { callee, args, .. } => lower_call(&Some(name.to_string()), callee, args),
        _ => Ok(format!("(.assign \"{name}\" {})", lower_expr(e)?)),
    }
}

fn lower_call(dst: &Option<String>, callee: &str, args: &[Expr]) -> Result<String, String> {
    let lowered: Result<Vec<String>, String> = args.iter().map(lower_expr).collect();
    let d = match dst {
        Some(x) => format!("(some \"{x}\")"),
        None => "none".into(),
    };
    Ok(format!(
        "(.call {d} \"{callee}\" [{}])",
        lowered?.join(", ")
    ))
}

fn lower_expr(e: &Expr) -> Result<String, String> {
    Ok(match &e.kind {
        ExprKind::IntLit(n) => {
            format!("(.intLit {} {})", lean_ty(expr_int_ty(e)?)?, int_lit(*n))
        }
        ExprKind::BoolLit(b) => format!("(.boolLit {b})"),
        ExprKind::Var(x) => format!("(.var \"{x}\")"),
        ExprKind::ResOp { op, .. } => {
            // Resource transformations are static: they redistribute
            // authority and there is nothing for the machine to do. A
            // differential subject containing one is a subject about
            // nothing, so it is an error rather than a silent erasure.
            return Err(format!(
                "`{}` is static: there is no machine step to compare",
                op.name()
            ));
        }
        ExprKind::RawOp { op, args, .. } => {
            let lowered: Result<Vec<String>, String> = args.iter().map(lower_expr).collect();
            let lowered = lowered?;
            match op {
                RawOp::Offset => format!("(.ptrAdd {} {})", lowered[0], lowered[1]),
                // The rest are statements in the machine (§ADR 0025), so
                // they cannot appear in expression position here; the
                // statement lowering handles them.
                _ => {
                    return Err(format!(
                        "`{}` is a statement in the machine, not an expression",
                        op.name()
                    ))
                }
            }
        }
        ExprKind::Unary { op, operand } => match op {
            UnOp::Not => format!("(.not {})", lower_expr(operand)?),
            UnOp::Neg => format!(
                "(.neg {} {})",
                lean_ty(expr_int_ty(e)?)?,
                lower_expr(operand)?
            ),
        },
        ExprKind::Binary { op, lhs, rhs, .. } => {
            let l = lower_expr(lhs)?;
            let r = lower_expr(rhs)?;
            match op {
                BinOp::And => format!("(.and {l} {r})"),
                BinOp::Or => format!("(.or {l} {r})"),
                BinOp::Lt => format!("(.cmp .lt {l} {r})"),
                BinOp::Le => format!("(.cmp .le {l} {r})"),
                BinOp::Gt => format!("(.cmp .gt {l} {r})"),
                BinOp::Ge => format!("(.cmp .ge {l} {r})"),
                BinOp::Eq => format!("(.cmp .eq {l} {r})"),
                BinOp::Ne => format!("(.cmp .ne {l} {r})"),
                BinOp::Add | BinOp::Sub | BinOp::Mul => {
                    let sym = match op {
                        BinOp::Add => ".add",
                        BinOp::Sub => ".sub",
                        _ => ".mul",
                    };
                    format!("(.arith {sym} {} {l} {r})", lean_ty(expr_int_ty(e)?)?)
                }
                BinOp::Div => format!("(.div {} {l} {r})", lean_ty(expr_int_ty(e)?)?),
                BinOp::Rem => format!("(.mod {} {l} {r})", lean_ty(expr_int_ty(e)?)?),
            }
        }
        ExprKind::Index { array, index, .. } => {
            format!("(.index \"{array}\" {})", lower_expr(index)?)
        }
        ExprKind::Len { array } => format!("(.len \"{array}\")"),
        ExprKind::Widen { target, arg } => {
            format!("(.widen {} {})", lean_ty(*target)?, lower_expr(arg)?)
        }
        ExprKind::Narrow { target, arg } => {
            format!("(.narrow {} {})", lean_ty(*target)?, lower_expr(arg)?)
        }
        ExprKind::SomeE(inner) => format!("(.someE {})", lower_expr(inner)?),
        ExprKind::NoneE => "(.noneE)".into(),
        ExprKind::AllocArray { len, init, .. } => format!(
            "(.allocArray {} {})",
            lower_expr(len)?,
            lower_expr(init)?
        ),
        ExprKind::Call { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::TraitCall { .. } => {
            return Err("calls are outside the SVM core subset".into());
        }
        ExprKind::IsSome { .. } | ExprKind::OptValue { .. } => {
            return Err("option accessors are outside the SVM core subset".into());
        }
        ExprKind::ArrayLit(_) => {
            return Err("array literals are outside the SVM core subset (use alloc_array)".into());
        }
        ExprKind::Borrow { .. } => {
            return Err("borrows are outside the SVM core subset".into());
        }
        ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. } => {
            return Err("class members are outside the SVM core subset".into());
        }
    })
}

fn int_lit(n: i128) -> String {
    if n < 0 { format!("({n})") } else { n.to_string() }
}

fn expr_int_ty(e: &Expr) -> Result<IntTy, String> {
    match e.ty {
        Some(Ty::Int(it)) => Ok(it),
        _ => Err("expression carries no integer type (unchecked program?)".into()),
    }
}

fn lean_ty(t: IntTy) -> Result<String, String> {
    match t {
        IntTy::TParam(_) => Err("type parameter survived monomorphization".into()),
        _ => Ok(format!(".{}", t.name())),
    }
}

/// Canonicalize an interpreter outcome into the harness wire format
/// (`done <val>` / `trap <name> <data>`), matching the Lean side's
/// `Config.render`. Unrecognized traps stay verbatim under an
/// `unclassified:` prefix so a comparison failure shows them.
pub fn canonical_outcome(res: Result<RtVal, String>) -> String {
    match res {
        Ok(v) => match v {
            RtVal::Unit => "done unit".into(),
            RtVal::Int(n) => format!("done int {n}"),
            RtVal::Bool(b) => format!("done bool {b}"),
            RtVal::Arr(a) => format!(
                "done arr [{}]",
                a.borrow()
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RtVal::Ptr(a, o) => format!("done ptr {a}+{o}"),
            RtVal::Opt(None) => "done opt none".into(),
            RtVal::Opt(Some(n)) => format!("done opt some {n}"),
            RtVal::Obj { .. } => "unclassified: class value".into(),
        },
        Err(msg) => classify_trap(&msg),
    }
}

/// Map `interp.rs`'s rendered trap messages onto the machine's
/// structural traps. This is a harness-only concern: the interpreter
/// speaks to humans, the machine speaks constructors, and the mapping
/// between them lives here and nowhere else.
fn classify_trap(msg: &str) -> String {
    if msg == "division by zero" {
        return "trap divByZero".into();
    }
    if let Some(rest) = msg.strip_prefix("Euclidean quotient overflows: ") {
        if let Some(ty) = rest.strip_suffix(".min / -1") {
            return format!("trap overflow {ty}");
        }
    }
    if let Some(len) = msg.strip_prefix("OOM trap: alloc_array of length ") {
        return format!("trap oom {len}");
    }
    if let Some(rest) = msg.strip_prefix("narrow out of range: ") {
        if let Some((v, tail)) = rest.split_once(" does not fit in `") {
            if let Some(ty) = tail.strip_suffix('`') {
                return format!("trap narrowOOB {ty} {v}");
            }
        }
    }
    // "index out of bounds: index {i}, length {len}" for loads;
    // stores prefix it with "store ".
    let idx = msg.strip_prefix("store ").unwrap_or(msg);
    if let Some(rest) = idx.strip_prefix("index out of bounds: index ") {
        if let Some((i, len)) = rest.split_once(", length ") {
            return format!("trap indexOOB {i} {len}");
        }
    }
    // "overflow: `{src}` = {val} does not fit in `{ty}` ({op})"
    if msg.starts_with("overflow: ") {
        if let Some(pos) = msg.rfind(" does not fit in `") {
            let tail = &msg[pos + " does not fit in `".len()..];
            if let Some(ty) = tail.split('`').next() {
                return format!("trap overflow {ty}");
            }
        }
    }
    format!("unclassified: {msg}")
}

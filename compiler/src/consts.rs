//! Top-level `const` declarations (ADR 0016): named compile-time
//! integer values, substituted into program expressions and clause
//! text before any later stage runs — downstream, a constant is
//! indistinguishable from the literal it names (so omega sees
//! numerals, the monitor evaluates numerals, and the verbatim-splice
//! invariant is untouched).

use crate::ast::{Expr, ExprKind, Fn, Program, Stmt};
use crate::diag::Diagnostic;
use crate::mono::subst_clause_text;
use std::collections::HashMap;

/// Validate the program's `const` declarations and substitute every
/// use. Runs on the merged (post-module-load) program, so imported
/// constants substitute the same as local ones.
pub fn apply(program: &mut Program) -> Result<(), Diagnostic> {
    if program.consts.is_empty() {
        return Ok(());
    }
    let mut values: HashMap<String, i128> = HashMap::new();
    let mut text_map: HashMap<String, String> = HashMap::new();
    for c in &program.consts {
        if values.insert(c.name.clone(), c.value).is_some() {
            return Err(Diagnostic {
                name: "const.duplicate".into(),
                title: format!("duplicate constant `{}`", c.name),
                span: c.name_span,
                label: "already declared".into(),
                notes: vec![],
            });
        }
        let (lo, hi) = (c.ty.min(), c.ty.max());
        if c.value < lo || c.value > hi {
            return Err(Diagnostic {
                name: "const.out_of_range".into(),
                title: format!("constant `{}` does not fit `{}`", c.name, c.ty.name()),
                span: c.span,
                label: format!("{} is outside [{lo}, {hi}]", c.value),
                notes: vec![],
            });
        }
        text_map.insert(c.name.clone(), c.value.to_string());
    }

    for f in program
        .fns
        .iter_mut()
        .chain(program.fn_templates.iter_mut())
    {
        subst_fn(f, &values, &text_map);
    }
    for cl in program
        .classes
        .iter_mut()
        .chain(program.class_templates.iter_mut())
    {
        for inv in &mut cl.invariants {
            inv.text = subst_clause_text(&inv.text, &text_map);
        }
        for init in &mut cl.inits {
            subst_fn(init, &values, &text_map);
        }
        for m in &mut cl.methods {
            subst_fn(&mut m.f, &values, &text_map);
        }
        if let Some(body) = &mut cl.deinit {
            subst_stmts(body, &values, &text_map);
        }
    }
    for im in &mut program.impls {
        for g in &mut im.ghosts {
            g.text = subst_clause_text(&g.text, &text_map);
        }
        for m in &mut im.fns {
            subst_fn(m, &values, &text_map);
        }
    }
    for g in &mut program.ghosts {
        g.text = subst_clause_text(&g.text, &text_map);
    }
    Ok(())
}

fn subst_fn(f: &mut Fn, values: &HashMap<String, i128>, text_map: &HashMap<String, String>) {
    for c in f
        .pres
        .iter_mut()
        .chain(f.posts.iter_mut())
        .chain(f.requires.iter_mut())
    {
        c.text = subst_clause_text(&c.text, text_map);
    }
    if let Some(v) = &mut f.variant {
        v.text = subst_clause_text(&v.text, text_map);
    }
    subst_stmts(&mut f.body, values, text_map);
}

fn subst_stmts(
    stmts: &mut [Stmt],
    values: &HashMap<String, i128>,
    text_map: &HashMap<String, String>,
) {
    for s in stmts {
        match s {
            Stmt::Decl { init: Some(e), .. }
            | Stmt::Assign { value: e, .. }
            | Stmt::ExprStmt(e)
            | Stmt::VarDecl { init: e, .. }
            | Stmt::FieldAssign { value: e, .. }
            | Stmt::Return { value: Some(e), .. } => subst_expr(e, values),
            Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
            Stmt::Assert(c) => c.text = subst_clause_text(&c.text, text_map),
            Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                subst_expr(index, values);
                subst_expr(value, values);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                subst_expr(cond, values);
                subst_stmts(then_block, values, text_map);
                if let Some(eb) = else_block {
                    subst_stmts(eb, values, text_map);
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                body,
                ..
            } => {
                subst_expr(cond, values);
                for c in invariants.iter_mut() {
                    c.text = subst_clause_text(&c.text, text_map);
                }
                if let Some(v) = variant {
                    v.text = subst_clause_text(&v.text, text_map);
                }
                subst_stmts(body, values, text_map);
            }
        }
    }
}

fn subst_expr(e: &mut Expr, values: &HashMap<String, i128>) {
    match &mut e.kind {
        ExprKind::Var(name) => {
            if let Some(v) = values.get(name.as_str()) {
                e.kind = ExprKind::IntLit(*v);
            }
        }
        ExprKind::ResOp { args, .. } => {
            for a in args {
                subst_expr(a, values);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => subst_expr(operand, values),
        ExprKind::Binary { lhs, rhs, .. } => {
            subst_expr(lhs, values);
            subst_expr(rhs, values);
        }
        ExprKind::Call { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::ArrayLit(args) => {
            for a in args {
                subst_expr(a, values);
            }
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => subst_expr(index, values),
        ExprKind::AllocArray { len, init, .. } => {
            subst_expr(len, values);
            subst_expr(init, values);
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::NoneE
        | ExprKind::Len { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::Borrow { .. } => {}
    }
}

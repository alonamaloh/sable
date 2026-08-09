//! Monomorphization (ADR 0006): between parse and typecheck, every
//! generic declaration is expanded into one ordinary declaration per
//! distinct instantiation reachable from the non-generic roots. No later
//! stage — checker, VCgen, interpreter, LSP — ever sees a type variable.
//!
//! Instances are mangled `Vec_i32`; spans point into the generic source,
//! so diagnostics land on the template with the instance visible in the
//! declaration name. `T` is substituted even inside proof-clause text
//! (bare, not parenthesized, so `T.max` becomes `i32.max`).

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{HashMap, HashSet, VecDeque};

type MResult<T> = Result<T, Diagnostic>;

const DEPTH_CAP: usize = 32;

pub fn monomorphize(program: &mut Program) -> MResult<()> {
    let mut fn_templates: HashMap<String, Fn> = HashMap::new();
    let mut class_templates: HashMap<String, ClassDecl> = HashMap::new();

    let fns = std::mem::take(&mut program.fns);
    for f in fns {
        if f.type_params.is_empty() {
            program.fns.push(f);
        } else {
            fn_templates.insert(f.name.clone(), f);
        }
    }
    let classes = std::mem::take(&mut program.classes);
    for c in classes {
        if c.type_params.is_empty() {
            program.classes.push(c);
        } else {
            class_templates.insert(c.name.clone(), c);
        }
    }

    let mut ctx = Mono {
        fn_templates,
        class_templates,
        instantiated: HashSet::new(),
        queue: VecDeque::new(),
        new_fns: Vec::new(),
        new_classes: Vec::new(),
    };

    // Roots: rewrite use sites in the non-generic declarations.
    for f in &mut program.fns {
        ctx.rewrite_fn_uses(f, 0)?;
    }
    for c in &mut program.classes {
        for init in &mut c.inits {
            ctx.rewrite_fn_uses(init, 0)?;
        }
        for m in &mut c.methods {
            ctx.rewrite_fn_uses(&mut m.f, 0)?;
        }
    }

    // Expand the worklist to a fixed point.
    let mut depth = 0;
    while let Some(req) = ctx.queue.pop_front() {
        depth += 1;
        if depth > 100_000 {
            return Err(Diagnostic {
                name: "mono.runaway".into(),
                title: "monomorphization did not terminate".into(),
                span: req.span,
                label: "instantiation explosion".into(),
                notes: vec![],
            });
        }
        ctx.instantiate(req)?;
    }

    // Deterministic output order.
    ctx.new_fns.sort_by(|a, b| a.name.cmp(&b.name));
    ctx.new_classes.sort_by(|a, b| a.name.cmp(&b.name));
    program.fns.extend(ctx.new_fns);
    program.classes.extend(ctx.new_classes);
    Ok(())
}

#[derive(Clone)]
struct Request {
    is_class: bool,
    template: String,
    args: Vec<IntTy>,
    span: Span,
    depth: usize,
}

struct Mono {
    fn_templates: HashMap<String, Fn>,
    class_templates: HashMap<String, ClassDecl>,
    instantiated: HashSet<String>,
    queue: VecDeque<Request>,
    new_fns: Vec<Fn>,
    new_classes: Vec<ClassDecl>,
}

pub fn mangle(template: &str, args: &[IntTy]) -> String {
    let mut out = template.to_string();
    for a in args {
        out.push('_');
        out.push_str(a.name());
    }
    out
}

impl Mono {
    fn request(
        &mut self,
        is_class: bool,
        template: &str,
        args: &[IntTy],
        span: Span,
        depth: usize,
    ) -> MResult<String> {
        if args.iter().any(|a| matches!(a, IntTy::TParam(_))) {
            unreachable!("unsubstituted parameter in instantiation request");
        }
        let expected = if is_class {
            self.class_templates[template].type_params.len()
        } else {
            self.fn_templates[template].type_params.len()
        };
        if args.len() != expected {
            return Err(Diagnostic {
                name: "mono.arity".into(),
                title: format!(
                    "`{template}` takes {expected} type argument(s), {} given",
                    args.len()
                ),
                span,
                label: "wrong number of type arguments".into(),
                notes: vec![],
            });
        }
        if depth > DEPTH_CAP {
            return Err(Diagnostic {
                name: "mono.depth".into(),
                title: "instantiation nesting too deep".into(),
                span,
                label: format!("more than {DEPTH_CAP} levels of generic instantiation"),
                notes: vec![],
            });
        }
        let mangled = mangle(template, args);
        if self.instantiated.insert(mangled.clone()) {
            self.queue.push_back(Request {
                is_class,
                template: template.to_string(),
                args: args.to_vec(),
                span,
                depth,
            });
        }
        Ok(mangled)
    }

    fn instantiate(&mut self, req: Request) -> MResult<()> {
        if req.is_class {
            let template = self.class_templates[&req.template].clone();
            let mut c = template;
            let param_names = std::mem::take(&mut c.type_params);
            let text_map: HashMap<String, String> = param_names
                .iter()
                .enumerate()
                .map(|(i, p)| (p.clone(), req.args[i].name().to_string()))
                .collect();
            c.name = mangle(&req.template, &req.args);
            for fld in &mut c.fields {
                subst_ty(&mut fld.ty, &req.args);
            }
            for inv in &mut c.invariants {
                inv.text = subst_clause_text(&inv.text, &text_map);
            }
            for init in &mut c.inits {
                self.subst_fn(init, &req.args, &text_map, req.depth)?;
            }
            for m in &mut c.methods {
                self.subst_fn(&mut m.f, &req.args, &text_map, req.depth)?;
            }
            self.new_classes.push(c);
        } else {
            let template = self.fn_templates[&req.template].clone();
            let mut f = template;
            let param_names = std::mem::take(&mut f.type_params);
            let text_map: HashMap<String, String> = param_names
                .iter()
                .enumerate()
                .map(|(i, p)| (p.clone(), req.args[i].name().to_string()))
                .collect();
            f.name = mangle(&req.template, &req.args);
            self.subst_fn(&mut f, &req.args, &text_map, req.depth)?;
            self.new_fns.push(f);
        }
        Ok(())
    }

    /// Substitute type parameters throughout one function, then rewrite
    /// its (now-concrete) use sites, discovering nested instantiations.
    fn subst_fn(
        &mut self,
        f: &mut Fn,
        args: &[IntTy],
        text_map: &HashMap<String, String>,
        depth: usize,
    ) -> MResult<()> {
        for p in &mut f.params {
            subst_ty(&mut p.ty, args);
        }
        subst_ty(&mut f.ret, args);
        for c in f.pres.iter_mut().chain(f.posts.iter_mut()) {
            c.text = subst_clause_text(&c.text, text_map);
        }
        if let Some(v) = &mut f.variant {
            v.text = subst_clause_text(&v.text, text_map);
        }
        subst_stmts(&mut f.body, args, text_map);
        self.rewrite_fn_uses(f, depth + 1)
    }

    /// Rewrite generic use sites (Call/CtorCall with type_args) in a
    /// declaration whose types are already concrete.
    fn rewrite_fn_uses(&mut self, f: &mut Fn, depth: usize) -> MResult<()> {
        let mut stmts = std::mem::take(&mut f.body);
        let r = self.rewrite_stmts(&mut stmts, depth);
        f.body = stmts;
        r
    }

    fn rewrite_stmts(&mut self, stmts: &mut [Stmt], depth: usize) -> MResult<()> {
        for s in stmts {
            match s {
                Stmt::Decl { init: Some(e), .. }
                | Stmt::Assign { value: e, .. }
                | Stmt::ExprStmt(e)
                | Stmt::VarDecl { init: e, .. }
                | Stmt::FieldAssign { value: e, .. }
                | Stmt::Return { value: Some(e), .. } => self.rewrite_expr(e, depth)?,
                Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
                Stmt::Store { index, value, .. }
                | Stmt::FieldStore { index, value, .. } => {
                    self.rewrite_expr(index, depth)?;
                    self.rewrite_expr(value, depth)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.rewrite_expr(cond, depth)?;
                    self.rewrite_stmts(then_block, depth)?;
                    if let Some(eb) = else_block {
                        self.rewrite_stmts(eb, depth)?;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.rewrite_expr(cond, depth)?;
                    self.rewrite_stmts(body, depth)?;
                }
            }
        }
        Ok(())
    }

    fn rewrite_expr(&mut self, e: &mut Expr, depth: usize) -> MResult<()> {
        match &mut e.kind {
            ExprKind::Call {
                callee,
                callee_span,
                type_args,
                args,
            } => {
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
                if self.fn_templates.contains_key(callee.as_str()) {
                    if type_args.is_empty() {
                        return Err(Diagnostic {
                            name: "mono.missing_type_args".into(),
                            title: format!("`{callee}` is generic"),
                            span: *callee_span,
                            label: "instantiation is explicit: write `name<type>(...)` \
                                    (ADR 0006)"
                                .into(),
                            notes: vec![],
                        });
                    }
                    let targs = std::mem::take(type_args);
                    *callee = self.request(false, &callee.clone(), &targs, *callee_span, depth)?;
                } else if !type_args.is_empty() {
                    return Err(Diagnostic {
                        name: "mono.not_generic".into(),
                        title: format!("`{callee}` takes no type arguments"),
                        span: *callee_span,
                        label: "not a generic function".into(),
                        notes: vec![],
                    });
                }
            }
            ExprKind::CtorCall {
                class,
                class_span,
                type_args,
                args,
                ..
            } => {
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
                if self.class_templates.contains_key(class.as_str()) {
                    if type_args.is_empty() {
                        return Err(Diagnostic {
                            name: "mono.missing_type_args".into(),
                            title: format!("`{class}` is generic"),
                            span: *class_span,
                            label: "instantiation is explicit: write `Class<type>::...` \
                                    (ADR 0006)"
                                .into(),
                            notes: vec![],
                        });
                    }
                    let targs = std::mem::take(type_args);
                    *class = self.request(true, &class.clone(), &targs, *class_span, depth)?;
                } else if !type_args.is_empty() {
                    return Err(Diagnostic {
                        name: "mono.not_generic".into(),
                        title: format!("`{class}` takes no type arguments"),
                        span: *class_span,
                        label: "not a generic class".into(),
                        notes: vec![],
                    });
                }
            }
            ExprKind::MethodCall { args, .. } => {
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
            }
            ExprKind::Unary { operand, .. } => self.rewrite_expr(operand, depth)?,
            ExprKind::Widen { arg, .. } => self.rewrite_expr(arg, depth)?,
            ExprKind::SomeE(inner) => self.rewrite_expr(inner, depth)?,
            ExprKind::Binary { lhs, rhs, .. } => {
                self.rewrite_expr(lhs, depth)?;
                self.rewrite_expr(rhs, depth)?;
            }
            ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
                self.rewrite_expr(index, depth)?
            }
            ExprKind::AllocArray { len, init, .. } => {
                self.rewrite_expr(len, depth)?;
                self.rewrite_expr(init, depth)?;
            }
            ExprKind::ArrayLit(elems) => {
                for el in elems.iter_mut() {
                    self.rewrite_expr(el, depth)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn subst_intty(t: &mut IntTy, args: &[IntTy]) {
    if let IntTy::TParam(i) = t {
        *t = args[*i as usize];
    }
}

fn subst_ty(t: &mut Ty, args: &[IntTy]) {
    match t {
        Ty::Int(it) => subst_intty(it, args),
        Ty::Array(it, _) | Ty::Option(it) => subst_intty(it, args),
        _ => {}
    }
}

fn subst_stmts(stmts: &mut [Stmt], args: &[IntTy], text_map: &HashMap<String, String>) {
    for s in stmts {
        match s {
            Stmt::Decl { ty, init, .. } => {
                subst_ty(ty, args);
                if let Some(e) = init {
                    subst_expr(e, args);
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::VarDecl { init: value, .. }
            | Stmt::FieldAssign { value, .. } => subst_expr(value, args),
            Stmt::Return { value: Some(e), .. } => subst_expr(e, args),
            Stmt::Return { value: None, .. } => {}
            Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                subst_expr(index, args);
                subst_expr(value, args);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                subst_expr(cond, args);
                subst_stmts(then_block, args, text_map);
                if let Some(eb) = else_block {
                    subst_stmts(eb, args, text_map);
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                body,
                ..
            } => {
                subst_expr(cond, args);
                for inv in invariants.iter_mut() {
                    inv.text = subst_clause_text(&inv.text, text_map);
                }
                if let Some(v) = variant {
                    v.text = subst_clause_text(&v.text, text_map);
                }
                subst_stmts(body, args, text_map);
            }
        }
    }
}

fn subst_expr(e: &mut Expr, args: &[IntTy]) {
    match &mut e.kind {
        ExprKind::Widen { target, arg } => {
            subst_intty(target, args);
            subst_expr(arg, args);
        }
        ExprKind::AllocArray { elem, len, init } => {
            subst_intty(elem, args);
            subst_expr(len, args);
            subst_expr(init, args);
        }
        ExprKind::Call {
            type_args, args: a, ..
        }
        | ExprKind::CtorCall {
            type_args, args: a, ..
        } => {
            for t in type_args.iter_mut() {
                subst_intty(t, args);
            }
            for x in a.iter_mut() {
                subst_expr(x, args);
            }
        }
        ExprKind::MethodCall { args: a, .. } => {
            for x in a.iter_mut() {
                subst_expr(x, args);
            }
        }
        ExprKind::Unary { operand, .. } => subst_expr(operand, args),
        ExprKind::SomeE(inner) => subst_expr(inner, args),
        ExprKind::Binary { lhs, rhs, .. } => {
            subst_expr(lhs, args);
            subst_expr(rhs, args);
        }
        ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
            subst_expr(index, args)
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems.iter_mut() {
                subst_expr(el, args);
            }
        }
        _ => {}
    }
}

/// Bare (unparenthesized) token substitution in clause text: `T.max`
/// must become `i32.max`, not `(i32).max`.
fn subst_clause_text(text: &str, map: &HashMap<String, String>) -> String {
    let mut out: Vec<u8> = Vec::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut prev: Option<u8> = None;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
            {
                i += 1;
            }
            let word = &text[start..i];
            let after_dot = prev == Some(b'.');
            match map.get(word) {
                Some(r) if !after_dot => out.extend_from_slice(r.as_bytes()),
                _ => out.extend_from_slice(word.as_bytes()),
            }
            prev = Some(bytes[i - 1]);
            continue;
        }
        out.push(b);
        prev = Some(b);
        i += 1;
    }
    String::from_utf8(out).expect("substitution preserves UTF-8")
}

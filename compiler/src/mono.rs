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

    // Traits and impls are consumed here (ADR 0007): each impl's spec
    // ghost defs are hoisted under mangled names, and each impl body
    // becomes a plain top-level fn carrying the trait's contract — then
    // verified like any other function.
    let trait_decls = std::mem::take(&mut program.traits);
    let impl_decls = std::mem::take(&mut program.impls);
    let mut traits: HashMap<String, TraitDecl> = HashMap::new();
    for t in trait_decls {
        traits.insert(t.name.clone(), t);
    }
    let mut impls: HashMap<(String, String), ImplInfo> = HashMap::new();
    for im in impl_decls {
        let Some(tr) = traits.get(&im.trait_name) else {
            return Err(Diagnostic {
                name: "impl.unknown_trait".into(),
                title: format!("no trait named `{}`", im.trait_name),
                span: im.trait_span,
                label: "unknown trait".into(),
                notes: vec![],
            });
        };
        let tyname = im.for_ty.name().to_string();
        let prefix = format!("{}_{}", tr.name, tyname);
        let key = (im.trait_name.clone(), tyname.clone());
        if impls.contains_key(&key) {
            return Err(Diagnostic {
                name: "impl.duplicate".into(),
                title: format!("duplicate `impl {} for {tyname}`", im.trait_name),
                span: im.trait_span,
                label: "already implemented".into(),
                notes: vec![],
            });
        }

        // Spec functions: every trait `spec` needs exactly one ghost def.
        let mut specs: HashMap<String, String> = HashMap::new();
        let mut ghost_by_name: HashMap<String, GhostItem> = HashMap::new();
        for g in &im.ghosts {
            let lead: String = g
                .text
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            ghost_by_name.insert(lead, g.clone());
        }
        for sp in &tr.specs {
            let Some(g) = ghost_by_name.remove(&sp.name) else {
                return Err(Diagnostic {
                    name: "impl.missing_spec".into(),
                    title: format!(
                        "`impl {} for {tyname}` does not define spec `{}`",
                        tr.name, sp.name
                    ),
                    span: im.trait_span,
                    label: format!("add `/// def {} ...` to the impl", sp.name),
                    notes: vec![],
                });
            };
            let mangled = format!("{prefix}_{}_spec", sp.name);
            let text = g.text.trim_start();
            let renamed = format!("{mangled}{}", &text[sp.name.len()..]);
            program.ghosts.push(GhostItem {
                keyword: "def",
                text: renamed,
                span: g.span,
            });
            specs.insert(sp.name.clone(), mangled);
        }
        if let Some(extra) = ghost_by_name.keys().next() {
            return Err(Diagnostic {
                name: "impl.unknown_spec".into(),
                title: format!("`{extra}` is not a spec of trait `{}`", im.trait_name),
                span: im.span,
                label: "impl ghost defs must match the trait's `spec` clauses".into(),
                notes: vec![],
            });
        }

        // Method bodies: exact match against the trait's signatures; the
        // trait's contract is instantiated onto each.
        let mut text_map: HashMap<String, String> = HashMap::new();
        text_map.insert("Self".to_string(), tyname.clone());
        for (spname, mangled) in &specs {
            text_map.insert(format!("Self::{spname}"), mangled.clone());
        }
        let mut impl_fns: HashMap<String, Fn> = HashMap::new();
        for f in im.fns {
            if !f.pres.is_empty() || !f.posts.is_empty() || f.variant.is_some() {
                unreachable!("parser rejects contracts in impl bodies");
            }
            impl_fns.insert(f.name.clone(), f);
        }
        let mut method_names: HashSet<String> = HashSet::new();
        for tm in &tr.methods {
            method_names.insert(tm.name.clone());
            let Some(mut body_fn) = impl_fns.remove(&tm.name) else {
                return Err(Diagnostic {
                    name: "impl.missing_fn".into(),
                    title: format!(
                        "`impl {} for {tyname}` does not implement `{}`",
                        tr.name, tm.name
                    ),
                    span: im.trait_span,
                    label: "missing trait method".into(),
                    notes: vec![],
                });
            };
            // The trait signature, with Self := the concrete type.
            let args = [im.for_ty];
            let mut want_params = tm.params.clone();
            for p in &mut want_params {
                subst_ty(&mut p.ty, &args);
            }
            let mut want_ret = tm.ret;
            subst_ty(&mut want_ret, &args);
            let sig_ok = body_fn.params.len() == want_params.len()
                && body_fn
                    .params
                    .iter()
                    .zip(&want_params)
                    .all(|(a, b)| a.ty == b.ty && a.name == b.name)
                && body_fn.ret == want_ret;
            if !sig_ok {
                return Err(Diagnostic {
                    name: "impl.sig_mismatch".into(),
                    title: format!(
                        "`{}` does not match the signature of `{}::{}`",
                        tm.name, tr.name, tm.name
                    ),
                    span: body_fn.name_span,
                    label: "parameter names, types, and return type must match \
                            the trait (contract clauses refer to them)"
                        .into(),
                    notes: vec![],
                });
            }
            body_fn.name = format!("{prefix}_{}", tm.name);
            body_fn.pres = tm.pres.clone();
            body_fn.posts = tm.posts.clone();
            for c in body_fn.pres.iter_mut().chain(body_fn.posts.iter_mut()) {
                c.text = subst_clause_text(&c.text, &text_map);
            }
            program.fns.push(body_fn);
        }
        if let Some(extra) = impl_fns.keys().next() {
            return Err(Diagnostic {
                name: "impl.extra_fn".into(),
                title: format!("`{extra}` is not a method of trait `{}`", im.trait_name),
                span: im.span,
                label: "impls define exactly the trait's methods".into(),
                notes: vec![],
            });
        }
        impls.insert(
            key,
            ImplInfo {
                prefix,
                methods: method_names,
                specs,
            },
        );
    }

    let fns = std::mem::take(&mut program.fns);
    for f in fns {
        if f.type_params.is_empty() {
            program.fns.push(f);
        } else {
            check_bounds_known(&f.type_bounds, &traits, f.name_span)?;
            // Preserved for template-level verification (ADR 0009):
            // bounded templates get `K::spec` → `K_spec` in clause text
            // and `K::m(...)` calls converted to TraitCall.
            let mut saved = f.clone();
            prepare_template_fn(&mut saved, &traits);
            program.fn_templates.push(saved);
            fn_templates.insert(f.name.clone(), f);
        }
    }
    let classes = std::mem::take(&mut program.classes);
    for c in classes {
        if c.type_params.is_empty() {
            program.classes.push(c);
        } else {
            check_bounds_known(&c.type_bounds, &traits, c.name_span)?;
            let mut saved = c.clone();
            prepare_template_class(&mut saved, &traits);
            program.class_templates.push(saved);
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
        traits,
        impls,
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

    // Traits are retained for template verification (check/vcgen model
    // trait calls against their contracts).
    let mut kept: Vec<TraitDecl> = ctx.traits.into_values().collect();
    kept.sort_by(|a, b| a.name.cmp(&b.name));
    program.traits = kept;

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
    /// Trait name → declaration (ADR 0007).
    traits: HashMap<String, TraitDecl>,
    /// (trait name, concrete type name) → impl info.
    impls: HashMap<(String, String), ImplInfo>,
}

/// What monomorphization needs to resolve `K::m` through an impl.
struct ImplInfo {
    /// `Hashable_i32` — program fns are `{prefix}_{method}`.
    prefix: String,
    methods: HashSet<String>,
    /// spec name → mangled ghost-def name (`Hashable_i32_hash_spec`).
    specs: HashMap<String, String>,
}

/// Template-save preparation (ADR 0009 slice 3): rewrite the qualified
/// spec references in clause text (`K::hash` → the abstract binder
/// `K_hash`) and convert bounded-parameter calls into `TraitCall`.
fn template_qual_map(
    params: &[String],
    bounds: &[Option<String>],
    traits: &HashMap<String, TraitDecl>,
) -> (HashMap<String, String>, HashSet<String>) {
    let mut qual = HashMap::new();
    let mut bound_params = HashSet::new();
    for (i, p) in params.iter().enumerate() {
        if let Some(Some(b)) = bounds.get(i) {
            bound_params.insert(p.clone());
            if let Some(tr) = traits.get(b) {
                for sp in &tr.specs {
                    qual.insert(format!("{p}::{}", sp.name), format!("{p}_{}", sp.name));
                }
            }
        }
    }
    (qual, bound_params)
}

fn prepare_template_fn(f: &mut Fn, traits: &HashMap<String, TraitDecl>) {
    let (qual, bound_params) = template_qual_map(&f.type_params, &f.type_bounds, traits);
    if qual.is_empty() && bound_params.is_empty() {
        return;
    }
    for c in f
        .pres
        .iter_mut()
        .chain(f.posts.iter_mut())
        .chain(f.requires.iter_mut())
    {
        c.text = subst_clause_text(&c.text, &qual);
    }
    if let Some(v) = &mut f.variant {
        v.text = subst_clause_text(&v.text, &qual);
    }
    prepare_stmts(&mut f.body, &qual, &bound_params);
}

fn prepare_template_class(c: &mut ClassDecl, traits: &HashMap<String, TraitDecl>) {
    let (qual, bound_params) = template_qual_map(&c.type_params, &c.type_bounds, traits);
    if qual.is_empty() && bound_params.is_empty() {
        return;
    }
    for inv in &mut c.invariants {
        inv.text = subst_clause_text(&inv.text, &qual);
    }
    for f in c.inits.iter_mut() {
        for cl in f.pres.iter_mut().chain(f.posts.iter_mut()) {
            cl.text = subst_clause_text(&cl.text, &qual);
        }
        prepare_stmts(&mut f.body, &qual, &bound_params);
    }
    for m in c.methods.iter_mut() {
        for cl in m.f.pres.iter_mut().chain(m.f.posts.iter_mut()) {
            cl.text = subst_clause_text(&cl.text, &qual);
        }
        if let Some(v) = &mut m.f.variant {
            v.text = subst_clause_text(&v.text, &qual);
        }
        prepare_stmts(&mut m.f.body, &qual, &bound_params);
    }
}

fn prepare_stmts(
    stmts: &mut [Stmt],
    qual: &HashMap<String, String>,
    bound_params: &HashSet<String>,
) {
    for s in stmts {
        match s {
            Stmt::Decl { init: Some(e), .. }
            | Stmt::Assign { value: e, .. }
            | Stmt::ExprStmt(e)
            | Stmt::VarDecl { init: e, .. }
            | Stmt::FieldAssign { value: e, .. }
            | Stmt::Return { value: Some(e), .. } => prepare_expr(e, bound_params),
            Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
            Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                prepare_expr(index, bound_params);
                prepare_expr(value, bound_params);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                prepare_expr(cond, bound_params);
                prepare_stmts(then_block, qual, bound_params);
                if let Some(eb) = else_block {
                    prepare_stmts(eb, qual, bound_params);
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                body,
                ..
            } => {
                prepare_expr(cond, bound_params);
                for inv in invariants.iter_mut() {
                    inv.text = subst_clause_text(&inv.text, qual);
                }
                if let Some(v) = variant {
                    v.text = subst_clause_text(&v.text, qual);
                }
                prepare_stmts(body, qual, bound_params);
            }
        }
    }
}

fn prepare_expr(e: &mut Expr, bound_params: &HashSet<String>) {
    match &mut e.kind {
        ExprKind::CtorCall {
            class,
            class_span,
            type_args,
            init,
            args,
        } if bound_params.contains(class.as_str()) && type_args.is_empty() => {
            for a in args.iter_mut() {
                prepare_expr(a, bound_params);
            }
            e.kind = ExprKind::TraitCall {
                param: class.clone(),
                param_span: *class_span,
                method: init.clone(),
                args: std::mem::take(args),
            };
        }
        ExprKind::Call { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::ArrayLit(args) => {
            for a in args.iter_mut() {
                prepare_expr(a, bound_params);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand } => prepare_expr(operand, bound_params),
        ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => {
            prepare_expr(arg, bound_params)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            prepare_expr(lhs, bound_params);
            prepare_expr(rhs, bound_params);
        }
        ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
            prepare_expr(index, bound_params)
        }
        ExprKind::AllocArray { len, init, .. } => {
            prepare_expr(len, bound_params);
            prepare_expr(init, bound_params);
        }
        _ => {}
    }
}

fn check_bounds_known(
    bounds: &[Option<String>],
    traits: &HashMap<String, TraitDecl>,
    span: Span,
) -> MResult<()> {
    for b in bounds.iter().flatten() {
        if !traits.contains_key(b) {
            return Err(Diagnostic {
                name: "mono.unknown_trait_bound".into(),
                title: format!("no trait named `{b}`"),
                span,
                label: "unknown trait bound".into(),
                notes: vec![],
            });
        }
    }
    Ok(())
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
        let (expected, bounds) = if is_class {
            let t = &self.class_templates[template];
            (t.type_params.len(), t.type_bounds.clone())
        } else {
            let t = &self.fn_templates[template];
            (t.type_params.len(), t.type_bounds.clone())
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
        for (bound, arg) in bounds.iter().zip(args) {
            if let Some(b) = bound {
                if !self.impls.contains_key(&(b.clone(), arg.name().to_string())) {
                    return Err(Diagnostic {
                        name: "mono.unsatisfied_bound".into(),
                        title: format!("`{}` does not implement `{b}`", arg.name()),
                        span,
                        label: format!(
                            "the bound requires `impl {b} for {}`",
                            arg.name()
                        ),
                        notes: vec![],
                    });
                }
            }
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
            let bounds = std::mem::take(&mut c.type_bounds);
            let (text_map, bound_calls) =
                self.subst_maps(&param_names, &bounds, &req.args);
            c.name = mangle(&req.template, &req.args);
            c.from_template = Some(req.template.clone());
            for fld in &mut c.fields {
                subst_ty(&mut fld.ty, &req.args);
            }
            for inv in &mut c.invariants {
                inv.text = subst_clause_text(&inv.text, &text_map);
            }
            for init in &mut c.inits {
                self.subst_fn(init, &req.args, &text_map, &bound_calls, req.depth)?;
            }
            for m in &mut c.methods {
                self.subst_fn(&mut m.f, &req.args, &text_map, &bound_calls, req.depth)?;
            }
            self.new_classes.push(c);
        } else {
            let template = self.fn_templates[&req.template].clone();
            let mut f = template;
            let param_names = std::mem::take(&mut f.type_params);
            let bounds = std::mem::take(&mut f.type_bounds);
            let (text_map, bound_calls) =
                self.subst_maps(&param_names, &bounds, &req.args);
            f.name = mangle(&req.template, &req.args);
            // Template-verified instances (ADR 0009): skip their own
            // obligations; owe the substituted `requires`.
            f.from_template = Some(req.template.clone());
            for r in f.requires.iter_mut() {
                r.text = subst_clause_text(&r.text, &text_map);
            }
            self.subst_fn(&mut f, &req.args, &text_map, &bound_calls, req.depth)?;
            self.new_fns.push(f);
        }
        Ok(())
    }

    /// The two substitution maps for one instantiation: clause-text
    /// replacements (bare `K` → `i32`, qualified `K::hash` → the impl's
    /// spec-def name) and program-call resolution for bounded params
    /// (`K::hash(x)` → `Hashable_i32_hash(x)`).
    fn subst_maps(
        &self,
        param_names: &[String],
        bounds: &[Option<String>],
        args: &[IntTy],
    ) -> (HashMap<String, String>, HashMap<String, (String, HashSet<String>)>) {
        let mut text_map: HashMap<String, String> = HashMap::new();
        let mut bound_calls: HashMap<String, (String, HashSet<String>)> = HashMap::new();
        for (i, p) in param_names.iter().enumerate() {
            text_map.insert(p.clone(), args[i].name().to_string());
            if let Some(b) = bounds.get(i).and_then(|b| b.as_ref()) {
                let info = &self.impls[&(b.clone(), args[i].name().to_string())];
                for (spname, mangled) in &info.specs {
                    text_map.insert(format!("{p}::{spname}"), mangled.clone());
                }
                bound_calls.insert(p.clone(), (info.prefix.clone(), info.methods.clone()));
            }
        }
        (text_map, bound_calls)
    }

    /// Substitute type parameters throughout one function, then rewrite
    /// its (now-concrete) use sites, discovering nested instantiations.
    fn subst_fn(
        &mut self,
        f: &mut Fn,
        args: &[IntTy],
        text_map: &HashMap<String, String>,
        bound_calls: &HashMap<String, (String, HashSet<String>)>,
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
        subst_stmts(&mut f.body, args, text_map, bound_calls)?;
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
            ExprKind::Unary { operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand } => self.rewrite_expr(operand, depth)?,
            ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => {
                self.rewrite_expr(arg, depth)?
            }
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

type BoundCalls = HashMap<String, (String, HashSet<String>)>;

fn subst_stmts(
    stmts: &mut [Stmt],
    args: &[IntTy],
    text_map: &HashMap<String, String>,
    bound_calls: &BoundCalls,
) -> MResult<()> {
    for s in stmts {
        match s {
            Stmt::Decl { ty, init, .. } => {
                subst_ty(ty, args);
                if let Some(e) = init {
                    subst_expr(e, args, bound_calls)?;
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::VarDecl { init: value, .. }
            | Stmt::FieldAssign { value, .. } => subst_expr(value, args, bound_calls)?,
            Stmt::Return { value: Some(e), .. } => subst_expr(e, args, bound_calls)?,
            Stmt::Return { value: None, .. } => {}
            Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                subst_expr(index, args, bound_calls)?;
                subst_expr(value, args, bound_calls)?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                subst_expr(cond, args, bound_calls)?;
                subst_stmts(then_block, args, text_map, bound_calls)?;
                if let Some(eb) = else_block {
                    subst_stmts(eb, args, text_map, bound_calls)?;
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                body,
                ..
            } => {
                subst_expr(cond, args, bound_calls)?;
                for inv in invariants.iter_mut() {
                    inv.text = subst_clause_text(&inv.text, text_map);
                }
                if let Some(v) = variant {
                    v.text = subst_clause_text(&v.text, text_map);
                }
                subst_stmts(body, args, text_map, bound_calls)?;
            }
        }
    }
    Ok(())
}

fn subst_expr(e: &mut Expr, args: &[IntTy], bound_calls: &BoundCalls) -> MResult<()> {
    match &mut e.kind {
        ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
            subst_intty(target, args);
            subst_expr(arg, args, bound_calls)?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            subst_intty(elem, args);
            subst_expr(len, args, bound_calls)?;
            subst_expr(init, args, bound_calls)?;
        }
        ExprKind::CtorCall {
            class,
            class_span,
            type_args,
            init,
            args: a,
        } if bound_calls.contains_key(class.as_str()) => {
            // `K::hash(x)` — a trait-method call through a bounded
            // parameter; resolves to the impl's plain fn (ADR 0007).
            let (prefix, methods) = &bound_calls[class.as_str()];
            if !type_args.is_empty() {
                return Err(Diagnostic {
                    name: "mono.not_generic".into(),
                    title: format!("`{class}::{init}` takes no type arguments"),
                    span: *class_span,
                    label: "trait methods are not generic".into(),
                    notes: vec![],
                });
            }
            if !methods.contains(init.as_str()) {
                return Err(Diagnostic {
                    name: "mono.no_trait_method".into(),
                    title: format!("the bound on `{class}` provides no method `{init}`"),
                    span: *class_span,
                    label: "not a method of the bounding trait".into(),
                    notes: vec![],
                });
            }
            for x in a.iter_mut() {
                subst_expr(x, args, bound_calls)?;
            }
            e.kind = ExprKind::Call {
                callee: format!("{prefix}_{init}"),
                callee_span: *class_span,
                type_args: Vec::new(),
                args: std::mem::take(a),
            };
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
                subst_expr(x, args, bound_calls)?;
            }
        }
        ExprKind::MethodCall { args: a, .. } => {
            for x in a.iter_mut() {
                subst_expr(x, args, bound_calls)?;
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand } => subst_expr(operand, args, bound_calls)?,
        ExprKind::SomeE(inner) => subst_expr(inner, args, bound_calls)?,
        ExprKind::Binary { lhs, rhs, .. } => {
            subst_expr(lhs, args, bound_calls)?;
            subst_expr(rhs, args, bound_calls)?;
        }
        ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
            subst_expr(index, args, bound_calls)?
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems.iter_mut() {
                subst_expr(el, args, bound_calls)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Bare (unparenthesized) token substitution in clause text: `T.max`
/// must become `i32.max`, not `(i32).max`.
pub(crate) fn subst_clause_text(text: &str, map: &HashMap<String, String>) -> String {
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
            // Qualified `K::hash` first — it must win over bare `K`.
            if !after_dot && i + 2 <= bytes.len() && &bytes[i..i + 2] == b"::" {
                let qstart = i + 2;
                let mut j = qstart;
                while j < bytes.len()
                    && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_')
                {
                    j += 1;
                }
                if j > qstart {
                    let qualified = format!("{word}::{}", &text[qstart..j]);
                    if let Some(r) = map.get(&qualified) {
                        out.extend_from_slice(r.as_bytes());
                        prev = Some(bytes[j - 1]);
                        i = j;
                        continue;
                    }
                }
            }
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

//! Monomorphization (ADR 0006): between parse and typecheck, every
//! generic declaration is expanded into one ordinary declaration per
//! distinct instantiation reachable from the non-generic roots. Ordinary
//! declarations are fully concrete afterward; retained ADR 0009 templates
//! deliberately keep explicit type parameters for checker/VCgen modeling.
//!
//! Instances are mangled `Vec_i32`; spans point into the generic source,
//! so diagnostics land on the template with the instance visible in the
//! declaration name. `T` is substituted even inside proof-clause text
//! (bare, not parenthesized, so `T.max` becomes `i32.max`).

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

type MResult<T> = Result<T, Diagnostic>;

const DEPTH_CAP: usize = 32;

pub fn monomorphize(program: &mut Program) -> MResult<()> {
    preflight_source_names(program)?;
    reject_input_proof_reuse(program)?;
    validate_declaration_type_params(program)?;
    validate_v1_type_args(program)?;
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
        if traits.contains_key(&t.name) {
            return Err(Diagnostic {
                name: "trait.duplicate".into(),
                title: format!("trait `{}` is defined twice", t.name),
                span: t.name_span,
                label: "second definition here".into(),
                notes: vec![],
            });
        }
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
        let mut ghost_decls: Vec<&GhostItem> = im.ghosts.iter().collect();
        ghost_decls.sort_by_key(|ghost| (ghost.span.start, ghost.span.end));
        for g in ghost_decls {
            let lead: String = g
                .text
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if ghost_by_name.contains_key(&lead) {
                return Err(Diagnostic {
                    name: "impl.duplicate_spec".into(),
                    title: format!(
                        "`impl {} for {tyname}` defines spec `{lead}` twice",
                        im.trait_name
                    ),
                    span: g.span,
                    label: "second definition here".into(),
                    notes: vec![],
                });
            }
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
                unfold: false,
                text: renamed,
                span: g.span,
            });
            specs.insert(sp.name.clone(), mangled);
        }
        if let Some((extra, ghost)) =
            ghost_by_name
                .iter()
                .min_by(|(name_a, ghost_a), (name_b, ghost_b)| {
                    ghost_a
                        .span
                        .start
                        .cmp(&ghost_b.span.start)
                        .then_with(|| ghost_a.span.end.cmp(&ghost_b.span.end))
                        .then_with(|| name_a.cmp(name_b))
                })
        {
            return Err(Diagnostic {
                name: "impl.unknown_spec".into(),
                title: format!("`{extra}` is not a spec of trait `{}`", im.trait_name),
                span: ghost.span,
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
        let mut method_decls = im.fns;
        method_decls.sort_by_key(|method| (method.name_span.start, method.name_span.end));
        for f in method_decls {
            if !f.pres.is_empty() || !f.posts.is_empty() || f.variant.is_some() {
                unreachable!("parser rejects contracts in impl bodies");
            }
            if impl_fns.contains_key(&f.name) {
                return Err(Diagnostic {
                    name: "impl.duplicate_fn".into(),
                    title: format!(
                        "`impl {} for {tyname}` defines method `{}` twice",
                        im.trait_name, f.name
                    ),
                    span: f.name_span,
                    label: "second definition here".into(),
                    notes: vec![],
                });
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
        if let Some((extra, method)) =
            impl_fns
                .iter()
                .min_by(|(name_a, method_a), (name_b, method_b)| {
                    method_a
                        .name_span
                        .start
                        .cmp(&method_b.name_span.start)
                        .then_with(|| method_a.name_span.end.cmp(&method_b.name_span.end))
                        .then_with(|| name_a.cmp(name_b))
                })
        {
            return Err(Diagnostic {
                name: "impl.extra_fn".into(),
                title: format!("`{extra}` is not a method of trait `{}`", im.trait_name),
                span: method.name_span,
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

    let emitted_names = seed_emitted_names(program)?;
    let mut ctx = Mono {
        fn_templates,
        class_templates,
        instances: HashMap::new(),
        emitted_names,
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
        if let Some(deinit) = &mut c.deinit {
            ctx.rewrite_stmts(deinit, 0)?;
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
    validate_concrete_output(program)
}

/// Monomorphization removes generic declarations before the checker sees the
/// program, so it must reject source-name conflicts first. Mirror the
/// checker's shared-namespace ordering: functions, then records, then classes.
/// This also covers already-retained templates, which can occur in synthetic
/// `Program` values and must not be allowed to overwrite a newly extracted
/// template in the lookup maps below.
fn preflight_source_names(program: &Program) -> MResult<()> {
    let mut function_names = HashSet::new();
    for function in program.fns.iter().chain(&program.fn_templates) {
        if !function_names.insert(function.name.clone()) {
            return Err(Diagnostic {
                name: "type.duplicate_function".into(),
                title: format!("function `{}` is defined twice", function.name),
                span: function.name_span,
                label: "second definition here".into(),
                notes: vec![],
            });
        }
    }

    let mut shared_names = function_names;
    for record in &program.records {
        if !shared_names.insert(record.name.clone()) {
            return Err(Diagnostic {
                name: "record.duplicate".into(),
                title: format!("`{}` is defined twice", record.name),
                span: record.name_span,
                label: "functions, classes, and records share one namespace".into(),
                notes: vec![],
            });
        }
    }
    for class in program.classes.iter().chain(&program.class_templates) {
        if !shared_names.insert(class.name.clone()) {
            return Err(Diagnostic {
                name: "type.duplicate_class".into(),
                title: format!("`{}` is defined twice", class.name),
                span: class.name_span,
                label: "class/function names share one namespace".into(),
                notes: vec![],
            });
        }
    }
    Ok(())
}

/// `ProofReuse` is an authorization produced by this pass, not source or
/// caller metadata. Reject a pre-populated marker before any declaration is
/// moved or rewritten so synthetic `Program` callers cannot suppress VCs.
fn reject_input_proof_reuse(program: &Program) -> MResult<()> {
    fn function(function: &Fn) -> MResult<()> {
        if !function.proof_reuse.is_none() {
            return Err(Diagnostic {
                name: "mono.forged_proof_reuse".into(),
                title: "proof reuse was supplied before monomorphization".into(),
                span: function.name_span,
                label: "only monomorphization may authorize ADR 0009 proof reuse".into(),
                notes: vec![],
            });
        }
        Ok(())
    }

    fn class(class: &ClassDecl) -> MResult<()> {
        if !class.proof_reuse.is_none() {
            return Err(Diagnostic {
                name: "mono.forged_proof_reuse".into(),
                title: "proof reuse was supplied before monomorphization".into(),
                span: class.name_span,
                label: "only monomorphization may authorize ADR 0009 proof reuse".into(),
                notes: vec![],
            });
        }
        for initializer in &class.inits {
            function(initializer)?;
        }
        for method in &class.methods {
            function(&method.f)?;
        }
        Ok(())
    }

    for function_ in program.fns.iter().chain(&program.fn_templates) {
        function(function_)?;
    }
    for class_ in program.classes.iter().chain(&program.class_templates) {
        class(class_)?;
    }
    for trait_ in &program.traits {
        for method in &trait_.methods {
            function(method)?;
        }
    }
    for impl_ in &program.impls {
        for function_ in &impl_.fns {
            function(function_)?;
        }
    }
    Ok(())
}

/// Validate declaration-position parameter identities before substitution.
/// The substitution helpers deliberately use direct indexing once this
/// invariant is established, so malformed synthetic ASTs must fail here
/// rather than panic partway through monomorphization.
fn validate_declaration_type_params(program: &Program) -> MResult<()> {
    fn validate_parameter(
        parameter: TypeParamId,
        arity: usize,
        span: Span,
        representation: &str,
    ) -> MResult<()> {
        if parameter.index() >= arity {
            return Err(Diagnostic {
                name: "mono.type_param_out_of_bounds".into(),
                title: "type parameter is outside its declaration".into(),
                span,
                label: format!(
                    "{representation} refers to type parameter #{}, but this declaration has {arity}",
                    parameter.index()
                ),
                notes: vec![],
            });
        }
        Ok(())
    }

    fn legacy_integer(
        integer: IntTy,
        arity: usize,
        span: Span,
        representation: &str,
        canonical_here: bool,
    ) -> MResult<()> {
        let IntTy::TParam(index) = integer else {
            return Ok(());
        };
        let parameter = TypeParamId::from_legacy(index);
        validate_parameter(parameter, arity, span, representation)?;
        if !canonical_here {
            return Err(Diagnostic {
                name: "mono.noncanonical_type_param".into(),
                title: "legacy integer parameter representation is not canonical here".into(),
                span,
                label: format!(
                    "{representation} must use the explicit declaration type-parameter form"
                ),
                notes: vec![],
            });
        }
        Ok(())
    }

    fn value(ty: ValueTy, arity: usize, span: Span, representation: &str) -> MResult<()> {
        match ty {
            ValueTy::Param(parameter_) => {
                validate_parameter(parameter_, arity, span, representation)
            }
            ValueTy::Int(integer) => legacy_integer(integer, arity, span, representation, false),
            ValueTy::Bool | ValueTy::Record(_) => Ok(()),
        }
    }

    fn affine_option(ty: AffineOptionTy, arity: usize, span: Span) -> MResult<()> {
        match ty {
            AffineOptionTy::Array(element) => {
                value(element, arity, span, "affine-option array element type")
            }
        }
    }

    fn checked_ty(ty: Ty, arity: usize, span: Span) -> MResult<()> {
        match ty {
            Ty::Param(parameter_) => validate_parameter(parameter_, arity, span, "type"),
            Ty::Int(integer) => legacy_integer(integer, arity, span, "value type", false),
            Ty::Array(element, _) => value(element, arity, span, "array element type"),
            Ty::Option(element) => value(element, arity, span, "option payload type"),
            Ty::AffineOption(payload) => affine_option(payload, arity, span),
            // Raw pointer element types and conversion targets still use the
            // legacy IntTy-shaped syntax in G1.0, so a bounded TParam is the
            // canonical representation in those positions.
            Ty::Raw(integer) => {
                legacy_integer(integer, arity, span, "raw-pointer element type", true)
            }
            Ty::Bool
            | Ty::Class(_)
            | Ty::ClassRef(..)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::RawRecord(_)
            | Ty::ResRef(..)
            | Ty::Unit => Ok(()),
        }
    }

    fn expression(expr: &Expr, arity: usize) -> MResult<()> {
        if let Some(ty) = expr.ty {
            checked_ty(ty, arity, expr.span)?;
        }
        match &expr.kind {
            ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
                legacy_integer(*target, arity, expr.span, "integer conversion target", true)?;
                expression(arg, arity)
            }
            ExprKind::AllocArray { elem, len, init } => {
                value(*elem, arity, expr.span, "array allocation element type")?;
                expression(len, arity)?;
                expression(init, arity)
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand }
            | ExprKind::SomeE(operand) => expression(operand, arity),
            ExprKind::Binary { lhs, rhs, .. } => {
                expression(lhs, arity)?;
                expression(rhs, arity)
            }
            ExprKind::Call { args, .. }
            | ExprKind::CtorCall { args, .. }
            | ExprKind::MethodCall { args, .. }
            | ExprKind::TraitCall { args, .. }
            | ExprKind::RawOp { args, .. }
            | ExprKind::ResOp { args, .. }
            | ExprKind::DeviceOp { args, .. }
            | ExprKind::ArrayLit(args)
            | ExprKind::RecordLit { args, .. } => {
                for argument in args {
                    expression(argument, arity)?;
                }
                Ok(())
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => expression(index, arity),
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => Ok(()),
        }
    }

    fn statements(stmts: &[Stmt], arity: usize) -> MResult<()> {
        for statement in stmts {
            match statement {
                Stmt::Decl {
                    ty,
                    name_span,
                    init,
                    ..
                } => {
                    checked_ty(*ty, arity, *name_span)?;
                    if let Some(initializer) = init {
                        expression(initializer, arity)?;
                    }
                }
                Stmt::VarDecl {
                    name_span,
                    init,
                    ty,
                    ..
                } => {
                    if let Some(ty) = ty {
                        checked_ty(*ty, arity, *name_span)?;
                    }
                    expression(init, arity)?;
                }
                Stmt::Assign { value, .. }
                | Stmt::ExprStmt(value)
                | Stmt::FieldAssign { value, .. }
                | Stmt::StaticAlloc { size: value, .. }
                | Stmt::SystemAlloc { size: value, .. }
                | Stmt::Return {
                    value: Some(value), ..
                } => expression(value, arity)?,
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    expression(ptr, arity)?;
                    expression(res, arity)?;
                    expression(release, arity)?;
                }
                Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                    expression(index, arity)?;
                    expression(value, arity)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    expression(cond, arity)?;
                    statements(then_block, arity)?;
                    if let Some(else_block) = else_block {
                        statements(else_block, arity)?;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    expression(cond, arity)?;
                    statements(body, arity)?;
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => statements(body, arity)?,
                Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
            }
        }
        Ok(())
    }

    fn function(function: &Fn, arity: usize) -> MResult<()> {
        for parameter_ in &function.params {
            checked_ty(parameter_.ty, arity, parameter_.span)?;
        }
        checked_ty(function.ret, arity, function.name_span)?;
        statements(&function.body, arity)
    }

    fn class(class: &ClassDecl) -> MResult<()> {
        let arity = class.type_params.len();
        for field in &class.fields {
            checked_ty(field.ty, arity, field.span)?;
        }
        for initializer in &class.inits {
            function(initializer, arity)?;
        }
        for method in &class.methods {
            function(&method.f, arity)?;
        }
        if let Some(deinitializer) = &class.deinit {
            statements(deinitializer, arity)?;
        }
        Ok(())
    }

    for function_ in &program.fns {
        function(function_, function_.type_params.len())?;
    }
    for function_ in &program.fn_templates {
        function(function_, function_.type_params.len())?;
    }
    for class_ in &program.classes {
        class(class_)?;
    }
    for record in &program.records {
        for field in &record.fields {
            checked_ty(field.ty, 0, field.span)?;
        }
    }
    for constant in &program.consts {
        legacy_integer(constant.ty, 0, constant.span, "constant type", true)?;
    }
    for class_ in &program.class_templates {
        class(class_)?;
    }
    for trait_ in &program.traits {
        for method in &trait_.methods {
            function(method, 1)?;
        }
    }
    for implementation in &program.impls {
        legacy_integer(
            implementation.for_ty,
            0,
            implementation.for_span,
            "impl target type",
            true,
        )?;
        for function_ in &implementation.fns {
            function(function_, 0)?;
        }
    }
    Ok(())
}

/// G0 stores recursive use-site types before current monomorphization can
/// implement them. Validate the whole input before mutating it so even a
/// dormant or unreachable template fails closed with the type argument's own
/// span. Parameters remain valid here; concrete-use checks happen when a
/// request is made.
fn validate_v1_type_args(program: &Program) -> MResult<()> {
    fn validate_args(args: &[TypeArg], arity: usize) -> MResult<()> {
        for arg in args {
            let ty = arg
                .ty
                .try_to_v1_int()
                .map_err(|error| unsupported_type_arg(arg.span, error))?;
            if let IntTy::TParam(index) = ty {
                let parameter = TypeParamId::from_legacy(index);
                if parameter.index() >= arity {
                    return Err(unsupported_type_arg(
                        arg.span,
                        GenericTyError::TypeParameterOutOfBounds { parameter, arity },
                    ));
                }
            }
        }
        Ok(())
    }

    fn expression(expr: &Expr, arity: usize) -> MResult<()> {
        match &expr.kind {
            ExprKind::Call {
                type_args, args, ..
            }
            | ExprKind::CtorCall {
                type_args, args, ..
            } => {
                validate_args(type_args, arity)?;
                for arg in args {
                    expression(arg, arity)?;
                }
            }
            ExprKind::MethodCall { args, .. }
            | ExprKind::TraitCall { args, .. }
            | ExprKind::RawOp { args, .. }
            | ExprKind::ResOp { args, .. }
            | ExprKind::DeviceOp { args, .. }
            | ExprKind::ArrayLit(args)
            | ExprKind::RecordLit { args, .. } => {
                for arg in args {
                    expression(arg, arity)?;
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand }
            | ExprKind::SomeE(operand)
            | ExprKind::Widen { arg: operand, .. }
            | ExprKind::Narrow { arg: operand, .. } => expression(operand, arity)?,
            ExprKind::Binary { lhs, rhs, .. } => {
                expression(lhs, arity)?;
                expression(rhs, arity)?;
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => expression(index, arity)?,
            ExprKind::AllocArray { len, init, .. } => {
                expression(len, arity)?;
                expression(init, arity)?;
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => {}
        }
        Ok(())
    }

    fn statements(stmts: &[Stmt], arity: usize) -> MResult<()> {
        for statement in stmts {
            match statement {
                Stmt::Decl {
                    init: Some(value), ..
                }
                | Stmt::Assign { value, .. }
                | Stmt::ExprStmt(value)
                | Stmt::VarDecl { init: value, .. }
                | Stmt::FieldAssign { value, .. }
                | Stmt::StaticAlloc { size: value, .. }
                | Stmt::SystemAlloc { size: value, .. }
                | Stmt::Return {
                    value: Some(value), ..
                } => expression(value, arity)?,
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    expression(ptr, arity)?;
                    expression(res, arity)?;
                    expression(release, arity)?;
                }
                Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                    expression(index, arity)?;
                    expression(value, arity)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    expression(cond, arity)?;
                    statements(then_block, arity)?;
                    if let Some(else_block) = else_block {
                        statements(else_block, arity)?;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    expression(cond, arity)?;
                    statements(body, arity)?;
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => statements(body, arity)?,
                Stmt::Decl { init: None, .. }
                | Stmt::Return { value: None, .. }
                | Stmt::Assert(_) => {}
            }
        }
        Ok(())
    }

    fn function(function: &Fn, arity: usize) -> MResult<()> {
        statements(&function.body, arity)
    }

    fn class(class: &ClassDecl) -> MResult<()> {
        let arity = class.type_params.len();
        for init in &class.inits {
            function(init, arity)?;
        }
        for method in &class.methods {
            function(&method.f, arity)?;
        }
        if let Some(deinit) = &class.deinit {
            statements(deinit, arity)?;
        }
        Ok(())
    }

    for function_ in program.fns.iter().chain(&program.fn_templates) {
        function(function_, function_.type_params.len())?;
    }
    for class_ in program.classes.iter().chain(&program.class_templates) {
        class(class_)?;
    }
    for trait_ in &program.traits {
        for method in &trait_.methods {
            function(method, 1)?;
        }
    }
    for impl_ in &program.impls {
        for function_ in &impl_.fns {
            function(function_, 0)?;
        }
    }
    Ok(())
}

/// Enforce mono's public postcondition for ordinary declarations. Retained
/// templates and traits intentionally keep parameters for ADR 0009 template
/// verification; everything that proceeds through the ordinary checker,
/// VCgen, interpreter, or backend must be concrete.
fn validate_concrete_output(program: &Program) -> MResult<()> {
    fn escaped(span: Span, parameter: TypeParamId, representation: &str) -> Diagnostic {
        Diagnostic {
            name: "mono.unsubstituted_type_param".into(),
            title: "a type parameter escaped monomorphization".into(),
            span,
            label: format!(
                "type parameter #{} remains in an ordinary {representation}",
                parameter.index()
            ),
            notes: vec![(
                "note".into(),
                "only retained generic templates may contain type parameters".into(),
            )],
        }
    }

    fn integer(ty: IntTy, span: Span, representation: &str) -> MResult<()> {
        if let IntTy::TParam(index) = ty {
            return Err(escaped(
                span,
                TypeParamId::from_legacy(index),
                representation,
            ));
        }
        Ok(())
    }

    fn value(ty: ValueTy, span: Span, representation: &str) -> MResult<()> {
        match ty {
            ValueTy::Param(parameter) => Err(escaped(span, parameter, representation)),
            ValueTy::Int(integer_ty) => integer(integer_ty, span, representation),
            ValueTy::Bool | ValueTy::Record(_) => Ok(()),
        }
    }

    fn affine_option(ty: AffineOptionTy, span: Span) -> MResult<()> {
        match ty {
            AffineOptionTy::Array(element) => {
                value(element, span, "affine-option array element type")
            }
        }
    }

    fn checked_ty(ty: Ty, span: Span) -> MResult<()> {
        match ty {
            Ty::Param(parameter) => Err(escaped(span, parameter, "type")),
            Ty::Int(integer_ty) => integer(integer_ty, span, "integer type"),
            Ty::Array(element, _) => value(element, span, "array element type"),
            Ty::Option(element) => value(element, span, "option payload type"),
            Ty::AffineOption(payload) => affine_option(payload, span),
            Ty::Raw(integer_ty) => integer(integer_ty, span, "raw-pointer element type"),
            Ty::Bool
            | Ty::Class(_)
            | Ty::ClassRef(..)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::RawRecord(_)
            | Ty::ResRef(..)
            | Ty::Unit => Ok(()),
        }
    }

    fn expression(expr: &Expr) -> MResult<()> {
        if let Some(ty) = expr.ty {
            checked_ty(ty, expr.span)?;
        }
        match &expr.kind {
            ExprKind::Unary { operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand }
            | ExprKind::SomeE(operand) => expression(operand),
            ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
                integer(*target, expr.span, "integer conversion target")?;
                expression(arg)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                expression(lhs)?;
                expression(rhs)
            }
            ExprKind::Call {
                type_args, args, ..
            }
            | ExprKind::CtorCall {
                type_args, args, ..
            } => {
                if let Some(argument) = type_args.first() {
                    return Err(Diagnostic {
                        name: "mono.unsubstituted_type_arg".into(),
                        title: "a generic type argument escaped monomorphization".into(),
                        span: argument.span,
                        label: "ordinary calls and constructors must name concrete emitted declarations"
                            .into(),
                        notes: vec![],
                    });
                }
                for argument in args {
                    expression(argument)?;
                }
                Ok(())
            }
            ExprKind::MethodCall { args, .. }
            | ExprKind::TraitCall { args, .. }
            | ExprKind::RawOp { args, .. }
            | ExprKind::ResOp { args, .. }
            | ExprKind::DeviceOp { args, .. }
            | ExprKind::ArrayLit(args)
            | ExprKind::RecordLit { args, .. } => {
                for argument in args {
                    expression(argument)?;
                }
                Ok(())
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => expression(index),
            ExprKind::AllocArray { elem, len, init } => {
                value(*elem, expr.span, "array allocation element type")?;
                expression(len)?;
                expression(init)
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => Ok(()),
        }
    }

    fn statements(stmts: &[Stmt]) -> MResult<()> {
        for statement in stmts {
            match statement {
                Stmt::Decl {
                    ty,
                    name_span,
                    init,
                    ..
                } => {
                    checked_ty(*ty, *name_span)?;
                    if let Some(initializer) = init {
                        expression(initializer)?;
                    }
                }
                Stmt::VarDecl {
                    name_span,
                    init,
                    ty,
                    ..
                } => {
                    if let Some(ty) = ty {
                        checked_ty(*ty, *name_span)?;
                    }
                    expression(init)?;
                }
                Stmt::Assign { value, .. }
                | Stmt::ExprStmt(value)
                | Stmt::FieldAssign { value, .. }
                | Stmt::StaticAlloc { size: value, .. }
                | Stmt::SystemAlloc { size: value, .. }
                | Stmt::Return {
                    value: Some(value), ..
                } => expression(value)?,
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    expression(ptr)?;
                    expression(res)?;
                    expression(release)?;
                }
                Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
                    expression(index)?;
                    expression(value)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    expression(cond)?;
                    statements(then_block)?;
                    if let Some(else_block) = else_block {
                        statements(else_block)?;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    expression(cond)?;
                    statements(body)?;
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => statements(body)?,
                Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
            }
        }
        Ok(())
    }

    fn function(function: &Fn) -> MResult<()> {
        for parameter in &function.params {
            checked_ty(parameter.ty, parameter.span)?;
        }
        checked_ty(function.ret, function.name_span)?;
        statements(&function.body)
    }

    fn class(class: &ClassDecl) -> MResult<()> {
        for field in &class.fields {
            checked_ty(field.ty, field.span)?;
        }
        for initializer in &class.inits {
            function(initializer)?;
        }
        for method in &class.methods {
            function(&method.f)?;
        }
        if let Some(deinitializer) = &class.deinit {
            statements(deinitializer)?;
        }
        Ok(())
    }

    for function_ in &program.fns {
        function(function_)?;
    }
    for class_ in &program.classes {
        class(class_)?;
    }
    for record in &program.records {
        for field in &record.fields {
            checked_ty(field.ty, field.span)?;
        }
    }
    for constant in &program.consts {
        integer(constant.ty, constant.span, "constant type")?;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TemplateKind {
    Function,
    Class,
}

impl TemplateKind {
    fn description(self) -> &'static str {
        match self {
            TemplateKind::Function => "function",
            TemplateKind::Class => "class",
        }
    }
}

/// Exact identity of an instance. The legacy emitted spelling is deliberately
/// absent: two structural identities may still render to the same v1 name,
/// which is a diagnosed collision rather than accidental deduplication.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    kind: TemplateKind,
    template: String,
    args: Box<[CanonicalTypeKey]>,
}

impl InstanceKey {
    fn from_args(kind: TemplateKind, template: &str, args: &ConcreteV1Args) -> InstanceKey {
        InstanceKey {
            kind,
            template: template.to_string(),
            args: args.keys.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum SourceNameKind {
    Function,
    FunctionTemplate,
    Class,
    ClassTemplate,
    Record,
}

impl SourceNameKind {
    fn description(self) -> &'static str {
        match self {
            SourceNameKind::Function => "source function",
            SourceNameKind::FunctionTemplate => "generic function template",
            SourceNameKind::Class => "source class",
            SourceNameKind::ClassTemplate => "generic class template",
            SourceNameKind::Record => "source record",
        }
    }
}

#[derive(Debug, Clone)]
enum EmittedNameOwner {
    Source(SourceNameKind),
    Instance(InstanceKey),
}

fn seed_emitted_names(program: &Program) -> MResult<BTreeMap<String, EmittedNameOwner>> {
    let mut names = BTreeMap::new();
    let mut reserve = |name: &str, span: Span, kind: SourceNameKind| -> MResult<()> {
        if let Some(existing) = names.get(name) {
            let EmittedNameOwner::Source(existing) = existing else {
                unreachable!("seeding happens before any instances")
            };
            return Err(Diagnostic {
                name: "mono.source_name_collision".into(),
                title: format!("`{name}` has conflicting source declarations"),
                span,
                label: format!(
                    "this {} collides with an earlier {}",
                    kind.description(),
                    existing.description()
                ),
                notes: vec![(
                    "note".into(),
                    "impl lowering can introduce functions before instance names are reserved; \
                     every retained runtime and template name must still be unique"
                        .into(),
                )],
            });
        }
        names.insert(name.to_string(), EmittedNameOwner::Source(kind));
        Ok(())
    };
    for function in &program.fns {
        reserve(&function.name, function.name_span, SourceNameKind::Function)?;
    }
    for function in &program.fn_templates {
        reserve(
            &function.name,
            function.name_span,
            SourceNameKind::FunctionTemplate,
        )?;
    }
    for class in &program.classes {
        reserve(&class.name, class.name_span, SourceNameKind::Class)?;
    }
    for class in &program.class_templates {
        reserve(&class.name, class.name_span, SourceNameKind::ClassTemplate)?;
    }
    for record in &program.records {
        reserve(&record.name, record.name_span, SourceNameKind::Record)?;
    }
    Ok(names)
}

#[derive(Clone)]
struct Request {
    key: InstanceKey,
    emitted_name: String,
    args: Vec<IntTy>,
    span: Span,
    depth: usize,
}

struct Mono {
    fn_templates: HashMap<String, Fn>,
    class_templates: HashMap<String, ClassDecl>,
    instances: HashMap<InstanceKey, String>,
    emitted_names: BTreeMap<String, EmittedNameOwner>,
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

/// Template-save preparation (ADR 0009): rewrite the qualified
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
        for cl in f
            .pres
            .iter_mut()
            .chain(f.posts.iter_mut())
            .chain(f.requires.iter_mut())
        {
            cl.text = subst_clause_text(&cl.text, &qual);
        }
        if let Some(v) = &mut f.variant {
            v.text = subst_clause_text(&v.text, &qual);
        }
        prepare_stmts(&mut f.body, &qual, &bound_params);
    }
    for m in c.methods.iter_mut() {
        for cl in
            m.f.pres
                .iter_mut()
                .chain(m.f.posts.iter_mut())
                .chain(m.f.requires.iter_mut())
        {
            cl.text = subst_clause_text(&cl.text, &qual);
        }
        if let Some(v) = &mut m.f.variant {
            v.text = subst_clause_text(&v.text, &qual);
        }
        prepare_stmts(&mut m.f.body, &qual, &bound_params);
    }
    if let Some(deinit) = &mut c.deinit {
        prepare_stmts(deinit, &qual, &bound_params);
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
            | Stmt::StaticAlloc { size: e, .. }
            | Stmt::SystemAlloc { size: e, .. }
            | Stmt::Return { value: Some(e), .. } => prepare_expr(e, bound_params),
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                prepare_expr(ptr, bound_params);
                prepare_expr(res, bound_params);
                prepare_expr(release, bound_params);
            }
            Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                prepare_stmts(body, qual, bound_params)
            }
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
            Stmt::Assert(c) => {
                c.text = subst_clause_text(&c.text, qual);
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
        | ExprKind::RawOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ArrayLit(args)
        | ExprKind::RecordLit { args, .. } => {
            for a in args.iter_mut() {
                prepare_expr(a, bound_params);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => prepare_expr(operand, bound_params),
        ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => {
            prepare_expr(arg, bound_params)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            prepare_expr(lhs, bound_params);
            prepare_expr(rhs, bound_params);
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => prepare_expr(index, bound_params),
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

fn unsupported_type_arg(span: Span, error: GenericTyError) -> Diagnostic {
    let reason = match error {
        GenericTyError::NotV1Integer => {
            "this recursive type shape is outside the current integer-only generic domain"
        }
        GenericTyError::UnsubstitutedTypeParameter(_) => {
            "an unsubstituted type parameter reached a concrete instantiation"
        }
        GenericTyError::TypeParameterOutOfBounds { .. } => {
            "the type parameter is outside this declaration's argument list"
        }
        GenericTyError::NonCanonicalLegacyParameter(_) => {
            "a legacy embedded type parameter was not normalized"
        }
    };
    Diagnostic {
        name: "mono.type_arg_unsupported".into(),
        title: "this generic type argument is not supported yet".into(),
        span,
        label: "G0 instantiation still accepts only `u8`..`u64` and `i8`..`i64`".into(),
        notes: vec![(
            "note".into(),
            format!(
                "{reason}; the recursive representation is present so later slices can enable \
                 Boolean, aggregate, and nominal arguments without changing instance identity"
            ),
        )],
    }
}

/// The current substitution payload plus the future-proof structural keys
/// taken directly from the recursive source types. Keeping both here prevents
/// instance identity from being accidentally reconstructed from the temporary
/// integer-only v1 lowering.
struct ConcreteV1Args {
    values: Vec<IntTy>,
    keys: Box<[CanonicalTypeKey]>,
}

/// Borrow recursive use-site arguments at the current integer-only mono
/// boundary. The AST arguments remain intact until request validation and
/// emitted-name reservation both succeed.
fn concrete_v1_type_args(type_args: &[TypeArg]) -> MResult<ConcreteV1Args> {
    let mut values = Vec::with_capacity(type_args.len());
    let mut keys = Vec::with_capacity(type_args.len());
    for TypeArg { ty, span } in type_args {
        values.push(
            ty.try_to_concrete_v1_int()
                .map_err(|error| unsupported_type_arg(*span, error))?,
        );
        keys.push(
            ty.concrete_key()
                .map_err(|error| unsupported_type_arg(*span, error))?,
        );
    }
    Ok(ConcreteV1Args {
        values,
        keys: keys.into_boxed_slice(),
    })
}

fn require_concrete_v1_type_args(type_args: &[TypeArg]) -> MResult<()> {
    for arg in type_args {
        arg.ty
            .try_to_concrete_v1_int()
            .map_err(|error| unsupported_type_arg(arg.span, error))?;
    }
    Ok(())
}

fn substitute_type_args(type_args: &mut [TypeArg], args: &[IntTy]) -> MResult<()> {
    let substitutions: Vec<GenericTy> = args
        .iter()
        .copied()
        .map(GenericTy::from_legacy_int)
        .collect();
    for arg in type_args {
        arg.ty = arg
            .ty
            .substitute(&substitutions)
            .map_err(|error| unsupported_type_arg(arg.span, error))?;
    }
    Ok(())
}

impl Mono {
    fn request(
        &mut self,
        kind: TemplateKind,
        template: &str,
        args: &ConcreteV1Args,
        span: Span,
        depth: usize,
    ) -> MResult<String> {
        if let Some(index) = args.values.iter().find_map(|arg| match arg {
            IntTy::TParam(index) => Some(*index),
            _ => None,
        }) {
            return Err(unsupported_type_arg(
                span,
                GenericTyError::UnsubstitutedTypeParameter(TypeParamId::from_legacy(index)),
            ));
        }
        let (expected, bounds) = match kind {
            TemplateKind::Function => {
                let template = self
                    .fn_templates
                    .get(template)
                    .expect("function requests name a known template");
                (template.type_params.len(), template.type_bounds.clone())
            }
            TemplateKind::Class => {
                let template = self
                    .class_templates
                    .get(template)
                    .expect("class requests name a known template");
                (template.type_params.len(), template.type_bounds.clone())
            }
        };
        if args.values.len() != expected {
            return Err(Diagnostic {
                name: "mono.arity".into(),
                title: format!(
                    "`{template}` takes {expected} type argument(s), {} given",
                    args.values.len()
                ),
                span,
                label: "wrong number of type arguments".into(),
                notes: vec![],
            });
        }
        for (bound, arg) in bounds.iter().zip(&args.values) {
            if let Some(b) = bound {
                if !self
                    .impls
                    .contains_key(&(b.clone(), arg.name().to_string()))
                {
                    return Err(Diagnostic {
                        name: "mono.unsatisfied_bound".into(),
                        title: format!("`{}` does not implement `{b}`", arg.name()),
                        span,
                        label: format!("the bound requires `impl {b} for {}`", arg.name()),
                        notes: vec![],
                    });
                }
            }
        }
        let key = InstanceKey::from_args(kind, template, args);
        if let Some(emitted_name) = self.instances.get(&key) {
            return Ok(emitted_name.clone());
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

        let emitted_name = mangle(template, &args.values);
        if let Some(owner) = self.emitted_names.get(&emitted_name) {
            let occupied_by = match owner {
                EmittedNameOwner::Source(source_kind) => source_kind.description().to_string(),
                EmittedNameOwner::Instance(existing) => format!(
                    "a distinct {} instance of `{}`",
                    existing.kind.description(),
                    existing.template
                ),
            };
            return Err(Diagnostic {
                name: "mono.name_collision".into(),
                title: format!("generated name `{emitted_name}` is already occupied"),
                span,
                label: format!(
                    "this {} instantiation collides with {occupied_by}",
                    kind.description()
                ),
                notes: vec![(
                    "note".into(),
                    "instance identity is structural, but v1 keeps the legacy underscore \
                     spelling for compatible programs; rename one declaration to make the \
                     emitted names distinct"
                        .into(),
                )],
            });
        }

        self.instances.insert(key.clone(), emitted_name.clone());
        self.emitted_names.insert(
            emitted_name.clone(),
            EmittedNameOwner::Instance(key.clone()),
        );
        self.queue.push_back(Request {
            key,
            emitted_name: emitted_name.clone(),
            args: args.values.clone(),
            span,
            depth,
        });
        Ok(emitted_name)
    }

    fn instantiate(&mut self, req: Request) -> MResult<()> {
        let proof_reuse = adr0009_int_model_reuse(&req.key.template, &req.args, req.span)?;
        if req.key.kind == TemplateKind::Class {
            let template = self.class_templates[&req.key.template].clone();
            let mut c = template;
            let param_names = std::mem::take(&mut c.type_params);
            let bounds = std::mem::take(&mut c.type_bounds);
            let (text_map, bound_calls) = self.subst_maps(&param_names, &bounds, &req.args);
            c.name = req.emitted_name;
            c.proof_reuse = proof_reuse;
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
            if let Some(deinit) = &mut c.deinit {
                subst_stmts(deinit, &req.args, &text_map, &bound_calls)?;
                self.rewrite_stmts(deinit, req.depth + 1)?;
            }
            self.new_classes.push(c);
        } else {
            let template = self.fn_templates[&req.key.template].clone();
            let mut f = template;
            let param_names = std::mem::take(&mut f.type_params);
            let bounds = std::mem::take(&mut f.type_bounds);
            let (text_map, bound_calls) = self.subst_maps(&param_names, &bounds, &req.args);
            f.name = req.emitted_name;
            // Template-verified instances (ADR 0009): skip their own
            // obligations; owe the substituted `requires`.
            f.proof_reuse = proof_reuse;
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
    ) -> (
        HashMap<String, String>,
        HashMap<String, (String, HashSet<String>)>,
    ) {
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
                | Stmt::StaticAlloc { size: e, .. }
                | Stmt::SystemAlloc { size: e, .. }
                | Stmt::Return { value: Some(e), .. } => self.rewrite_expr(e, depth)?,
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    self.rewrite_expr(ptr, depth)?;
                    self.rewrite_expr(res, depth)?;
                    self.rewrite_expr(release, depth)?;
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                    self.rewrite_stmts(body, depth)?
                }
                Stmt::Decl { init: None, .. }
                | Stmt::Return { value: None, .. }
                | Stmt::Assert(_) => {}
                Stmt::Store { index, value, .. } | Stmt::FieldStore { index, value, .. } => {
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
                require_concrete_v1_type_args(type_args)?;
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
                    let targs = concrete_v1_type_args(type_args)?;
                    let emitted = self.request(
                        TemplateKind::Function,
                        &callee.clone(),
                        &targs,
                        *callee_span,
                        depth,
                    )?;
                    *callee = emitted;
                    type_args.clear();
                } else if !type_args.is_empty() {
                    return Err(Diagnostic {
                        name: "mono.not_generic".into(),
                        title: format!("`{callee}` takes no type arguments"),
                        span: *callee_span,
                        label: "not a generic function".into(),
                        notes: vec![],
                    });
                }
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
            }
            ExprKind::CtorCall {
                class,
                class_span,
                type_args,
                args,
                ..
            } => {
                require_concrete_v1_type_args(type_args)?;
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
                    let targs = concrete_v1_type_args(type_args)?;
                    let emitted = self.request(
                        TemplateKind::Class,
                        &class.clone(),
                        &targs,
                        *class_span,
                        depth,
                    )?;
                    *class = emitted;
                    type_args.clear();
                } else if !type_args.is_empty() {
                    return Err(Diagnostic {
                        name: "mono.not_generic".into(),
                        title: format!("`{class}` takes no type arguments"),
                        span: *class_span,
                        label: "not a generic class".into(),
                        notes: vec![],
                    });
                }
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
            }
            ExprKind::MethodCall { args, .. } => {
                for a in args.iter_mut() {
                    self.rewrite_expr(a, depth)?;
                }
            }
            ExprKind::RawOp { args, .. }
            | ExprKind::ResOp { args, .. }
            | ExprKind::DeviceOp { args, .. } => {
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
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => self.rewrite_expr(index, depth)?,
            ExprKind::AllocArray { len, init, .. } => {
                self.rewrite_expr(len, depth)?;
                self.rewrite_expr(init, depth)?;
            }
            ExprKind::ArrayLit(elems) => {
                for el in elems.iter_mut() {
                    self.rewrite_expr(el, depth)?;
                }
            }
            ExprKind::RecordLit { args, .. } => {
                for arg in args.iter_mut() {
                    self.rewrite_expr(arg, depth)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn adr0009_int_model_reuse(template: &str, args: &[IntTy], span: Span) -> MResult<ProofReuse> {
    if let Some(index) = args.iter().find_map(|argument| match argument {
        IntTy::TParam(index) => Some(*index),
        _ => None,
    }) {
        return Err(unsupported_type_arg(
            span,
            GenericTyError::UnsubstitutedTypeParameter(TypeParamId::from_legacy(index)),
        ));
    }
    Ok(ProofReuse::adr0009_int_model(template.to_string()))
}

fn subst_intty(t: &mut IntTy, args: &[IntTy]) {
    if let IntTy::TParam(i) = t {
        *t = args[*i as usize];
    }
}

fn subst_value_ty(t: &mut ValueTy, args: &[IntTy]) {
    match *t {
        ValueTy::Param(parameter) => *t = ValueTy::Int(args[parameter.index()]),
        ValueTy::Int(mut integer) => {
            subst_intty(&mut integer, args);
            *t = ValueTy::Int(integer);
        }
        ValueTy::Bool | ValueTy::Record(_) => {}
    }
}

fn subst_affine_option_ty(t: &mut AffineOptionTy, args: &[IntTy]) {
    match *t {
        AffineOptionTy::Array(mut element) => {
            subst_value_ty(&mut element, args);
            *t = AffineOptionTy::Array(element);
        }
    }
}

fn subst_ty(t: &mut Ty, args: &[IntTy]) {
    match *t {
        Ty::Param(parameter) => *t = Ty::Int(args[parameter.index()]),
        Ty::Int(mut integer) => {
            subst_intty(&mut integer, args);
            *t = Ty::Int(integer);
        }
        Ty::Array(mut element, mutability) => {
            subst_value_ty(&mut element, args);
            *t = Ty::Array(element, mutability);
        }
        Ty::Option(mut element) => {
            subst_value_ty(&mut element, args);
            *t = Ty::Option(element);
        }
        Ty::AffineOption(mut payload) => {
            subst_affine_option_ty(&mut payload, args);
            *t = Ty::AffineOption(payload);
        }
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
            Stmt::VarDecl {
                init: value, ty, ..
            } => {
                if let Some(ty) = ty {
                    subst_ty(ty, args);
                }
                subst_expr(value, args, bound_calls)?;
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::FieldAssign { value, .. }
            | Stmt::StaticAlloc { size: value, .. }
            | Stmt::SystemAlloc { size: value, .. } => subst_expr(value, args, bound_calls)?,
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                subst_expr(ptr, args, bound_calls)?;
                subst_expr(res, args, bound_calls)?;
                subst_expr(release, args, bound_calls)?;
            }
            Stmt::Return { value: Some(e), .. } => subst_expr(e, args, bound_calls)?,
            Stmt::Return { value: None, .. } => {}
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                subst_stmts(body, args, text_map, bound_calls)?
            }
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
            Stmt::Assert(c) => {
                c.text = subst_clause_text(&c.text, text_map);
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
    if let Some(ty) = &mut e.ty {
        subst_ty(ty, args);
    }
    match &mut e.kind {
        ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
            subst_intty(target, args);
            subst_expr(arg, args, bound_calls)?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            subst_value_ty(elem, args);
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
            substitute_type_args(type_args, args)?;
            for x in a.iter_mut() {
                subst_expr(x, args, bound_calls)?;
            }
        }
        ExprKind::MethodCall { args: a, .. }
        | ExprKind::RawOp { args: a, .. }
        | ExprKind::ResOp { args: a, .. }
        | ExprKind::DeviceOp { args: a, .. } => {
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
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => subst_expr(index, args, bound_calls)?,
        ExprKind::ArrayLit(elems) => {
            for el in elems.iter_mut() {
                subst_expr(el, args, bound_calls)?;
            }
        }
        ExprKind::RecordLit { args: fields, .. } => {
            for field in fields.iter_mut() {
                subst_expr(field, args, bound_calls)?;
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
                while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::LineMap;

    fn parse_program(source: &str) -> Program {
        let lines = LineMap::new(source);
        let scanned = crate::scan::scan(source);
        let tokens = crate::lexer::lex(&scanned.program_text).expect("test source should lex");
        crate::parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text)
            .expect("test source should parse")
    }

    fn parse_and_monomorphize(source: &str) -> Program {
        let mut program = parse_program(source);
        monomorphize(&mut program).expect("test source should monomorphize");
        program
    }

    fn monomorphization_error(source: &str) -> Diagnostic {
        let mut program = parse_program(source);
        monomorphize(&mut program).expect_err("test source should fail monomorphization")
    }

    fn call_name(expr: &Expr) -> (&str, &[TypeArg]) {
        let ExprKind::Call {
            callee, type_args, ..
        } = &expr.kind
        else {
            panic!("expected a call, found {:?}", expr.kind);
        };
        (callee, type_args)
    }

    #[test]
    fn rejects_duplicate_traits_at_the_second_declaration() {
        let source = r#"
trait Repeated {}

trait Repeated {}
"#;
        let mut program = parse_program(source);
        let expected_span = program.traits[1].name_span;
        let error =
            monomorphize(&mut program).expect_err("duplicate traits must not overwrite each other");

        assert_eq!(error.name, "trait.duplicate");
        assert_eq!(error.span, expected_span);
        assert_eq!(error.label, "second definition here");
    }

    #[test]
    fn keeps_trait_and_function_names_in_separate_namespaces() {
        let program = parse_and_monomorphize(
            r#"
trait SharedName {}

fn SharedName() {}
"#,
        );

        assert!(
            program
                .traits
                .iter()
                .any(|trait_| trait_.name == "SharedName")
        );
        assert!(
            program
                .fns
                .iter()
                .any(|function| function.name == "SharedName")
        );
    }

    #[test]
    fn rejects_duplicate_impl_spec_heads_at_the_second_declaration() {
        let source = r#"
trait Measured {
    /// spec measure : int → int
    fn read(Self value) -> u64;
}

impl Measured for u64 {
    /// def measure (x : int) : int := x
    /// def measure (x : int) : int := x + 1
    fn read(u64 value) -> u64 {
        return value;
    }
}
"#;
        let mut program = parse_program(source);
        let mut spans: Vec<Span> = program.impls[0]
            .ghosts
            .iter()
            .map(|ghost| ghost.span)
            .collect();
        spans.sort_by_key(|span| (span.start, span.end));
        let error = monomorphize(&mut program)
            .expect_err("duplicate impl specs must not overwrite each other");

        assert_eq!(error.name, "impl.duplicate_spec");
        assert_eq!(error.span, spans[1]);
        assert!(error.title.contains("spec `measure` twice"));
    }

    #[test]
    fn rejects_duplicate_impl_methods_at_the_second_declaration() {
        let source = r#"
trait Runnable {
    fn run(Self value) -> u64;
}

impl Runnable for u64 {
    fn run(u64 value) -> u64 {
        return value;
    }

    fn run(u64 value) -> u64 {
        return value;
    }
}
"#;
        let mut program = parse_program(source);
        let mut spans: Vec<Span> = program.impls[0]
            .fns
            .iter()
            .map(|method| method.name_span)
            .collect();
        spans.sort_by_key(|span| (span.start, span.end));
        let error = monomorphize(&mut program)
            .expect_err("duplicate impl methods must not overwrite each other");

        assert_eq!(error.name, "impl.duplicate_fn");
        assert_eq!(error.span, spans[1]);
        assert!(error.title.contains("method `run` twice"));
    }

    #[test]
    fn reports_the_earliest_extra_impl_spec() {
        let source = r#"
trait Runnable {
    fn run(Self value) -> u64;
}

impl Runnable for u64 {
    /// def zeta (x : int) : int := x
    /// def alpha (x : int) : int := x
    fn run(u64 value) -> u64 {
        return value;
    }
}
"#;
        let mut program = parse_program(source);
        let expected_span = program.impls[0]
            .ghosts
            .iter()
            .min_by_key(|ghost| (ghost.span.start, ghost.span.end))
            .expect("two impl specs")
            .span;
        let error = monomorphize(&mut program).expect_err("extra specs must be rejected");

        assert_eq!(error.name, "impl.unknown_spec");
        assert_eq!(error.span, expected_span);
        assert!(error.title.contains("`zeta`"));
    }

    #[test]
    fn reports_the_earliest_extra_impl_method() {
        let source = r#"
trait Runnable {
    fn run(Self value) -> u64;
}

impl Runnable for u64 {
    fn run(u64 value) -> u64 {
        return value;
    }

    fn zeta(u64 value) -> u64 {
        return value;
    }

    fn alpha(u64 value) -> u64 {
        return value;
    }
}
"#;
        let mut program = parse_program(source);
        let expected_span = program.impls[0]
            .fns
            .iter()
            .find(|method| method.name == "zeta")
            .expect("zeta method")
            .name_span;
        let error = monomorphize(&mut program).expect_err("extra methods must be rejected");

        assert_eq!(error.name, "impl.extra_fn");
        assert_eq!(error.span, expected_span);
        assert!(error.title.contains("`zeta`"));
    }

    #[test]
    fn rejects_same_kind_instances_with_ambiguous_legacy_names() {
        let source = r#"
fn amb_i32<T>(T value) -> T {
    return value;
}

fn amb<T, U>(U value) -> U {
    return value;
}

fn root() -> u8 {
    u8 first = amb_i32<u8>(1);
    return amb<i32, u8>(first);
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "mono.name_collision");
        assert_eq!(error.span.start, source.rfind("amb<i32").unwrap());
        assert!(error.title.contains("amb_i32_u8"));
        assert!(error.label.contains("distinct function instance"));
    }

    #[test]
    fn rejects_cross_kind_instances_with_the_same_legacy_name() {
        let source = r#"
fn Cross_i32<T>(T value) -> T {
    return value;
}

class Cross<T, U> {
    U value;

    init make(U value) {
        self.value = value;
    }
}

fn root() {
    u8 first = Cross_i32<u8>(1);
    var instance = Cross<i32, u8>::make(first);
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "mono.name_collision");
        assert_eq!(error.span.start, source.rfind("Cross<i32").unwrap());
        assert!(error.title.contains("Cross_i32_u8"));
        assert!(error.label.contains("distinct function instance"));
    }

    #[test]
    fn rejects_an_instance_name_occupied_by_an_ordinary_root() {
        let source = r#"
fn rooted_u8() -> u8 {
    return 0;
}

fn rooted<T>(T value) -> T {
    return value;
}

fn root() -> u8 {
    return rooted<u8>(1);
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "mono.name_collision");
        assert_eq!(error.span.start, source.rfind("rooted<u8>").unwrap());
        assert!(error.title.contains("rooted_u8"));
        assert!(error.label.contains("source function"));
    }

    #[test]
    fn rejects_an_instance_name_occupied_by_a_retained_template() {
        let source = r#"
fn named_u8<T>(T value) -> T {
    return value;
}

fn named<T>(T value) -> T {
    return value;
}

fn root() -> u8 {
    return named<u8>(1);
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "mono.name_collision");
        assert_eq!(error.span.start, source.rfind("named<u8>").unwrap());
        assert!(error.title.contains("named_u8"));
        assert!(error.label.contains("generic function template"));
    }

    #[test]
    fn rejects_ordinary_root_and_generic_template_with_the_same_source_name() {
        let source = r#"
fn duplicate() -> u8 {
    return 0;
}

fn duplicate<T>(T value) -> T {
    return value;
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "type.duplicate_function");
        assert_eq!(error.span.start, source.rfind("duplicate<T>").unwrap());
    }

    #[test]
    fn concrete_v1_arguments_keep_keys_from_recursive_source_types() {
        let source_type = GenericTy::Int(IntTy::I32);
        let source_key = source_type.concrete_key().unwrap();
        let args = concrete_v1_type_args(&[TypeArg {
            ty: source_type,
            span: Span::new(7, 10),
        }])
        .unwrap();

        assert_eq!(args.values, vec![IntTy::I32]);
        assert_eq!(args.keys.as_ref(), &[source_key]);

        // Instance identity consumes the structural-key channel, not the
        // temporary v1 substitution values. Keep this deliberately mismatched
        // construction as a wiring regression for the recursive-type rollout.
        let bool_key = GenericTy::Bool.concrete_key().unwrap();
        let mismatched = ConcreteV1Args {
            values: vec![IntTy::I32],
            keys: vec![bool_key.clone()].into_boxed_slice(),
        };
        let key = InstanceKey::from_args(TemplateKind::Function, "identity", &mismatched);
        assert_eq!(key.args.as_ref(), &[bool_key]);
        assert_eq!(mangle("identity", &mismatched.values), "identity_i32");
    }

    #[test]
    fn deduplicates_only_exact_structural_instance_requests() {
        let program = parse_and_monomorphize(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

fn root() -> u8 {
    u8 first = identity<u8>(1);
    return identity<u8>(first);
}
"#,
        );
        assert_eq!(
            program
                .fns
                .iter()
                .filter(|function| function.name == "identity_u8")
                .count(),
            1
        );
    }

    #[test]
    fn rejects_duplicate_generic_source_declarations_before_extraction() {
        let source = r#"
fn duplicate<T>(T value) -> T {
    return value;
}

fn duplicate<U>(U value) -> U {
    return value;
}
"#;
        let error = monomorphization_error(source);
        assert_eq!(error.name, "type.duplicate_function");
        assert_eq!(error.span.start, source.rfind("duplicate<U>").unwrap());
    }

    #[test]
    fn rewrites_generic_calls_nested_in_record_literals() {
        let program = parse_and_monomorphize(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

record Pair #[layout(size := 16, align := 8)] {
    #[offset(0)] u64 left;
    #[offset(8)] u64 right;
}

fn record_root() -> Pair {
    return Pair(identity<u64>(20), identity<u64>(22));
}
"#,
        );

        let root = program
            .fns
            .iter()
            .find(|f| f.name == "record_root")
            .expect("root function");
        let Stmt::Return {
            value:
                Some(Expr {
                    kind: ExprKind::RecordLit { args, .. },
                    ..
                }),
            ..
        } = &root.body[0]
        else {
            panic!("expected the root to return a record literal");
        };
        assert_eq!(args.len(), 2);
        for field in args {
            let (callee, type_args) = call_name(field);
            assert_eq!(callee, "identity_u64");
            assert!(type_args.is_empty());
        }
        assert!(program.fns.iter().any(|f| f.name == "identity_u64"));
    }

    #[test]
    fn substitutes_and_rewrites_generic_uses_in_class_deinits() {
        let program = parse_and_monomorphize(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

class Plain {
    u64 value;

    init make(u64 value) {
        self.value = value;
    }

    deinit {
        u64 copy = identity<u64>(self.value);
    }
}

class Generic<T> {
    T value;

    init make(T value) {
        self.value = value;
    }

    deinit {
        /// assert T.max = T.max
        T copy = identity<T>(self.value);
    }
}

fn class_roots() {
    var plain = Plain::make(1);
    var generic = Generic<u64>::make(2);
}
"#,
        );

        let plain = program
            .classes
            .iter()
            .find(|class| class.name == "Plain")
            .expect("non-generic root class");
        let plain_deinit = plain.deinit.as_ref().expect("plain deinit");
        let Stmt::Decl {
            init: Some(plain_call),
            ..
        } = &plain_deinit[0]
        else {
            panic!("expected the plain deinit declaration");
        };
        let (callee, type_args) = call_name(plain_call);
        assert_eq!(callee, "identity_u64");
        assert!(type_args.is_empty());

        let generic = program
            .classes
            .iter()
            .find(|class| class.name == "Generic_u64")
            .expect("instantiated generic class");
        let generic_deinit = generic.deinit.as_ref().expect("generic deinit");
        let Stmt::Assert(clause) = &generic_deinit[0] else {
            panic!("expected the substituted deinit assertion");
        };
        assert_eq!(clause.text, "u64.max = u64.max");
        let Stmt::Decl {
            ty,
            init: Some(generic_call),
            ..
        } = &generic_deinit[1]
        else {
            panic!("expected the generic deinit declaration");
        };
        assert_eq!(*ty, Ty::Int(IntTy::U64));
        let (callee, type_args) = call_name(generic_call);
        assert_eq!(callee, "identity_u64");
        assert!(type_args.is_empty());
        assert!(program.fns.iter().any(|f| f.name == "identity_u64"));
    }

    #[test]
    fn rejects_dormant_noninteger_type_arguments_at_the_v1_boundary() {
        let mut program = parse_program(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

fn root() -> u8 {
    return identity<u8>(7);
}
"#,
        );
        let root = program
            .fns
            .iter_mut()
            .find(|function| function.name == "root")
            .expect("root function");
        let Stmt::Return {
            value: Some(expression),
            ..
        } = &mut root.body[0]
        else {
            panic!("expected the root return");
        };
        let ExprKind::Call { type_args, .. } = &mut expression.kind else {
            panic!("expected a generic call");
        };
        let span = type_args[0].span;
        type_args[0].ty = GenericTy::Bool;

        let error = monomorphize(&mut program).expect_err("bool is outside G0's enabled domain");
        assert_eq!(error.name, "mono.type_arg_unsupported");
        assert_eq!(error.span, span);
        assert!(error.label.contains("only `u8`..`u64`"));
    }

    #[test]
    fn rejects_dormant_type_parameters_outside_the_enclosing_arity() {
        let mut program = parse_program(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

fn dormant<T>(T value) -> T {
    return identity<T>(value);
}
"#,
        );
        let dormant = program
            .fns
            .iter_mut()
            .find(|function| function.name == "dormant")
            .expect("dormant template");
        let Stmt::Return {
            value: Some(expression),
            ..
        } = &mut dormant.body[0]
        else {
            panic!("expected the dormant return");
        };
        let ExprKind::Call { type_args, .. } = &mut expression.kind else {
            panic!("expected a generic call");
        };
        let span = type_args[0].span;
        type_args[0].ty = GenericTy::Param(TypeParamId::from_legacy(1));

        let error = monomorphize(&mut program).expect_err("parameter 1 exceeds arity 1");
        assert_eq!(error.name, "mono.type_arg_unsupported");
        assert_eq!(error.span, span);
        assert!(error.notes[0].1.contains("outside this declaration"));
    }

    #[test]
    fn rejects_out_of_bounds_declaration_parameters_before_substitution() {
        let mut program = parse_program(
            r#"
fn identity<T>(T value) -> T {
    return value;
}

fn root() -> u8 {
    return identity<u8>(7);
}
"#,
        );
        let template = program
            .fns
            .iter_mut()
            .find(|function| function.name == "identity")
            .expect("identity template");
        let span = template.params[0].span;
        template.params[0].ty = Ty::Param(TypeParamId::from_legacy(1));

        let error = monomorphize(&mut program)
            .expect_err("a malformed declaration parameter must not index past its arguments");
        assert_eq!(error.name, "mono.type_param_out_of_bounds");
        assert_eq!(error.span, span);
        assert!(error.label.contains("parameter #1"));
        assert!(error.label.contains("has 1"));
    }

    #[test]
    fn rejects_forged_proof_reuse_before_any_vc_can_be_skipped() {
        let mut program = parse_program(
            r#"
fn root() -> u8 {
    return 7;
}
"#,
        );
        let span = program.fns[0].name_span;
        program.fns[0].proof_reuse = ProofReuse::adr0009_int_model("forged".into());

        let error = monomorphize(&mut program).expect_err("proof reuse is mono-authored");
        assert_eq!(error.name, "mono.forged_proof_reuse");
        assert_eq!(error.span, span);
    }

    #[test]
    fn prepares_trait_calls_nested_in_option_construction() {
        let program = parse_and_monomorphize(
            r#"
trait Hashable {
    /// spec hash : int → int
    /// post result = Self::hash x
    fn hash(Self x) -> u64;
}

impl Hashable for u64 {
    /// def hash (x : int) : int := x
    fn hash(u64 x) -> u64 {
        return x;
    }
}

fn wrapped_hash<K: Hashable>(K value) -> option<u64> {
    return some(K::hash(value));
}

fn root() -> option<u64> {
    return wrapped_hash<u64>(42);
}
"#,
        );

        let template = program
            .fn_templates
            .iter()
            .find(|function| function.name == "wrapped_hash")
            .expect("retained verified template");
        let Stmt::Return {
            value:
                Some(Expr {
                    kind: ExprKind::SomeE(inner),
                    ..
                }),
            ..
        } = &template.body[0]
        else {
            panic!("expected the template to return an option");
        };
        assert!(matches!(inner.kind, ExprKind::TraitCall { .. }));

        let instance = program
            .fns
            .iter()
            .find(|function| function.name == "wrapped_hash_u64")
            .expect("concrete instance");
        let Stmt::Return {
            value:
                Some(Expr {
                    kind: ExprKind::SomeE(inner),
                    ..
                }),
            ..
        } = &instance.body[0]
        else {
            panic!("expected the instance to return an option");
        };
        assert!(matches!(inner.kind, ExprKind::Call { .. }));
    }

    #[test]
    fn integer_instances_substitute_value_types_and_record_proof_domain() {
        let program = parse_and_monomorphize(
            r#"
fn make<T>(T value) -> option<T> {
    [T] items = alloc_array<T>(1, value);
    return some(items[0]);
}

fn root() -> option<u16> {
    return make<u16>(7);
}
"#,
        );

        let instance = program
            .fns
            .iter()
            .find(|function| function.name == "make_u16")
            .expect("concrete integer instance");
        assert_eq!(instance.params[0].ty, Ty::Int(IntTy::U16));
        assert_eq!(instance.ret, Ty::Option(ValueTy::Int(IntTy::U16)));
        assert_eq!(instance.proof_reuse.template(), Some("make"));
        assert!(matches!(
            &instance.proof_reuse,
            ProofReuse::Adr0009IntModel(_)
        ));

        let Stmt::Decl {
            ty,
            init: Some(initializer),
            ..
        } = &instance.body[0]
        else {
            panic!("expected instantiated array declaration");
        };
        assert_eq!(*ty, Ty::Array(ValueTy::Int(IntTy::U16), Mutability::Owned));
        let ExprKind::AllocArray { elem, .. } = &initializer.kind else {
            panic!("expected instantiated allocation");
        };
        assert_eq!(*elem, ValueTy::Int(IntTy::U16));

        validate_concrete_output(&program).expect("ordinary output is fully concrete");
        let retained = program
            .fn_templates
            .iter()
            .find(|function| function.name == "make")
            .expect("retained template");
        assert_eq!(
            retained.params[0].ty,
            Ty::Param(TypeParamId::from_legacy(0))
        );
        assert_eq!(
            retained.ret,
            Ty::Option(ValueTy::Param(TypeParamId::from_legacy(0)))
        );
    }

    #[test]
    fn integer_instances_substitute_through_affine_option_payloads() {
        let program = parse_and_monomorphize(
            r#"
fn hold<T>(option<[T]> value) -> option<[T]> {
    return value;
}

fn root(option<[i32]> value) -> option<[i32]> {
    return hold<i32>(value);
}
"#,
        );

        let instance = program
            .fns
            .iter()
            .find(|function| function.name == "hold_i32")
            .expect("concrete affine-option instance");
        let expected = Ty::AffineOption(AffineOptionTy::Array(ValueTy::Int(IntTy::I32)));
        assert_eq!(instance.params[0].ty, expected);
        assert_eq!(instance.ret, expected);
        validate_concrete_output(&program).expect("affine-option output is fully concrete");

        let retained = program
            .fn_templates
            .iter()
            .find(|function| function.name == "hold")
            .expect("retained affine-option template");
        let parameter = TypeParamId::from_legacy(0);
        let abstract_ty = Ty::AffineOption(AffineOptionTy::Array(ValueTy::Param(parameter)));
        assert_eq!(retained.params[0].ty, abstract_ty);
        assert_eq!(retained.ret, abstract_ty);
    }

    #[test]
    fn rejects_every_parameter_representation_in_ordinary_output() {
        let base = parse_program(
            r#"
fn root(i32 value) -> i32 {
    [i32] items = alloc_array<i32>(1, value);
    return value;
}
"#,
        );
        let parameter = TypeParamId::from_legacy(0);

        let mut direct = base.clone();
        direct.fns[0].params[0].ty = Ty::Param(parameter);
        let error = monomorphize(&mut direct).expect_err("direct parameter must not escape");
        assert_eq!(error.name, "mono.type_param_out_of_bounds");

        let mut noncanonical_array = base.clone();
        let Stmt::Decl { ty, .. } = &mut noncanonical_array.fns[0].body[0] else {
            panic!("expected array declaration");
        };
        *ty = Ty::Array(ValueTy::Int(IntTy::TParam(0)), Mutability::Owned);
        let error = monomorphize(&mut noncanonical_array)
            .expect_err("legacy parameter in a value type must not escape");
        assert_eq!(error.name, "mono.type_param_out_of_bounds");

        let mut allocation = base;
        let Stmt::Decl {
            init: Some(initializer),
            ..
        } = &mut allocation.fns[0].body[0]
        else {
            panic!("expected initialized array declaration");
        };
        let ExprKind::AllocArray { elem, .. } = &mut initializer.kind else {
            panic!("expected allocation");
        };
        *elem = ValueTy::Param(parameter);
        let error =
            monomorphize(&mut allocation).expect_err("allocation parameter must not escape");
        assert_eq!(error.name, "mono.type_param_out_of_bounds");

        let mut escaped_affine = parse_program("fn root() {}\n");
        escaped_affine.fns[0].ret =
            Ty::AffineOption(AffineOptionTy::Array(ValueTy::Param(parameter)));
        let error = validate_concrete_output(&escaped_affine)
            .expect_err("affine-option payload parameters must not escape");
        assert_eq!(error.name, "mono.unsubstituted_type_param");
        assert!(error.label.contains("affine-option array element type"));
    }
}

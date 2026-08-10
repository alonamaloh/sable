//! Module loading (ADR 0013): `use` imports resolved file-per-module,
//! parsed into one combined program with globally consistent spans.
//!
//! The trick that keeps diagnostics exact: `scan` blanks proof lines, so
//! `program_text` is byte-for-byte the same length as its source. Module
//! sources are concatenated in load order, each module's tokens and proof
//! blocks are shifted by its byte/line base, and every span in the merged
//! AST then indexes one combined string. `ModuleSet::locate` maps any
//! span back to its file and per-file line for rendering.
//!
//! v1 semantics: everything a module declares is exported; imports are a
//! flat merge with cross-module name collisions diagnosed; `use m::{a}`
//! additionally validates the listed names exist in `m`. Verification of
//! a root file covers the whole import DAG (separate verification with
//! Lean-level imports is the next slice).

use crate::ast::{Program, UseDecl};
use crate::diag::Diagnostic;
use crate::span::{LineMap, Span};
use crate::{lexer, parser, scan};
use std::path::{Path, PathBuf};

pub struct ModuleInfo {
    /// Path as shown in diagnostics.
    pub display: String,
    /// Canonical filesystem path (empty for synthesized single-module
    /// sets) — the stable identity used by the per-module verification
    /// cache and by cross-load span remapping.
    pub path: PathBuf,
    /// Byte offset of this module's source in the combined string.
    pub base: usize,
    /// Length of this module's source.
    pub len: usize,
    /// This module's own source text (for rendering excerpts).
    pub source: String,
    /// Line map over this module's own source.
    pub lines: LineMap,
}

pub struct ModuleSet {
    /// Root module first (base 0), dependencies after in load order.
    pub modules: Vec<ModuleInfo>,
    /// All sources concatenated (spans in the merged AST index this).
    pub combined_source: String,
}

impl ModuleSet {
    pub fn single(display: String, source: String) -> ModuleSet {
        let lines = LineMap::new(&source);
        let len = source.len();
        ModuleSet {
            combined_source: source.clone(),
            modules: vec![ModuleInfo {
                display,
                path: PathBuf::new(),
                base: 0,
                len,
                source,
                lines,
            }],
        }
    }

    pub fn module_of(&self, offset: usize) -> &ModuleInfo {
        self.modules
            .iter()
            .rev()
            .find(|m| m.base <= offset && offset < m.base + m.len.max(1))
            .unwrap_or(&self.modules[0])
    }

    /// `(file, line, col)` of a combined-source offset.
    pub fn locate(&self, offset: usize) -> (&str, usize, usize) {
        let m = self.module_of(offset);
        let (line, col) = m.lines.line_col(offset - m.base);
        (&m.display, line, col)
    }

    /// Render a diagnostic against its own module's source.
    pub fn render(&self, d: &Diagnostic) -> String {
        let m = self.module_of(d.span.start);
        let mut local = d.clone();
        local.span = Span::new(
            d.span.start.saturating_sub(m.base),
            d.span.end.saturating_sub(m.base),
        );
        local.render(&m.display, &m.source, &m.lines)
    }

    /// Render a diagnostic at a given severity level.
    pub fn render_level(&self, level: &str, d: &Diagnostic) -> String {
        let m = self.module_of(d.span.start);
        let mut local = d.clone();
        local.span = Span::new(
            d.span.start.saturating_sub(m.base),
            d.span.end.saturating_sub(m.base),
        );
        local.render_level(level, &m.display, &m.source, &m.lines)
    }
}

struct Loading {
    set: ModuleSet,
    programs: Vec<(usize, Program)>,
    /// Canonical paths of loaded modules (dedup) → module index.
    seen: Vec<(PathBuf, usize)>,
    /// DFS stack of canonical paths (cycle detection).
    stack: Vec<PathBuf>,
    module_paths: Vec<PathBuf>,
    /// Resolved direct imports: (importer idx, the `use`, dep idx) —
    /// the edges the visibility pass (ADR 0019) checks against.
    imports: Vec<(usize, UseDecl, usize)>,
    /// Per module: the extern class-name table its parse was seeded
    /// with, so parse-time `Ty::Class` indices resolve back to names.
    externs: Vec<(usize, Vec<String>)>,
}

/// Load `root` and its transitive imports; returns the merged program
/// and the module set for rendering. Errors carry combined-source spans
/// (or the `use` span of the module that failed to load).
pub fn load(
    root: &Path,
    module_paths: &[PathBuf],
) -> Result<(Program, ModuleSet), (Diagnostic, ModuleSet)> {
    let mut loading = Loading {
        set: ModuleSet {
            modules: Vec::new(),
            combined_source: String::new(),
        },
        programs: Vec::new(),
        seen: Vec::new(),
        stack: Vec::new(),
        module_paths: module_paths.to_vec(),
        imports: Vec::new(),
        externs: Vec::new(),
    };
    if let Err(d) = load_file(&mut loading, root, None) {
        // Errors carry combined-source spans; hand back the partial set
        // so they render against the right file. An empty set (root
        // unreadable) gets a placeholder for span (0,0) rendering.
        if loading.set.modules.is_empty() {
            loading.set = ModuleSet::single(root.display().to_string(), String::new());
        }
        return Err((d, loading.set));
    }
    if let Err(d) = enforce_visibility(&loading) {
        return Err((d, loading.set));
    }
    match merge(loading) {
        Ok(ok) => Ok(ok),
        Err((d, set)) => Err((d, set)),
    }
}

/// Visibility (ADR 0019): the program language sees its own module
/// plus the `pub` items of modules it directly imports (a `use` list
/// restricts further); the proof layer (ghost defs, theorems, clause
/// text) sees the whole DAG. Enforced on the per-module parses, before
/// the flat merge erases ownership.
fn enforce_visibility(loading: &Loading) -> Result<(), Diagnostic> {
    use crate::ast::{Expr, ExprKind, Stmt, Ty};
    use std::collections::HashMap;

    // Global item index: name → (owner module, pub).
    let mut items: HashMap<&str, (usize, bool)> = HashMap::new();
    let mut consts: HashMap<&str, (usize, bool)> = HashMap::new();
    for (idx, p) in &loading.programs {
        for f in &p.fns {
            items.entry(f.name.as_str()).or_insert((*idx, f.is_pub));
        }
        for c in &p.classes {
            items.entry(c.name.as_str()).or_insert((*idx, c.is_pub));
        }
        for t in &p.traits {
            items.entry(t.name.as_str()).or_insert((*idx, t.is_pub));
        }
        for c in &p.consts {
            consts.entry(c.name.as_str()).or_insert((*idx, c.is_pub));
            items.entry(c.name.as_str()).or_insert((*idx, c.is_pub));
        }
    }

    let module_name = |idx: usize| -> String {
        let m = &loading.set.modules[idx];
        Path::new(&m.display)
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| m.display.clone())
    };

    // May module `from` reference `name`?
    let check = |from: usize, name: &str, span: Span| -> Result<(), Diagnostic> {
        let Some(&(owner, is_pub)) = items.get(name) else {
            return Ok(()); // unknown names are the checker's diagnostics
        };
        if owner == from {
            return Ok(());
        }
        if !is_pub {
            return Err(Diagnostic {
                name: "module.private".into(),
                title: format!("`{name}` is private to module `{}`", module_name(owner)),
                span,
                label: "not exported".into(),
                notes: vec![(
                    "note".into(),
                    format!(
                        "mark it `pub` in {} to export it",
                        loading.set.modules[owner].display
                    ),
                )],
            });
        }
        let edge = loading
            .imports
            .iter()
            .find(|(f, _, dep)| *f == from && *dep == owner);
        match edge {
            None => Err(Diagnostic {
                name: "module.not_imported".into(),
                title: format!(
                    "`{name}` is in module `{}`, which this module does not import",
                    module_name(owner)
                ),
                span,
                label: "no direct `use` for its module".into(),
                notes: vec![(
                    "note".into(),
                    format!(
                        "the program language sees direct imports only; add `use {};`",
                        module_name(owner)
                    ),
                )],
            }),
            Some((_, u, _)) => match &u.names {
                None => Ok(()),
                Some(list) if list.iter().any(|n| n == name) => Ok(()),
                Some(_) => Err(Diagnostic {
                    name: "module.not_imported".into(),
                    title: format!(
                        "`{name}` is not in this module's `use {}::{{…}}` list",
                        module_name(owner)
                    ),
                    span,
                    label: "not imported by the list".into(),
                    notes: vec![(
                        "note".into(),
                        "a listed import is restrictive: add the name to the list, \
                         or import the module wholesale"
                            .into(),
                    )],
                }),
            },
        }
    };

    fn walk_expr(
        e: &Expr,
        refs: &mut Vec<(String, Span)>,
        const_names: &HashMap<&str, (usize, bool)>,
    ) {
        match &e.kind {
            ExprKind::Call {
                callee,
                callee_span,
                args,
                ..
            } => {
                refs.push((callee.clone(), *callee_span));
                for a in args {
                    walk_expr(a, refs, const_names);
                }
            }
            ExprKind::CtorCall {
                class,
                class_span,
                args,
                ..
            } => {
                refs.push((class.clone(), *class_span));
                for a in args {
                    walk_expr(a, refs, const_names);
                }
            }
            ExprKind::MethodCall { args, .. } | ExprKind::TraitCall { args, .. } => {
                for a in args {
                    walk_expr(a, refs, const_names);
                }
            }
            ExprKind::Var(name) => {
                // Bare tokens are how consts are referenced (the const
                // pass substitutes them); only const names count.
                if const_names.contains_key(name.as_str()) {
                    refs.push((name.clone(), e.span));
                }
            }
            ExprKind::Unary { operand, .. } => walk_expr(operand, refs, const_names),
            ExprKind::Binary { lhs, rhs, .. } => {
                walk_expr(lhs, refs, const_names);
                walk_expr(rhs, refs, const_names);
            }
            ExprKind::Index { index, .. }
            | ExprKind::ClassFieldIndex { index, .. }
            | ExprKind::SelfFieldIndex { index, .. } => walk_expr(index, refs, const_names),
            ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => {
                walk_expr(arg, refs, const_names)
            }
            ExprKind::IsSome { operand } | ExprKind::OptValue { operand } => {
                walk_expr(operand, refs, const_names)
            }
            ExprKind::SomeE(inner) => walk_expr(inner, refs, const_names),
            ExprKind::ArrayLit(elems) => {
                for el in elems {
                    walk_expr(el, refs, const_names);
                }
            }
            ExprKind::AllocArray { len, init, .. } => {
                walk_expr(len, refs, const_names);
                walk_expr(init, refs, const_names);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::Borrow { .. }
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::ClassFieldLen { .. } => {}
        }
    }

    fn walk_stmts(
        stmts: &[Stmt],
        refs: &mut Vec<(String, Span)>,
        const_names: &HashMap<&str, (usize, bool)>,
    ) {
        for s in stmts {
            match s {
                Stmt::Decl { init, .. } => {
                    if let Some(e) = init {
                        walk_expr(e, refs, const_names);
                    }
                }
                Stmt::Assign { value, .. } => walk_expr(value, refs, const_names),
                Stmt::VarDecl { init, .. } => walk_expr(init, refs, const_names),
                Stmt::ExprStmt(e) => walk_expr(e, refs, const_names),
                Stmt::FieldAssign { value, .. } => walk_expr(value, refs, const_names),
                Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                    walk_expr(index, refs, const_names);
                    walk_expr(value, refs, const_names);
                }
                Stmt::Return { value, .. } => {
                    if let Some(e) = value {
                        walk_expr(e, refs, const_names);
                    }
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    walk_expr(cond, refs, const_names);
                    walk_stmts(then_block, refs, const_names);
                    if let Some(eb) = else_block {
                        walk_stmts(eb, refs, const_names);
                    }
                }
                Stmt::While { cond, body, .. } => {
                    walk_expr(cond, refs, const_names);
                    walk_stmts(body, refs, const_names);
                }
                Stmt::Assert(_) => {}
            }
        }
    }

    for (idx, p) in &loading.programs {
        let externs: &[String] = loading
            .externs
            .iter()
            .find(|(i, _)| i == idx)
            .map(|(_, e)| e.as_slice())
            .unwrap_or(&[]);
        let mut refs: Vec<(String, Span)> = Vec::new();

        let mut walk_fn = |f: &crate::ast::Fn, refs: &mut Vec<(String, Span)>| {
            walk_stmts(&f.body, refs, &consts);
            for (ty, span) in f
                .params
                .iter()
                .map(|pa| (&pa.ty, pa.span))
                .chain(std::iter::once((&f.ret, f.name_span)))
            {
                if let Ty::Class(ci) | Ty::ClassRef(ci) = ty {
                    if let Some(name) = externs.get(*ci) {
                        refs.push((name.clone(), span));
                    }
                }
            }
            for b in f.type_bounds.iter().flatten() {
                refs.push((b.clone(), f.name_span));
            }
        };

        for f in &p.fns {
            walk_fn(f, &mut refs);
        }
        for c in &p.classes {
            for i in &c.inits {
                walk_fn(i, &mut refs);
            }
            for m in &c.methods {
                walk_fn(&m.f, &mut refs);
            }
            if let Some(d) = &c.deinit {
                walk_stmts(d, &mut refs, &consts);
            }
            for fi in &c.fields {
                if let Ty::Class(ci) | Ty::ClassRef(ci) = fi.ty {
                    if let Some(name) = externs.get(ci) {
                        refs.push((name.clone(), fi.span));
                    }
                }
            }
            for b in c.type_bounds.iter().flatten() {
                refs.push((b.clone(), c.name_span));
            }
        }
        for im in &p.impls {
            refs.push((im.trait_name.clone(), im.trait_span));
            for f in &im.fns {
                walk_fn(f, &mut refs);
            }
        }
        for ob in &p.operators {
            refs.push((ob.fn_name.clone(), ob.span));
        }
        // A listed `use` may only name exports.
        for (from, u, dep) in &loading.imports {
            if from == idx {
                if let Some(list) = &u.names {
                    for n in list {
                        if let Some(&(owner, is_pub)) = items.get(n.as_str()) {
                            if owner == *dep && !is_pub {
                                return Err(Diagnostic {
                                    name: "module.private".into(),
                                    title: format!(
                                        "`{n}` is private to module `{}`",
                                        module_name(*dep)
                                    ),
                                    span: u.span,
                                    label: "listed, but not exported".into(),
                                    notes: vec![(
                                        "note".into(),
                                        format!(
                                            "mark it `pub` in {} to export it",
                                            loading.set.modules[*dep].display
                                        ),
                                    )],
                                });
                            }
                        }
                    }
                }
            }
        }

        for (name, span) in refs {
            check(*idx, &name, span)?;
        }
    }
    Ok(())
}

fn load_file(
    loading: &mut Loading,
    path: &Path,
    requested_at: Option<Span>,
) -> Result<usize, Diagnostic> {
    let canonical = path.canonicalize().map_err(|err| Diagnostic {
        name: "module.not_found".into(),
        title: format!("cannot read module `{}`: {err}", path.display()),
        span: requested_at.unwrap_or(Span::new(0, 0)),
        label: "no such file".into(),
        notes: vec![],
    })?;
    // Order matters: a module still on the DFS stack is also in `seen`,
    // so the cycle check must come first.
    if loading.stack.contains(&canonical) {
        return Err(Diagnostic {
            name: "module.cycle".into(),
            title: format!("import cycle through `{}`", path.display()),
            span: requested_at.unwrap_or(Span::new(0, 0)),
            label: "modules form a cycle".into(),
            notes: vec![("note".into(), "imports must form a DAG".into())],
        });
    }
    if let Some((_, idx)) = loading.seen.iter().find(|(p, _)| *p == canonical) {
        return Ok(*idx);
    }
    let source = std::fs::read_to_string(&canonical).map_err(|err| Diagnostic {
        name: "module.not_found".into(),
        title: format!("cannot read module `{}`: {err}", path.display()),
        span: requested_at.unwrap_or(Span::new(0, 0)),
        label: "unreadable".into(),
        notes: vec![],
    })?;

    loading.stack.push(canonical.clone());
    let base = loading.set.combined_source.len();
    loading.set.combined_source.push_str(&source);
    let display = path.display().to_string();
    let idx = loading.set.modules.len();
    loading.set.modules.push(ModuleInfo {
        display,
        path: canonical.clone(),
        base,
        len: source.len(),
        lines: LineMap::new(&source),
        source: source.clone(),
    });
    loading.seen.push((canonical.clone(), idx));

    // Scan/lex per module, then shift into combined coordinates. The
    // parser needs line numbers consistent with the shifted block lines,
    // so it gets a line map over the combined prefix.
    let mut scanned = scan::scan(&source);
    let line_base = loading.set.combined_source[..base]
        .bytes()
        .filter(|b| *b == b'\n')
        .count();
    for block in &mut scanned.blocks {
        block.first_line += line_base;
        block.last_line += line_base;
        block.span = shift(block.span, base);
        for c in &mut block.clauses {
            c.span = shift(c.span, base);
            c.line_span = shift(c.line_span, base);
        }
    }
    let mut tokens = lexer::lex(&scanned.program_text).map_err(|mut d| {
        d.span = shift(d.span, base);
        d
    })?;
    for t in &mut tokens {
        t.span = shift(t.span, base);
    }

    // Imports load before this module parses: imported class names must
    // be known (with their merged indices) when this module's class
    // references resolve. `use` declarations are read off the token
    // stream directly.
    let dir = canonical
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let uses = scan_uses(&tokens);
    for u in &uses {
        let mut candidates = vec![dir.join(format!("{}.sable", u.module))];
        for mp in &loading.module_paths {
            candidates.push(mp.join(format!("{}.sable", u.module)));
        }
        let Some(found) = candidates.iter().find(|c| c.is_file()) else {
            return Err(Diagnostic {
                name: "module.not_found".into(),
                title: format!("no module `{}` on the module path", u.module),
                span: u.span,
                label: "not found".into(),
                notes: vec![(
                    "note".into(),
                    format!(
                        "searched {} (add directories with `-M`)",
                        candidates
                            .iter()
                            .map(|c| c.display().to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )],
            });
        };
        let dep_idx = load_file(loading, found, Some(u.span))?;
        loading.imports.push((idx, u.clone(), dep_idx));
        // Listed imports validate the names exist in the target module.
        if let Some(names) = &u.names {
            let (_, dep) = loading
                .programs
                .iter()
                .find(|(i, _)| *i == dep_idx)
                .expect("loaded");
            for n in names {
                let known = dep.fns.iter().any(|f| f.name == *n)
                    || dep.fn_templates.iter().any(|f| f.name == *n)
                    || dep.classes.iter().any(|c| c.name == *n)
                    || dep.class_templates.iter().any(|c| c.name == *n)
                    || dep.traits.iter().any(|t| t.name == *n);
                if !known {
                    return Err(Diagnostic {
                        name: "module.unknown_name".into(),
                        title: format!("module `{}` has no `{n}`", u.module),
                        span: u.span,
                        label: "not declared there".into(),
                        notes: vec![],
                    });
                }
            }
        }
    }

    // Dependencies are parsed; their classes (in merge order) seed this
    // module's class-index space.
    // Finish order, not load order: a module always finishes after its
    // dependencies, so concatenating classes in finish order puts every
    // module's own classes exactly where its parse assumed they were.
    let extern_classes: Vec<String> = loading
        .programs
        .iter()
        .flat_map(|(_, p)| p.classes.iter().map(|c| c.name.clone()))
        .collect();
    // The combined program text mirrors the combined source (same
    // lengths, proof lines blanked).
    loading.externs.push((idx, extern_classes.clone()));
    let combined_program: String = {
        let mut buf = String::new();
        for m in &loading.set.modules {
            buf.push_str(&scan::scan(&m.source).program_text);
        }
        buf
    };
    let combined_lines = LineMap::new(&loading.set.combined_source);
    let program = parser::parse_module(
        &tokens,
        &scanned.blocks,
        &combined_lines,
        &combined_program,
        &extern_classes,
    )?;
    loading.programs.push((idx, program));
    loading.stack.pop();
    Ok(idx)
}

/// Read the `use` declarations off a token stream (they may appear at
/// any top-level position; the full parse re-reads them into the AST).
fn scan_uses(tokens: &[crate::lexer::Token]) -> Vec<UseDecl> {
    use crate::lexer::Tok;
    let mut uses = Vec::new();
    let mut i = 0;
    let mut depth = 0usize;
    while i < tokens.len() {
        match &tokens[i].tok {
            Tok::LBrace => depth += 1,
            Tok::RBrace => depth = depth.saturating_sub(1),
            Tok::Ident(n) if n == "use" && depth == 0 => {
                let start = tokens[i].span;
                if let Some(Tok::Ident(m)) = tokens.get(i + 1).map(|t| &t.tok) {
                    let module = m.clone();
                    let mut j = i + 2;
                    let mut names = None;
                    if tokens.get(j).map(|t| &t.tok) == Some(&Tok::ColonColon) {
                        j += 1;
                        if tokens.get(j).map(|t| &t.tok) == Some(&Tok::LBrace) {
                            j += 1;
                            let mut listed = Vec::new();
                            while let Some(Tok::Ident(n)) = tokens.get(j).map(|t| &t.tok) {
                                listed.push(n.clone());
                                j += 1;
                                if tokens.get(j).map(|t| &t.tok) == Some(&Tok::Comma) {
                                    j += 1;
                                }
                            }
                            if tokens.get(j).map(|t| &t.tok) == Some(&Tok::RBrace) {
                                j += 1;
                            }
                            names = Some(listed);
                        }
                    }
                    let end = tokens.get(j).map(|t| t.span).unwrap_or(start);
                    uses.push(UseDecl {
                        module,
                        names,
                        span: start.join(end),
                    });
                    i = j;
                }
            }
            _ => {}
        }
        i += 1;
    }
    uses
}

fn shift(s: Span, base: usize) -> Span {
    Span::new(s.start + base, s.end + base)
}

/// Flat merge, in **finish order**. Class-index consistency requires the
/// same order each parse saw as `extern_classes`: the classes of every
/// module that had already finished, concatenated in finish order, with
/// the module's own classes appended when it finishes. Since a module
/// always finishes after its dependencies, merging in finish order
/// reproduces every module's view simultaneously. (Load order will not
/// do: the root is loaded first and finishes last.)
fn merge(loading: Loading) -> Result<(Program, ModuleSet), (Diagnostic, ModuleSet)> {
    let programs = loading.programs;
    let mut it = programs.into_iter();
    let (_, mut merged) = it.next().expect("root loaded");
    for (_, p) in it {
        for f in &p.fns {
            if merged.fns.iter().any(|g| g.name == f.name) {
                return Err((collision("function", &f.name, f.name_span), loading.set));
            }
        }
        for c in &p.classes {
            if merged.classes.iter().any(|d| d.name == c.name) {
                return Err((collision("class", &c.name, c.name_span), loading.set));
            }
        }
        merged.fns.extend(p.fns);
        merged.fn_templates.extend(p.fn_templates);
        merged.class_templates.extend(p.class_templates);
        merged.classes.extend(p.classes);
        merged.traits.extend(p.traits);
        merged.impls.extend(p.impls);
        merged.discharges.extend(p.discharges);
        merged.ghosts.extend(p.ghosts);
        merged.defers.extend(p.defers);
        merged.assumes.extend(p.assumes);
        merged.operators.extend(p.operators);
        merged.consts.extend(p.consts);
    }
    Ok((merged, loading.set))
}

fn collision(what: &str, name: &str, span: Span) -> Diagnostic {
    Diagnostic {
        name: "module.name_collision".into(),
        title: format!("{what} `{name}` is declared in two modules"),
        span,
        label: "second declaration here".into(),
        notes: vec![(
            "note".into(),
            "imports are a flat namespace in v1; rename one of them".into(),
        )],
    }
}

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
use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy)]
enum ItemNamespace {
    Runtime,
    Trait,
    Const,
}

#[derive(Clone, Copy)]
struct ItemDecl<'a> {
    namespace: ItemNamespace,
    kind: &'static str,
    name: &'a str,
    span: Span,
    is_pub: bool,
}

/// Reconstruct declaration order from spans because `Program` stores each
/// declaration category in a separate vector. Functions, classes, and records
/// share the runtime namespace; traits and constants each have their own.
fn item_declarations(program: &Program) -> Vec<ItemDecl<'_>> {
    let mut declarations = Vec::with_capacity(
        program.fns.len()
            + program.fn_templates.len()
            + program.classes.len()
            + program.class_templates.len()
            + program.records.len()
            + program.traits.len()
            + program.consts.len(),
    );
    declarations.extend(
        program
            .fns
            .iter()
            .chain(&program.fn_templates)
            .map(|f| ItemDecl {
                namespace: ItemNamespace::Runtime,
                kind: "function",
                name: f.name.as_str(),
                span: f.name_span,
                is_pub: f.is_pub,
            }),
    );
    declarations.extend(
        program
            .classes
            .iter()
            .chain(&program.class_templates)
            .map(|c| ItemDecl {
                namespace: ItemNamespace::Runtime,
                kind: "class",
                name: c.name.as_str(),
                span: c.name_span,
                is_pub: c.is_pub,
            }),
    );
    declarations.extend(program.records.iter().map(|r| ItemDecl {
        namespace: ItemNamespace::Runtime,
        kind: "record",
        name: r.name.as_str(),
        span: r.name_span,
        is_pub: r.is_pub,
    }));
    declarations.extend(program.traits.iter().map(|trait_| ItemDecl {
        namespace: ItemNamespace::Trait,
        kind: "trait",
        name: trait_.name.as_str(),
        span: trait_.name_span,
        is_pub: trait_.is_pub,
    }));
    declarations.extend(program.consts.iter().map(|constant| ItemDecl {
        namespace: ItemNamespace::Const,
        kind: "constant",
        name: constant.name.as_str(),
        span: constant.name_span,
        is_pub: constant.is_pub,
    }));
    declarations.sort_by_key(|declaration| declaration.span.start);
    declarations
}

/// Whether a module declares `name` in any importable program namespace, and
/// whether at least one such declaration is public. A restrictive import is a
/// name filter, so a public item is importable even if a separate namespace has
/// a private item with the same spelling; an actual reference is checked in its
/// own namespace below.
fn named_item_visibility(program: &Program, name: &str) -> Option<bool> {
    let mut found = false;
    let mut any_public = false;
    for is_public in program
        .fns
        .iter()
        .chain(&program.fn_templates)
        .filter(|f| f.name == name)
        .map(|f| f.is_pub)
        .chain(
            program
                .classes
                .iter()
                .chain(&program.class_templates)
                .filter(|c| c.name == name)
                .map(|c| c.is_pub),
        )
        .chain(
            program
                .records
                .iter()
                .filter(|r| r.name == name)
                .map(|r| r.is_pub),
        )
        .chain(
            program
                .traits
                .iter()
                .filter(|t| t.name == name)
                .map(|t| t.is_pub),
        )
        .chain(
            program
                .consts
                .iter()
                .filter(|c| c.name == name)
                .map(|c| c.is_pub),
        )
    {
        found = true;
        any_public |= is_public;
    }
    found.then_some(any_public)
}

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
    /// Resolved direct import edges `(importer, dependency)`, preserving each
    /// importer's source order. Snapshot consumers use these canonical
    /// identities to distinguish equal source sets wired into different
    /// module graphs.
    pub import_edges: Vec<(usize, usize)>,
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
            import_edges: Vec::new(),
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
    /// Parallel merged-index table for explicitly laid-out records.
    record_externs: Vec<(usize, Vec<String>)>,
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
            import_edges: Vec::new(),
        },
        programs: Vec::new(),
        seen: Vec::new(),
        stack: Vec::new(),
        module_paths: module_paths.to_vec(),
        imports: Vec::new(),
        externs: Vec::new(),
        record_externs: Vec::new(),
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
    if let Some(d) = first_name_collision(&loading) {
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
    use crate::ast::{
        AffineOptionTy, Expr, ExprKind, GenericTy, RawOp, ResKind, Stmt, Ty, TypeArg, ValueTy,
    };

    // Each legal source namespace gets its own global index. Runtime items
    // deliberately share one table; traits and constants do not participate
    // in runtime-name resolution or runtime collision checks.
    let mut runtime_items: HashMap<&str, (usize, bool)> = HashMap::new();
    let mut trait_items: HashMap<&str, (usize, bool)> = HashMap::new();
    let mut consts: HashMap<&str, (usize, bool)> = HashMap::new();
    for (idx, p) in &loading.programs {
        for declaration in item_declarations(p) {
            let items = match declaration.namespace {
                ItemNamespace::Runtime => &mut runtime_items,
                ItemNamespace::Trait => &mut trait_items,
                ItemNamespace::Const => &mut consts,
            };
            items
                .entry(declaration.name)
                .or_insert((*idx, declaration.is_pub));
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
    let check =
        |from: usize, namespace: ItemNamespace, name: &str, span: Span| -> Result<(), Diagnostic> {
            let items = match namespace {
                ItemNamespace::Runtime => &runtime_items,
                ItemNamespace::Trait => &trait_items,
                ItemNamespace::Const => &consts,
            };
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

    fn walk_type_args(type_args: &[TypeArg], refs: &mut Vec<(ItemNamespace, String, Span)>) {
        fn walk_type(ty: &GenericTy, span: Span, refs: &mut Vec<(ItemNamespace, String, Span)>) {
            match ty {
                GenericTy::Record(name) => {
                    refs.push((ItemNamespace::Runtime, name.clone(), span));
                }
                GenericTy::Class { name, args } => {
                    refs.push((ItemNamespace::Runtime, name.clone(), span));
                    for argument in args {
                        walk_type(argument, span, refs);
                    }
                }
                GenericTy::Array(element) | GenericTy::Option(element) => {
                    walk_type(element, span, refs);
                }
                GenericTy::Int(_) | GenericTy::Param(_) | GenericTy::Bool => {}
            }
        }

        for argument in type_args {
            walk_type(&argument.ty, argument.span, refs);
        }
    }

    fn push_record_ref(
        index: usize,
        span: Span,
        record_externs: &[String],
        refs: &mut Vec<(ItemNamespace, String, Span)>,
    ) {
        if let Some(name) = record_externs.get(index) {
            refs.push((ItemNamespace::Runtime, name.clone(), span));
        }
    }

    /// Collect every nominal reference carried by a storable aggregate
    /// payload. Keeping this match exhaustive prevents a newly represented
    /// payload kind from silently bypassing module visibility.
    fn walk_value_ty(
        ty: &ValueTy,
        span: Span,
        record_externs: &[String],
        refs: &mut Vec<(ItemNamespace, String, Span)>,
    ) {
        match ty {
            ValueTy::Record(index) => push_record_ref(*index, span, record_externs, refs),
            ValueTy::Int(_) | ValueTy::Bool | ValueTy::Param(_) => {}
        }
    }

    /// Collect every nominal reference carried by a checked `Ty`. Keeping the
    /// match exhaustive makes a new type form a visibility-pass compile error
    /// rather than an accidental bypass.
    fn walk_ty(
        ty: &Ty,
        span: Span,
        externs: &[String],
        record_externs: &[String],
        refs: &mut Vec<(ItemNamespace, String, Span)>,
    ) {
        match ty {
            Ty::Class(index) | Ty::ClassRef(index, _) => {
                if let Some(name) = externs.get(*index) {
                    refs.push((ItemNamespace::Runtime, name.clone(), span));
                }
            }
            Ty::Record(index) | Ty::RawRecord(index) | Ty::OptionRaw(index) => {
                push_record_ref(*index, span, record_externs, refs);
            }
            Ty::Res(kind) | Ty::ResRef(kind, _) => {
                let record = match kind {
                    ResKind::PointsToRecord(index) | ResKind::ResourceMapPointsToRecord(index) => {
                        Some(*index)
                    }
                    ResKind::RawSpan
                    | ResKind::PointsToU64
                    | ResKind::OpenFile
                    | ResKind::PosixWorld
                    | ResKind::Uart
                    | ResKind::SystemDealloc
                    | ResKind::AllocatorState
                    | ResKind::BlockLease
                    | ResKind::LeasedPointsToU64
                    | ResKind::FreeBlock
                    | ResKind::FreeHeader
                    | ResKind::ResourceMapPointsToU64 => None,
                };
                if let Some(index) = record {
                    push_record_ref(index, span, record_externs, refs);
                }
            }
            Ty::Array(element, _) | Ty::Option(element) => {
                walk_value_ty(element, span, record_externs, refs)
            }
            Ty::AffineOption(AffineOptionTy::Array(element)) => {
                walk_value_ty(element, span, record_externs, refs)
            }
            Ty::Int(_) | Ty::Param(_) | Ty::Bool | Ty::Raw(_) | Ty::Unit => {}
        }
    }

    /// Return the nominal record tag carried by a typed raw operation. This is
    /// deliberately exhaustive for the same fail-closed reason as `walk_ty`.
    fn raw_op_record_index(op: RawOp) -> Option<usize> {
        match op {
            RawOp::IntoCellRecord(index)
            | RawOp::FromCellRecord(index)
            | RawOp::CellInitRecord(index)
            | RawOp::CellReadRecord(index)
            | RawOp::CellTakeRecord(index)
            | RawOp::CellDropRecord(index)
            | RawOp::CastRecord(index)
            | RawOp::PointerOffsetRecord(index) => Some(index),
            RawOp::Offset
            | RawOp::Load8
            | RawOp::Store8
            | RawOp::Copy
            | RawOp::IntoCellU64
            | RawOp::FromCellU64
            | RawOp::CellInitU64
            | RawOp::CellReadU64
            | RawOp::CellTakeU64
            | RawOp::CellDropU64
            | RawOp::IntoFreeHeader
            | RawOp::FromFreeHeader
            | RawOp::HeaderInit
            | RawOp::HeaderSize
            | RawOp::HeaderNext
            | RawOp::HeaderClear => None,
        }
    }

    fn walk_expr(
        e: &Expr,
        refs: &mut Vec<(ItemNamespace, String, Span)>,
        const_names: &HashMap<&str, (usize, bool)>,
        record_externs: &[String],
    ) {
        match &e.kind {
            ExprKind::ResOp { args, .. } | ExprKind::DeviceOp { args, .. } => {
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::RawOp { op, op_span, args } => {
                if let Some(index) = raw_op_record_index(*op) {
                    push_record_ref(index, *op_span, record_externs, refs);
                }
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::Call {
                callee,
                callee_span,
                type_args,
                args,
            } => {
                refs.push((ItemNamespace::Runtime, callee.clone(), *callee_span));
                walk_type_args(type_args, refs);
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::CtorCall {
                class,
                class_span,
                type_args,
                args,
                ..
            } => {
                refs.push((ItemNamespace::Runtime, class.clone(), *class_span));
                walk_type_args(type_args, refs);
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::RecordLit {
                record,
                record_span,
                args,
            } => {
                refs.push((ItemNamespace::Runtime, record.clone(), *record_span));
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::MethodCall { args, .. } | ExprKind::TraitCall { args, .. } => {
                for a in args {
                    walk_expr(a, refs, const_names, record_externs);
                }
            }
            ExprKind::Var(name) => {
                // Bare tokens are how consts are referenced (the const
                // pass substitutes them); only const names count.
                if const_names.contains_key(name.as_str()) {
                    refs.push((ItemNamespace::Const, name.clone(), e.span));
                }
            }
            ExprKind::Unary { operand, .. } => {
                walk_expr(operand, refs, const_names, record_externs)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                walk_expr(lhs, refs, const_names, record_externs);
                walk_expr(rhs, refs, const_names, record_externs);
            }
            ExprKind::Index { index, .. }
            | ExprKind::ClassFieldIndex { index, .. }
            | ExprKind::SelfFieldIndex { index, .. } => {
                walk_expr(index, refs, const_names, record_externs)
            }
            ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => {
                walk_expr(arg, refs, const_names, record_externs)
            }
            ExprKind::IsSome { operand } | ExprKind::OptValue { operand } => {
                walk_expr(operand, refs, const_names, record_externs)
            }
            ExprKind::OptTake { .. } => {}
            ExprKind::SomeE(inner) => walk_expr(inner, refs, const_names, record_externs),
            ExprKind::ArrayLit(elems) => {
                for el in elems {
                    walk_expr(el, refs, const_names, record_externs);
                }
            }
            ExprKind::AllocArray { elem, len, init } => {
                walk_value_ty(elem, e.span, record_externs, refs);
                walk_expr(len, refs, const_names, record_externs);
                walk_expr(init, refs, const_names, record_externs);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::Borrow { .. }
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. } => {}
        }
    }

    fn walk_stmts(
        stmts: &[Stmt],
        refs: &mut Vec<(ItemNamespace, String, Span)>,
        const_names: &HashMap<&str, (usize, bool)>,
        externs: &[String],
        record_externs: &[String],
    ) {
        for s in stmts {
            match s {
                Stmt::Decl {
                    ty,
                    name_span,
                    init,
                    ..
                } => {
                    walk_ty(ty, *name_span, externs, record_externs, refs);
                    if let Some(e) = init {
                        walk_expr(e, refs, const_names, record_externs);
                    }
                }
                Stmt::Assign { value, .. } => walk_expr(value, refs, const_names, record_externs),
                Stmt::VarDecl {
                    init,
                    ty,
                    name_span,
                    ..
                } => {
                    if let Some(ty) = ty {
                        walk_ty(ty, *name_span, externs, record_externs, refs);
                    }
                    walk_expr(init, refs, const_names, record_externs);
                }
                Stmt::ExprStmt(e) => walk_expr(e, refs, const_names, record_externs),
                Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                    walk_expr(size, refs, const_names, record_externs)
                }
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    walk_expr(ptr, refs, const_names, record_externs);
                    walk_expr(res, refs, const_names, record_externs);
                    walk_expr(release, refs, const_names, record_externs);
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                    walk_stmts(body, refs, const_names, externs, record_externs)
                }
                Stmt::FieldAssign { value, .. } => {
                    walk_expr(value, refs, const_names, record_externs)
                }
                Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                    walk_expr(index, refs, const_names, record_externs);
                    walk_expr(value, refs, const_names, record_externs);
                }
                Stmt::Return { value, .. } => {
                    if let Some(e) = value {
                        walk_expr(e, refs, const_names, record_externs);
                    }
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    walk_expr(cond, refs, const_names, record_externs);
                    walk_stmts(then_block, refs, const_names, externs, record_externs);
                    if let Some(eb) = else_block {
                        walk_stmts(eb, refs, const_names, externs, record_externs);
                    }
                }
                Stmt::While { cond, body, .. } => {
                    walk_expr(cond, refs, const_names, record_externs);
                    walk_stmts(body, refs, const_names, externs, record_externs);
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
        let record_externs: &[String] = loading
            .record_externs
            .iter()
            .find(|(i, _)| i == idx)
            .map(|(_, e)| e.as_slice())
            .unwrap_or(&[]);
        let mut refs: Vec<(ItemNamespace, String, Span)> = Vec::new();

        let walk_fn = |f: &crate::ast::Fn, refs: &mut Vec<(ItemNamespace, String, Span)>| {
            walk_stmts(&f.body, refs, &consts, externs, record_externs);
            for (ty, span) in f
                .params
                .iter()
                .map(|pa| (&pa.ty, pa.span))
                .chain(std::iter::once((&f.ret, f.name_span)))
            {
                walk_ty(ty, span, externs, record_externs, refs);
            }
            for b in f.type_bounds.iter().flatten() {
                refs.push((ItemNamespace::Trait, b.clone(), f.name_span));
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
                walk_stmts(d, &mut refs, &consts, externs, record_externs);
            }
            for fi in &c.fields {
                walk_ty(&fi.ty, fi.span, externs, record_externs, &mut refs);
            }
            for b in c.type_bounds.iter().flatten() {
                refs.push((ItemNamespace::Trait, b.clone(), c.name_span));
            }
        }
        for r in &p.records {
            for fi in &r.fields {
                walk_ty(&fi.ty, fi.span, externs, record_externs, &mut refs);
            }
        }
        for trait_ in &p.traits {
            for method in &trait_.methods {
                walk_fn(method, &mut refs);
            }
        }
        for im in &p.impls {
            refs.push((ItemNamespace::Trait, im.trait_name.clone(), im.trait_span));
            for f in &im.fns {
                walk_fn(f, &mut refs);
            }
        }
        for ob in &p.operators {
            refs.push((ItemNamespace::Runtime, ob.fn_name.clone(), ob.span));
        }
        // A listed `use` may only name exports.
        for (from, u, dep) in &loading.imports {
            if from == idx {
                if let Some(list) = &u.names {
                    for n in list {
                        let (_, dep_program) = loading
                            .programs
                            .iter()
                            .find(|(candidate, _)| candidate == dep)
                            .expect("import target is loaded");
                        if named_item_visibility(dep_program, n) == Some(false) {
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

        for (namespace, name, span) in refs {
            check(*idx, namespace, &name, span)?;
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
        loading.set.import_edges.push((idx, dep_idx));
        // Listed imports validate the names exist in the target module.
        if let Some(names) = &u.names {
            let (_, dep) = loading
                .programs
                .iter()
                .find(|(i, _)| *i == dep_idx)
                .expect("loaded");
            for n in names {
                if named_item_visibility(dep, n).is_none() {
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

    // Dependencies are parsed; their non-generic classes (in merge order)
    // seed this module's checked class-index space. Generic templates travel
    // in the separate name/arity table below and acquire no checked index.
    // Finish order, not load order: a module always finishes after its
    // dependencies, so concatenating classes in finish order puts every
    // module's own classes exactly where its parse assumed they were.
    let extern_classes: Vec<String> = loading
        .programs
        .iter()
        .flat_map(|(_, p)| {
            p.classes
                .iter()
                .filter(|c| c.type_params.is_empty())
                .map(|c| c.name.clone())
        })
        .collect();
    let extern_generic_classes: Vec<(String, usize)> = loading
        .programs
        .iter()
        .flat_map(|(_, p)| {
            p.classes
                .iter()
                .filter(|c| !c.type_params.is_empty())
                .chain(p.class_templates.iter())
                .map(|c| (c.name.clone(), c.type_params.len()))
        })
        .collect();
    let extern_records: Vec<String> = loading
        .programs
        .iter()
        .flat_map(|(_, p)| p.records.iter().map(|r| r.name.clone()))
        .collect();
    // The combined program text mirrors the combined source (same
    // lengths, proof lines blanked).
    loading.externs.push((idx, extern_classes.clone()));
    loading.record_externs.push((idx, extern_records.clone()));
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
        &extern_generic_classes,
        &extern_records,
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

/// Report the first cross-module collision within any legal item namespace.
/// This runs before visibility so first-wins owner lookup cannot turn a link
/// error into `module.private`/`module.not_imported`. Module finish order is
/// the merge order; declaration spans restore source order within each module.
fn first_name_collision(loading: &Loading) -> Option<Diagnostic> {
    let mut runtime_owners: HashMap<&str, (usize, &'static str)> = HashMap::new();
    let mut trait_owners: HashMap<&str, (usize, &'static str)> = HashMap::new();
    let mut const_owners: HashMap<&str, (usize, &'static str)> = HashMap::new();
    for (module, program) in &loading.programs {
        for declaration in item_declarations(program) {
            let owners = match declaration.namespace {
                ItemNamespace::Runtime => &mut runtime_owners,
                ItemNamespace::Trait => &mut trait_owners,
                ItemNamespace::Const => &mut const_owners,
            };
            match owners.get(declaration.name) {
                Some(&(owner, first_kind)) if owner != *module => {
                    return Some(collision(
                        declaration.namespace,
                        first_kind,
                        declaration.kind,
                        declaration.name,
                        declaration.span,
                    ));
                }
                Some(_) => {}
                None => {
                    owners.insert(declaration.name, (*module, declaration.kind));
                }
            }
        }
    }
    None
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
                return Err((
                    collision(
                        ItemNamespace::Runtime,
                        "function",
                        "function",
                        &f.name,
                        f.name_span,
                    ),
                    loading.set,
                ));
            }
        }
        for c in &p.classes {
            if merged.classes.iter().any(|d| d.name == c.name) {
                return Err((
                    collision(
                        ItemNamespace::Runtime,
                        "class",
                        "class",
                        &c.name,
                        c.name_span,
                    ),
                    loading.set,
                ));
            }
        }
        for r in &p.records {
            if merged.records.iter().any(|d| d.name == r.name) {
                return Err((
                    collision(
                        ItemNamespace::Runtime,
                        "record",
                        "record",
                        &r.name,
                        r.name_span,
                    ),
                    loading.set,
                ));
            }
        }
        merged.fns.extend(p.fns);
        merged.fn_templates.extend(p.fn_templates);
        merged.class_templates.extend(p.class_templates);
        merged.classes.extend(p.classes);
        merged.records.extend(p.records);
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

fn collision(
    namespace: ItemNamespace,
    first_kind: &str,
    second_kind: &str,
    name: &str,
    span: Span,
) -> Diagnostic {
    let title = if first_kind == second_kind {
        format!("{second_kind} `{name}` is declared in two modules")
    } else {
        format!("`{name}` is declared as a {first_kind} and a {second_kind} in two modules")
    };
    let note = match namespace {
        ItemNamespace::Runtime => {
            "functions, classes, and records share one flat runtime namespace in v1; \
             rename one of them"
        }
        ItemNamespace::Trait => {
            "a trait name has one owner in the linked program; rename one declaration"
        }
        ItemNamespace::Const => {
            "a constant name has one owner in the linked program; rename one declaration"
        }
    };
    Diagnostic {
        name: "module.name_collision".into(),
        title,
        span,
        label: "second declaration here".into(),
        notes: vec![("note".into(), note.into())],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AffineOptionTy, ExprKind, Mutability, Stmt, Ty, ValueTy};
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

    struct FixtureDir {
        path: PathBuf,
    }

    impl FixtureDir {
        fn new(files: &[(&str, &str)]) -> FixtureDir {
            let id = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "sable-module-namespace-{}-{id}",
                std::process::id()
            ));
            fs::create_dir(&path).expect("create module fixture directory");
            for (name, source) in files {
                fs::write(path.join(name), source).expect("write module fixture");
            }
            FixtureDir { path }
        }

        fn root(&self) -> PathBuf {
            self.path.join("root.sable")
        }
    }

    impl Drop for FixtureDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn load_error(fixture: &FixtureDir) -> Diagnostic {
        match load(&fixture.root(), &[]) {
            Err((diagnostic, _)) => diagnostic,
            Ok(_) => panic!("module fixture unexpectedly loaded"),
        }
    }

    fn parse_fixture(fixture: &FixtureDir) -> Loading {
        let mut loading = Loading {
            set: ModuleSet {
                modules: Vec::new(),
                combined_source: String::new(),
                import_edges: Vec::new(),
            },
            programs: Vec::new(),
            seen: Vec::new(),
            stack: Vec::new(),
            module_paths: Vec::new(),
            imports: Vec::new(),
            externs: Vec::new(),
            record_externs: Vec::new(),
        };
        if let Err(diagnostic) = load_file(&mut loading, &fixture.root(), None) {
            panic!(
                "module fixture should parse before synthetic mutation:\n{}",
                loading.set.render(&diagnostic)
            );
        }
        loading
    }

    #[derive(Clone, Copy)]
    enum AggregateRecordSite {
        ArrayParameter,
        OptionReturn,
        AffineOptionReturn,
        InferredAffineOptionLocal,
        AllocationElement,
    }

    fn inject_record_payload(loading: &mut Loading, record_name: &str, site: AggregateRecordSite) {
        let root_index = 0;
        let record_index = loading
            .record_externs
            .iter()
            .find(|(module, _)| *module == root_index)
            .and_then(|(_, records)| records.iter().position(|name| name == record_name))
            .expect("record is present in the root module's checked index space");
        let root = loading
            .programs
            .iter_mut()
            .find(|(module, _)| *module == root_index)
            .map(|(_, program)| program)
            .expect("root program is parsed");

        match site {
            AggregateRecordSite::ArrayParameter => {
                let function = root
                    .fns
                    .iter_mut()
                    .find(|function| function.name == "aggregate")
                    .expect("aggregate function exists");
                function.params[0].ty =
                    Ty::Array(ValueTy::Record(record_index), Mutability::Shared);
            }
            AggregateRecordSite::OptionReturn => {
                let function = root
                    .fns
                    .iter_mut()
                    .find(|function| function.name == "aggregate")
                    .expect("aggregate function exists");
                function.ret = Ty::Option(ValueTy::Record(record_index));
            }
            AggregateRecordSite::AffineOptionReturn => {
                let function = root
                    .fns
                    .iter_mut()
                    .find(|function| function.name == "aggregate")
                    .expect("aggregate function exists");
                function.ret =
                    Ty::AffineOption(AffineOptionTy::Array(ValueTy::Record(record_index)));
            }
            AggregateRecordSite::InferredAffineOptionLocal => {
                let function = root
                    .fns
                    .iter_mut()
                    .find(|function| function.name == "allocation")
                    .expect("allocation function exists");
                function.body.push(Stmt::VarDecl {
                    name: "optional".into(),
                    name_span: function.name_span,
                    mutable: false,
                    init: crate::ast::Expr {
                        kind: ExprKind::NoneE,
                        span: function.name_span,
                        ty: None,
                    },
                    ty: Some(Ty::AffineOption(AffineOptionTy::Array(ValueTy::Record(
                        record_index,
                    )))),
                });
            }
            AggregateRecordSite::AllocationElement => {
                let function = root
                    .fns
                    .iter_mut()
                    .find(|function| function.name == "allocation")
                    .expect("allocation function exists");
                let expression = function
                    .body
                    .iter_mut()
                    .find_map(|statement| match statement {
                        Stmt::Decl {
                            init: Some(expression),
                            ..
                        } => Some(expression),
                        _ => None,
                    })
                    .expect("allocation initializer exists");
                let ExprKind::AllocArray { elem, .. } = &mut expression.kind else {
                    panic!("initializer is an array allocation");
                };
                *elem = ValueTy::Record(record_index);
            }
        }
    }

    #[test]
    fn runtime_traits_and_consts_use_separate_visibility_namespaces() {
        let fixture = FixtureDir::new(&[
            (
                "runtime_names.sable",
                "fn shared(u64 value) -> u64 { return value; }\n",
            ),
            ("trait_names.sable", "pub trait shared {}\n"),
            ("const_names.sable", "pub const u64 shared = 7;\n"),
            (
                "root.sable",
                r#"use runtime_names;
use trait_names::{shared};
use const_names::{shared};

fn identity<T: shared>(T value) -> T {
    return value;
}

fn read_shared() -> u64 {
    return shared;
}
"#,
            ),
        ]);

        let (program, _) = load(&fixture.root(), &[]).unwrap_or_else(|(diagnostic, modules)| {
            panic!(
                "module fixture should load:\n{}",
                modules.render(&diagnostic)
            )
        });
        assert!(program.fns.iter().any(|function| function.name == "shared"));
        assert!(program.traits.iter().any(|trait_| trait_.name == "shared"));
        assert!(
            program
                .consts
                .iter()
                .any(|constant| constant.name == "shared")
        );
    }

    #[test]
    fn restrictive_imports_recognize_private_consts_before_visibility() {
        let fixture = FixtureDir::new(&[
            ("values.sable", "const u64 hidden = 7;\n"),
            (
                "root.sable",
                "use values::{hidden};\nfn read_hidden() -> u64 { return hidden; }\n",
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.private");
        assert!(diagnostic.title.contains("hidden"));
    }

    #[test]
    fn recursive_type_arguments_obey_private_visibility() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "record Hidden #[layout(size := 1, align := 1)] {}\n",
            ),
            (
                "root.sable",
                r#"use types;

fn identity<T>(T value) -> T {
    return value;
}

fn read() -> u64 {
    return identity<option<[Hidden]>>(7);
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.private");
        assert!(diagnostic.title.contains("Hidden"));
    }

    #[test]
    fn recursive_type_arguments_require_a_direct_import() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "pub record Shared #[layout(size := 1, align := 1)] {}\n",
            ),
            ("middle.sable", "use types;\n"),
            (
                "root.sable",
                r#"use middle;

fn identity<T>(T value) -> T {
    return value;
}

fn read() -> u64 {
    return identity<option<[Shared]>>(7);
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.not_imported");
        assert!(diagnostic.title.contains("Shared"));
    }

    #[test]
    fn aggregate_record_payloads_obey_private_visibility() {
        for site in [
            AggregateRecordSite::ArrayParameter,
            AggregateRecordSite::OptionReturn,
            AggregateRecordSite::AffineOptionReturn,
            AggregateRecordSite::InferredAffineOptionLocal,
            AggregateRecordSite::AllocationElement,
        ] {
            let fixture = FixtureDir::new(&[
                (
                    "types.sable",
                    "record Hidden #[layout(size := 1, align := 1)] {}\n",
                ),
                (
                    "root.sable",
                    r#"use types;

fn aggregate(&[u64] values) -> option<u64> {
    return none;
}

fn allocation() {
    [u64] values = alloc_array<u64>(1, 0);
}
"#,
                ),
            ]);
            let mut loading = parse_fixture(&fixture);
            inject_record_payload(&mut loading, "Hidden", site);

            let diagnostic = enforce_visibility(&loading)
                .expect_err("synthetic aggregate record payload should be private");
            assert_eq!(diagnostic.name, "module.private");
            assert!(diagnostic.title.contains("Hidden"));
        }
    }

    #[test]
    fn aggregate_record_payloads_require_a_direct_import() {
        for site in [
            AggregateRecordSite::ArrayParameter,
            AggregateRecordSite::OptionReturn,
            AggregateRecordSite::AffineOptionReturn,
            AggregateRecordSite::InferredAffineOptionLocal,
            AggregateRecordSite::AllocationElement,
        ] {
            let fixture = FixtureDir::new(&[
                (
                    "types.sable",
                    "pub record Shared #[layout(size := 1, align := 1)] {}\n",
                ),
                ("middle.sable", "use types;\n"),
                (
                    "root.sable",
                    r#"use middle;

fn aggregate(&[u64] values) -> option<u64> {
    return none;
}

fn allocation() {
    [u64] values = alloc_array<u64>(1, 0);
}
"#,
                ),
            ]);
            let mut loading = parse_fixture(&fixture);
            inject_record_payload(&mut loading, "Shared", site);

            let diagnostic = enforce_visibility(&loading)
                .expect_err("synthetic aggregate record payload should require a direct import");
            assert_eq!(diagnostic.name, "module.not_imported");
            assert!(diagnostic.title.contains("Shared"));
        }
    }

    #[test]
    fn explicit_local_types_obey_private_visibility() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "record Hidden #[layout(size := 1, align := 1)] {}\n",
            ),
            (
                "root.sable",
                r#"use types;

fn declare_hidden() {
    raw<Hidden> pointer;
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.private");
        assert!(diagnostic.title.contains("Hidden"));
    }

    #[test]
    fn explicit_local_types_require_a_direct_import() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "pub record Shared #[layout(size := 1, align := 1)] {}\n",
            ),
            ("middle.sable", "use types;\n"),
            (
                "root.sable",
                r#"use middle;

fn declare_shared() {
    raw<Shared> pointer;
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.not_imported");
        assert!(diagnostic.title.contains("Shared"));
    }

    #[test]
    fn typed_raw_operations_obey_private_visibility() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "record Hidden #[layout(size := 1, align := 1)] {}\n",
            ),
            (
                "root.sable",
                r#"use types;

fn cast_hidden(raw<u8> pointer) -> u64 {
    unsafe {
        raw_cast<Hidden>(pointer);
    }
    return 0;
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.private");
        assert!(diagnostic.title.contains("Hidden"));
    }

    #[test]
    fn typed_raw_operations_require_a_direct_import() {
        let fixture = FixtureDir::new(&[
            (
                "types.sable",
                "pub record Shared #[layout(size := 1, align := 1)] {}\n",
            ),
            ("middle.sable", "use types;\n"),
            (
                "root.sable",
                r#"use middle;

fn cast_shared(raw<u8> pointer) -> u64 {
    unsafe {
        raw_cast<Shared>(pointer);
    }
    return 0;
}
"#,
            ),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.not_imported");
        assert!(diagnostic.title.contains("Shared"));
    }

    #[test]
    fn every_cross_category_runtime_collision_is_a_module_collision() {
        let cases = [
            (
                "fn clash() -> u64 { return 0; }\n",
                "class clash {}\n",
                "function",
                "class",
            ),
            (
                "class clash {}\n",
                "record clash #[layout(size := 1, align := 1)] {}\n",
                "class",
                "record",
            ),
            (
                "record clash #[layout(size := 1, align := 1)] {}\n",
                "fn clash() -> u64 { return 0; }\n",
                "record",
                "function",
            ),
        ];

        for (dependency, root_declaration, first_kind, second_kind) in cases {
            let root = format!("use dependency;\n{root_declaration}");
            let fixture =
                FixtureDir::new(&[("dependency.sable", dependency), ("root.sable", &root)]);
            let diagnostic = load_error(&fixture);
            assert_eq!(diagnostic.name, "module.name_collision");
            assert!(diagnostic.title.contains(first_kind));
            assert!(diagnostic.title.contains(second_kind));
            assert!(diagnostic.title.contains("clash"));
        }
    }

    #[test]
    fn duplicate_traits_and_consts_collide_within_their_own_namespaces() {
        let cases = [
            ("trait duplicate {}\n", "trait duplicate {}\n", "trait"),
            (
                "const u64 duplicate = 1;\n",
                "const u64 duplicate = 2;\n",
                "constant",
            ),
        ];

        for (dependency, root_declaration, kind) in cases {
            let root = format!("use dependency;\n{root_declaration}");
            let fixture =
                FixtureDir::new(&[("dependency.sable", dependency), ("root.sable", &root)]);
            let diagnostic = load_error(&fixture);
            assert_eq!(diagnostic.name, "module.name_collision");
            assert!(diagnostic.title.contains(kind));
            assert!(diagnostic.title.contains("duplicate"));
        }
    }

    #[test]
    fn collision_selection_is_source_ordered_across_item_namespaces() {
        let root = r#"use dependency;

const u64 constant_first = 2;
trait trait_second {}
"#;
        let fixture = FixtureDir::new(&[
            (
                "dependency.sable",
                "trait trait_second {}\nconst u64 constant_first = 1;\n",
            ),
            ("root.sable", root),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.name_collision");
        assert!(diagnostic.title.contains("constant_first"));
        assert!(!diagnostic.title.contains("trait_second"));
        assert_eq!(diagnostic.span.start, root.find("constant_first").unwrap());
    }

    #[test]
    fn runtime_collision_selection_follows_source_order_within_a_module() {
        let root = r#"use dependency;

record beta #[layout(size := 1, align := 1)] {}
class alpha {}
"#;
        let fixture = FixtureDir::new(&[
            (
                "dependency.sable",
                "fn alpha() -> u64 { return 0; }\nfn beta() -> u64 { return 0; }\n",
            ),
            ("root.sable", root),
        ]);

        let diagnostic = load_error(&fixture);
        assert_eq!(diagnostic.name, "module.name_collision");
        assert!(diagnostic.title.contains("beta"));
        assert!(!diagnostic.title.contains("alpha"));
        assert_eq!(diagnostic.span.start, root.find("beta").unwrap());
    }
}

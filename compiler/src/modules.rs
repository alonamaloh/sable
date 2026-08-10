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
    match merge(loading) {
        Ok(ok) => Ok(ok),
        Err((d, set)) => Err((d, set)),
    }
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
    let extern_classes: Vec<String> = {
        let mut order: Vec<usize> = loading.programs.iter().map(|(i, _)| *i).collect();
        order.sort();
        let mut names = Vec::new();
        for i in order {
            let (_, p) = loading
                .programs
                .iter()
                .find(|(j, _)| *j == i)
                .expect("loaded");
            names.extend(p.classes.iter().map(|c| c.name.clone()));
        }
        names
    };
    // The combined program text mirrors the combined source (same
    // lengths, proof lines blanked).
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

/// Flat merge. Class-index consistency requires the same order the
/// parser saw as `extern_classes`: ascending module index among
/// finished dependencies, with each module's own classes appended when
/// it parses — i.e. classes ordered by (finish-set at parse time). The
/// loader finishes dependencies before dependents, and extern order is
/// ascending index over finished programs, so merging in ascending
/// index order over the finished list reproduces it exactly.
fn merge(loading: Loading) -> Result<(Program, ModuleSet), (Diagnostic, ModuleSet)> {
    let mut programs = loading.programs;
    programs.sort_by_key(|(idx, _)| *idx);
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

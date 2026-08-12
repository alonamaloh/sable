//! Lean file generation, invocation, and diagnostic mapping.
//!
//! One generated file per checked .sable file: clause well-formedness defs
//! first (so a clause that fails to elaborate maps to its own span), then
//! one theorem per obligation, proved `by sable_auto`. A source map from
//! generated-file lines back to obligations/clauses turns `lean --json`
//! messages into .sable diagnostics.

use crate::diag::Diagnostic;
use crate::span::Span;
use crate::vcgen::{Obligation, VcResult};
use std::path::{Path, PathBuf};
use std::process::Command;

enum MapTarget {
    Clause {
        span: Span,
        desc: String,
    },
    Obligation(usize),
    /// Theorem proved by a user discharge script; errors point at the
    /// discharge block.
    Discharged {
        name: String,
        span: Span,
        goal: String,
    },
}

struct MapEntry {
    first_line: usize,
    last_line: usize,
    target: MapTarget,
}

/// The Lean-level names a generated module file declares. Importers
/// subtract these sets so a declaration is emitted (and verified) in
/// exactly one file of the import DAG.
#[derive(Default, Clone)]
pub struct EmittedNames {
    /// Structure names (`lean_class_name`).
    pub classes: std::collections::HashSet<String>,
    /// Ghost def/theorem head names.
    pub ghosts: std::collections::HashSet<String>,
    /// Clause well-formedness def names.
    pub wfs: std::collections::HashSet<String>,
    /// Obligation theorem names.
    pub thms: std::collections::HashSet<String>,
    /// Obligation names (escape-hatch ownership checks).
    pub obligations: std::collections::HashSet<String>,
}

impl EmittedNames {
    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
            && self.ghosts.is_empty()
            && self.wfs.is_empty()
            && self.thms.is_empty()
    }
}

pub struct Emitted {
    pub lean_source: String,
    /// What this file declares (after exclusion filtering).
    pub names: EmittedNames,
    map: Vec<MapEntry>,
}

struct Emitter {
    buf: String,
    line: usize,
}

impl Emitter {
    fn push(&mut self, s: &str) {
        for l in s.split('\n') {
            self.buf.push_str(l);
            self.buf.push('\n');
            self.line += 1;
        }
    }
}

/// Emit a module's Lean file. `imports` are generated dependency
/// artifacts (`import <name>` lines after `import Sable`); anything
/// named in `exclude` is declared by one of those imports and is
/// filtered out here — the import supplies it, already verified.
pub fn emit(
    vc: &VcResult,
    discharges: &[crate::ast::Discharge],
    skip: &std::collections::HashSet<String>,
    imports: &[String],
    exclude: &EmittedNames,
) -> Emitted {
    let mut e = Emitter {
        buf: String::new(),
        line: 0,
    };
    let mut map = Vec::new();
    let mut names = EmittedNames::default();

    e.push("import Sable");
    for i in imports {
        e.push(&format!("import {i}"));
    }
    e.push("open Sable");
    e.push("set_option linter.unusedVariables false");
    // Test/CI hook: shrink or disable the grind heartbeat budget
    // without touching source (the option itself lives in the prelude).
    if let Ok(v) = std::env::var("SABLE_GRIND_HEARTBEATS") {
        if v.parse::<u64>().is_ok() {
            e.push(&format!("set_option sable.grindHeartbeats {v}"));
        }
    }
    // The trust manifest, inside the hashed content. Changing an audit id
    // or adding an extern has to invalidate the artifact exactly as
    // changing a proof does, and an artifact's validity is mere existence
    // of its `.ok` file — so this must be part of the bytes, not a file
    // beside them (ADR 0027).
    if !vc.trust.externs.is_empty() {
        e.push("-- trusted boundary: audited extern contracts");
        for (id, reason, name) in &vc.trust.externs {
            e.push(&format!("--   {id} ({name}): {reason}"));
        }
    }
    e.push("");

    for r in &vc.records {
        let lean_name = crate::vcgen::lean_record_name(&r.name);
        if exclude.classes.contains(&lean_name) {
            continue;
        }
        names.classes.insert(lean_name.clone());
        let first = e.line + 1;
        e.push(&format!("structure {lean_name} where"));
        for field in &r.fields {
            e.push(&format!("  {} : {}", field.name, field.lean_ty));
        }
        e.push("");
        e.push(&format!("namespace {lean_name}"));
        e.push(&format!(
            "def layout : Sable.Layout := ⟨{}, {}⟩",
            r.layout.size, r.layout.align
        ));
        e.push(&format!(
            "@[simp] theorem layout_size : layout.size = {} := rfl",
            r.layout.size
        ));
        e.push(&format!(
            "@[simp] theorem layout_align : layout.align = {} := rfl",
            r.layout.align
        ));
        for field in &r.fields {
            e.push(&format!("def {}Offset : Int := {}", field.name, field.offset));
        }
        let mut exponent = 0u32;
        let mut align = r.layout.align;
        while align > 1 {
            align /= 2;
            exponent += 1;
        }
        e.push("theorem layout_wf : layout.wf := by");
        e.push(&format!(
            "  refine ⟨by decide, by decide, ⟨{exponent}, rfl⟩⟩"
        ));
        for field in &r.fields {
            e.push(&format!(
                "theorem {}_fits : Sable.Layout.fieldFits layout {} {}Offset := by simp [Sable.Layout.fieldFits, layout, {}Offset, {}]",
                field.name, field.layout, field.name, field.name, field.layout
            ));
        }
        for left in 0..r.fields.len() {
            for right in (left + 1)..r.fields.len() {
                let lfield = &r.fields[left];
                let rfield = &r.fields[right];
                e.push(&format!(
                    "theorem {}_{}_disjoint : Sable.Layout.fieldsDisjoint {} {}Offset {} {}Offset := by simp [Sable.Layout.fieldsDisjoint, {}Offset, {}Offset, {}, {}]",
                    lfield.name,
                    rfield.name,
                    lfield.layout,
                    lfield.name,
                    rfield.layout,
                    rfield.name,
                    lfield.name,
                    rfield.name,
                    lfield.layout,
                    rfield.layout
                ));
            }
        }
        let value_wf: Vec<&str> = r.fields.iter().filter_map(|f| f.wf.as_deref()).collect();
        e.push(&format!("def wf (value : {lean_name}) : Prop :="));
        e.push(&format!(
            "  {}",
            if value_wf.is_empty() {
                "True".to_string()
            } else {
                value_wf.join(" ∧ ")
            }
        ));
        e.push(&format!(
            "def cellWf (cell : Sable.PointsToView {lean_name}) : Prop :="
        ));
        e.push("  cell.layout = layout ∧ 0 ≤ cell.off ∧ cell.off % cell.layout.align = 0 ∧");
        e.push("    match cell.state with | .uninit => True | .init value => wf value");
        e.push(&format!(
            "def fromSpan (span : Sable.SpanView) : Sable.PointsToView {lean_name} :="
        ));
        e.push("  { alloc := span.alloc, off := span.off, layout := layout, state := .uninit }");
        e.push("@[simp] theorem fromSpan_alloc (span : Sable.SpanView) : (fromSpan span).alloc = span.alloc := rfl");
        e.push("@[simp] theorem fromSpan_off (span : Sable.SpanView) : (fromSpan span).off = span.off := rfl");
        e.push("@[simp] theorem fromSpan_layout (span : Sable.SpanView) : (fromSpan span).layout = layout := rfl");
        e.push("@[simp] theorem fromSpan_state (span : Sable.SpanView) : (fromSpan span).state = .uninit := rfl");
        e.push(&format!(
            "def toSpan (cell : Sable.PointsToView {lean_name}) : Sable.SpanView :="
        ));
        e.push("  { alloc := cell.alloc, off := cell.off, len := cell.layout.size,");
        e.push("    bytes := ⟨cell.layout.size, fun _ => .init 0⟩ }");
        e.push(&format!("@[simp] theorem toSpan_alloc (cell : Sable.PointsToView {lean_name}) : (toSpan cell).alloc = cell.alloc := rfl"));
        e.push(&format!("@[simp] theorem toSpan_off (cell : Sable.PointsToView {lean_name}) : (toSpan cell).off = cell.off := rfl"));
        e.push(&format!("@[simp] theorem toSpan_len (cell : Sable.PointsToView {lean_name}) : (toSpan cell).len = cell.layout.size := rfl"));
        e.push(&format!("end {lean_name}"));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: r.span,
                desc: "record declaration".into(),
            },
        });
    }

    for c in &vc.classes {
        let lean_name = crate::vcgen::lean_class_name(&c.name);
        if exclude.classes.contains(&lean_name) {
            continue;
        }
        names.classes.insert(lean_name);
        let first = e.line + 1;
        e.push(&format!(
            "structure {} where",
            crate::vcgen::lean_class_name(&c.name)
        ));
        for (fname, fty) in &c.fields {
            e.push(&format!("  {fname} : {fty}"));
        }
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: c.span,
                desc: "class declaration".into(),
            },
        });
    }

    for g in &vc.ghosts {
        let head = ghost_head_name(&g.text);
        if exclude.ghosts.contains(&head) {
            continue;
        }
        names.ghosts.insert(head);
        let first = e.line + 1;
        // Non-recursive ghost defs get @[simp] so contracts naming them
        // unfold under the portfolio; recursive ones would loop and are
        // unfolded manually in discharges. `#[unfold]` opts an item in
        // explicitly — typically a conditional step lemma whose side
        // conditions gate the rewrite to concrete data.
        let attr = if g.unfold || (g.keyword == "def" && !ghost_recursive(&g.text)) {
            "@[simp] "
        } else {
            ""
        };
        e.push(&format!("{attr}{} {}", g.keyword, g.text));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: g.span,
                desc: format!("ghost `{}`", g.keyword),
            },
        });
    }

    for wf in &vc.clause_wfs {
        if exclude.wfs.contains(&wf.def_name) {
            continue;
        }
        names.wfs.insert(wf.def_name.clone());
        let first = e.line + 1;
        e.push(&format!(
            "def {} {} : {} :=",
            wf.def_name,
            binder_list(&wf.binders),
            wf.result_ty
        ));
        e.push(&format!("  ({})", wf.text));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: wf.span,
                desc: wf.desc.clone(),
            },
        });
    }

    for (i, ob) in vc.obligations.iter().enumerate() {
        // Deferred/assumed obligations become runtime traps or axioms;
        // no theorem is emitted (their goals are already assumed
        // downstream by the generator, which is exactly their semantics).
        if skip.contains(&ob.name) || exclude.thms.contains(&ob.thm_name) {
            continue;
        }
        names.thms.insert(ob.thm_name.clone());
        names.obligations.insert(ob.name.clone());
        let discharge = discharges.iter().find(|d| d.name == ob.name);
        let first = e.line + 1;
        e.push(&format!(
            "/-- `{}` — {} -/",
            ob.name,
            doc_safe(&ob.kind_desc)
        ));
        e.push(&format!(
            "theorem {} {}",
            ob.thm_name,
            binder_list(&ob.binders)
        ));
        for (hname, hprop) in &ob.hyps {
            e.push(&format!("    ({hname} : {hprop})"));
        }
        match discharge {
            None => e.push(&format!("    : ({}) := by sable_auto", ob.goal)),
            Some(d) => {
                e.push(&format!("    : ({}) := by", ob.goal));
                for line in d.script.lines() {
                    e.push(&format!("  {line}"));
                }
            }
        }
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: match discharge {
                None => MapTarget::Obligation(i),
                Some(d) => MapTarget::Discharged {
                    name: ob.name.clone(),
                    span: d.span,
                    goal: ob.goal.clone(),
                },
            },
        });
    }

    Emitted {
        lean_source: e.buf,
        names,
        map,
    }
}

/// Head name of a ghost `def`/`theorem` (the first identifier of its
/// verbatim text).
pub fn ghost_head_name(text: &str) -> String {
    text.trim_start()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect()
}

fn binder_list(binders: &[(String, String)]) -> String {
    binders
        .iter()
        .map(|(name, ty)| format!("({name} : {ty})"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// A ghost def is recursive if its body mentions its own head name.
fn ghost_recursive(text: &str) -> bool {
    let name = ghost_head_name(text);
    match text.split_once(":=") {
        Some((_, body)) => !name.is_empty() && crate::vcgen::mentions(body, &name),
        None => false,
    }
}

fn doc_safe(s: &str) -> String {
    s.replace("-/", "- /")
}

/// Locate the repo root: the nearest ancestor containing `lean/lean-toolchain`.
pub fn find_repo_root(start: &Path) -> Option<PathBuf> {
    let mut dir = if start.is_dir() {
        start.to_path_buf()
    } else {
        start.parent()?.to_path_buf()
    };
    loop {
        if dir.join("lean").join("lean-toolchain").is_file() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

pub struct LeanMessage {
    pub severity: String,
    pub line: usize,
    pub data: String,
}

/// The generated-artifact directory (`import`able compiled modules) —
/// on `LEAN_PATH` for every check, whether or not it exists yet.
pub fn modules_dir(repo_root: &Path) -> PathBuf {
    repo_root.join(".sable-out").join("modules")
}

/// The full `LEAN_PATH` for checking generated files: the lake
/// workspace's own path (prelude + toolchain; queried once per process)
/// extended with the generated-artifact directory.
pub fn lean_search_path(repo_root: &Path) -> Result<String, String> {
    use std::sync::OnceLock;
    static LAKE_PATH: OnceLock<Result<String, String>> = OnceLock::new();
    let base = LAKE_PATH
        .get_or_init(|| {
            let out = Command::new("lake")
                .args(["env", "printenv", "LEAN_PATH"])
                .current_dir(repo_root.join("lean"))
                .output()
                .map_err(|err| format!("failed to run `lake env`: {err}"))?;
            if !out.status.success() {
                return Err(format!(
                    "`lake env printenv LEAN_PATH` failed:\n{}",
                    String::from_utf8_lossy(&out.stderr)
                ));
            }
            Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
        })
        .clone()?;
    Ok(format!("{base}:{}", modules_dir(repo_root).display()))
}

/// Build the prelude if needed and check the generated file. With
/// `olean_out`, additionally compile it into an importable artifact
/// (the file must live in the modules dir, which becomes `--root` so
/// the Lean module name matches the file stem).
pub fn run_lean(
    repo_root: &Path,
    lean_file: &Path,
    olean_out: Option<&Path>,
) -> Result<Vec<LeanMessage>, String> {
    let lean_dir = repo_root.join("lean");

    // `lake build` is a fast no-op when the prelude is current, and keeps
    // agents who edit the prelude from checking against stale oleans.
    let build = Command::new("lake")
        .arg("build")
        .current_dir(&lean_dir)
        .output()
        .map_err(|err| format!("failed to run `lake build`: {err}"))?;
    if !build.status.success() {
        return Err(format!(
            "`lake build` failed in {}:\n{}{}",
            lean_dir.display(),
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr),
        ));
    }

    // Direct `lean` (the elan shim resolves the pinned toolchain from
    // `lean/`): `lake env lean` rebuilds LEAN_PATH from scratch and
    // drops ambient additions, so the search path is passed explicitly.
    let mut cmd = Command::new("lean");
    cmd.arg("--json")
        .env("LEAN_PATH", lean_search_path(repo_root)?)
        .current_dir(&lean_dir);
    if let Some(olean) = olean_out {
        cmd.arg("--root")
            .arg(modules_dir(repo_root))
            .arg("-o")
            .arg(olean);
    }
    let output = cmd
        .arg(lean_file)
        .output()
        .map_err(|err| format!("failed to run `lean`: {err}"))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut messages = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else {
            continue; // non-JSON chatter
        };
        let severity = v["severity"].as_str().unwrap_or("error").to_string();
        let msg_line = v["pos"]["line"].as_u64().unwrap_or(0) as usize;
        let data = match &v["data"] {
            serde_json::Value::String(s) => s.clone(),
            other => other.to_string(),
        };
        messages.push(LeanMessage {
            severity,
            line: msg_line,
            data,
        });
    }

    // A crash with no parseable messages should still surface.
    if !output.status.success() && messages.iter().all(|m| m.severity != "error") {
        return Err(format!(
            "lean exited with {} but produced no error messages:\n{}\n{}",
            output.status,
            stdout,
            String::from_utf8_lossy(&output.stderr),
        ));
    }

    Ok(messages)
}

/// Map lean error messages back to .sable diagnostics.
pub fn diagnose(
    emitted: &Emitted,
    vc: &VcResult,
    messages: &[LeanMessage],
    mods: &crate::modules::ModuleSet,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for msg in messages {
        if msg.severity != "error" {
            continue;
        }
        let entry = emitted
            .map
            .iter()
            .find(|en| en.first_line <= msg.line && msg.line <= en.last_line);
        match entry.map(|en| &en.target) {
            Some(MapTarget::Clause { span, desc }) => diags.push(Diagnostic {
                name: "proof.clause_syntax".into(),
                title: format!("{desc} fails to elaborate"),
                span: *span,
                label: "this clause is not well-formed proof language".into(),
                notes: vec![("lean".into(), msg.data.clone())],
            }),
            Some(MapTarget::Discharged { name, span, goal }) => diags.push(Diagnostic {
                name: "proof.discharge_failed".into(),
                title: format!("discharge of `{name}` does not prove it"),
                span: *span,
                label: "this tactic script fails".into(),
                notes: vec![
                    ("goal".into(), goal.clone()),
                    ("lean".into(), msg.data.clone()),
                ],
            }),
            Some(MapTarget::Obligation(i)) => {
                let ob: &Obligation = &vc.obligations[*i];
                let mut notes = vec![("goal".into(), ob.goal.clone())];
                if !ob.context.is_empty() {
                    // Each entry carries the line its fact came from, so
                    // the provenance of every hypothesis is traceable —
                    // cross-module facts name their file.
                    let ob_file = mods.locate(ob.span.start).0.to_string();
                    let rendered: Vec<String> = ob
                        .context
                        .iter()
                        .map(|(text, span)| {
                            if span.start == 0 && span.end == 0 {
                                text.clone()
                            } else {
                                let (file, line, _) = mods.locate(span.start);
                                if file == ob_file {
                                    format!("{text}   (line {line})")
                                } else {
                                    let short = file.rsplit('/').next().unwrap_or(file);
                                    format!("{text}   ({short}:{line})")
                                }
                            }
                        })
                        .collect();
                    notes.push(("context".into(), rendered.join("\n")));
                }
                notes.push((
                    "automation".into(),
                    "`sable_auto` could not discharge this obligation \
                     (prove it with a `discharge <obligation> by <tactics>` block)"
                        .into(),
                ));
                notes.push(("lean".into(), msg.data.clone()));
                diags.push(Diagnostic {
                    name: ob.name.clone(),
                    title: format!("unproved obligation `{}`", ob.name),
                    span: ob.span,
                    label: ob.kind_desc.clone(),
                    notes,
                });
            }
            None => diags.push(Diagnostic {
                name: "internal.unmapped_lean_error".into(),
                span: Span::new(0, 0),
                title: "internal error: Lean reported an error outside any obligation".into(),
                label: "this is a bug in the Sable compiler, not in your program".into(),
                notes: vec![("lean".into(), format!("line {}: {}", msg.line, msg.data))],
            }),
        }
    }
    diags
}

/// Map the automation-budget warnings (`sable_grind`'s expensive-success
/// diagnostics) back to obligations. Non-fatal: returned separately from
/// `diagnose` so callers report them without failing the check. A
/// `grind?` "Try this:" suggestion at the same position becomes a
/// ready-to-paste `discharge` note.
pub fn diagnose_warnings(
    emitted: &Emitted,
    vc: &VcResult,
    messages: &[LeanMessage],
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for msg in messages {
        if msg.severity != "warning" || !msg.data.contains("expensive automation") {
            continue;
        }
        let entry = emitted
            .map
            .iter()
            .find(|en| en.first_line <= msg.line && msg.line <= en.last_line);
        let suggestion = messages.iter().find(|m| {
            m.severity == "information"
                && m.data.contains("Try th")
                && entry.is_some_and(|en| en.first_line <= m.line && m.line <= en.last_line)
        });
        let mut notes = vec![("automation".into(), msg.data.clone())];
        if let Some(sug) = suggestion {
            // "Try this:"/"Try these:" list alternatives; the first is
            // grind's own minimization of the successful proof.
            let tactic = sug
                .data
                .lines()
                .nth(1)
                .map(|l| l.trim().trim_start_matches("[apply]").trim().to_string())
                .unwrap_or_default();
            notes.push((
                "suggested".into(),
                format!("discharge <obligation> by {tactic}"),
            ));
        }
        match entry.map(|en| &en.target) {
            Some(MapTarget::Obligation(i)) => {
                let ob: &Obligation = &vc.obligations[*i];
                if let Some((_, sug)) = notes.iter_mut().find(|(k, _)| k == "suggested") {
                    *sug = sug.replace("<obligation>", &ob.name);
                }
                diags.push(Diagnostic {
                    name: ob.name.clone(),
                    title: format!("obligation `{}` leans on expensive automation", ob.name),
                    span: ob.span,
                    label: ob.kind_desc.clone(),
                    notes,
                });
            }
            Some(MapTarget::Discharged { name, span, .. }) => diags.push(Diagnostic {
                name: name.clone(),
                title: format!("discharge of `{name}` leans on expensive automation"),
                span: *span,
                label: "this tactic script reaches the budgeted grind".into(),
                notes,
            }),
            _ => {}
        }
    }
    diags
}

/// Deduplicate: one obligation can produce several lean messages.
pub fn dedup_by_name(diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen = std::collections::HashSet::new();
    diags
        .into_iter()
        .filter(|d| seen.insert((d.name.clone(), d.span.start)))
        .collect()
}

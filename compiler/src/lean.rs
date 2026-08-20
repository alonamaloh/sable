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
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::fd::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

enum MapTarget {
    Clause {
        span: Span,
        desc: String,
    },
    /// Fixed-proof compiler certificate for a selected symbolic transition.
    Certificate(usize),
    /// Closed argument-evaluation schedule selected from the typed AST and
    /// checker ownership records.
    ArgumentScheduleCertificate(usize),
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
    /// Non-skippable certificate theorem names.
    pub certificates: std::collections::HashSet<String>,
    /// Obligation names (escape-hatch ownership checks).
    pub obligations: std::collections::HashSet<String>,
}

impl EmittedNames {
    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
            && self.ghosts.is_empty()
            && self.wfs.is_empty()
            && self.thms.is_empty()
            && self.certificates.is_empty()
    }
}

pub struct Emitted {
    pub lean_source: String,
    /// What this file declares (after exclusion filtering).
    pub names: EmittedNames,
    /// Exact user-derived Lean fragments whose parser boundaries must be
    /// authenticated before this document may be submitted to Lean.
    pub(crate) ingress: Vec<IngressFragment>,
    map: Vec<MapEntry>,
}

#[derive(Clone)]
pub(crate) struct IngressFragment {
    category: &'static str,
    text: String,
    expected_kind: &'static str,
    expected_name: String,
    pub(crate) span: Span,
    pub(crate) description: String,
}

impl IngressFragment {
    fn term(text: impl Into<String>, span: Span, description: impl Into<String>) -> Self {
        Self {
            category: "term",
            text: text.into(),
            expected_kind: "",
            expected_name: String::new(),
            span,
            description: description.into(),
        }
    }

    fn command(
        text: impl Into<String>,
        expected_kind: &'static str,
        expected_name: impl Into<String>,
        span: Span,
        description: impl Into<String>,
    ) -> Self {
        Self {
            category: "command",
            text: text.into(),
            expected_kind,
            expected_name: expected_name.into(),
            span,
            description: description.into(),
        }
    }
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
    let mut ingress = Vec::new();

    e.push("import Sable");
    for i in imports {
        e.push(&format!("import {i}"));
    }
    e.push("open Sable");
    e.push("set_option linter.unusedVariables false");
    // The portfolio owns the proof-cost policy: each expensive tier of
    // `sable_auto` runs under its own heartbeat budget, and their sum
    // exceeds the elaborator's default allowance — an obligation that
    // exhausts every tier near its cap would otherwise die on the outer
    // limit with an uncatchable timeout instead of a clean tier failure
    // (ADR 0082). Twice the default keeps the outer cap as a backstop.
    e.push("set_option maxHeartbeats 400000");
    // Test/CI hook: shrink or disable the grind heartbeat budget
    // without touching source (the option itself lives in the prelude).
    if let Ok(v) = std::env::var("SABLE_GRIND_HEARTBEATS") {
        if v.parse::<u64>().is_ok() {
            e.push(&format!("set_option sable.grindHeartbeats {v}"));
        }
    }
    // The trust manifest, inside the hashed content. Changing an audit id
    // or adding an extern has to invalidate the artifact exactly as
    // changing a proof does. The exact policy-bound `.ok` stamp is necessary
    // but cannot describe per-artifact trust, so this manifest must remain in
    // the generated bytes too (ADR 0027).
    if !vc.trust.externs.is_empty() {
        e.push("-- trusted boundary: audited extern contracts");
        for (id, reason, name) in &vc.trust.externs {
            e.push(&format!(
                "--   audit-id-utf8:{} extern-name-utf8:{} reason-utf8:{}",
                comment_hex(id),
                comment_hex(name),
                comment_hex(reason),
            ));
        }
    }
    if !vc.machine.profiles.is_empty() {
        e.push("-- formal machine profiles (kernel-checked, not trusted axioms)");
        for (id, hash) in &vc.machine.profiles {
            e.push(&format!(
                "--   profile-id-utf8:{} semantics-hash-utf8:{}",
                comment_hex(id),
                comment_hex(hash),
            ));
        }
        if !vc.machine.intrinsics.is_empty() {
            e.push(&format!(
                "--   intrinsics-utf8:{}",
                comment_hex(&vc.machine.intrinsics.join("\0"))
            ));
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
            ingress.push(IngressFragment::term(
                field.lean_ty.clone(),
                r.span,
                format!("record `{}` field `{}` type", r.name, field.name),
            ));
            ingress.push(IngressFragment::term(
                field.layout.clone(),
                r.span,
                format!("record `{}` field `{}` layout", r.name, field.name),
            ));
            if let Some(wf) = &field.wf {
                ingress.push(IngressFragment::term(
                    wf.clone(),
                    r.span,
                    format!("record `{}` field `{}` well-formedness", r.name, field.name),
                ));
            }
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
            e.push(&format!(
                "def {}Offset : Int := {}",
                field.name, field.offset
            ));
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
        let wf_body = if value_wf.is_empty() {
            "True".to_string()
        } else {
            value_wf.join(" ∧ ")
        };
        e.push(&format!("def wf (value : {lean_name}) : Prop :="));
        e.push(&format!("  {wf_body}"));
        // A plain `def` is invisible to `simp`; the explicit unfolding
        // lemma is what lets automation read the field facts out of a
        // `wf` hypothesis (an elementwise array fact included).
        e.push(&format!(
            "@[simp] theorem wf_iff (value : {lean_name}) : wf value ↔ ({wf_body}) := Iff.rfl"
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
            ingress.push(IngressFragment::term(
                fty.clone(),
                c.span,
                format!("class `{}` field `{fname}` type", c.name),
            ));
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
        names.ghosts.insert(head.clone());
        let first = e.line + 1;
        // Non-recursive ghost defs get @[simp] so contracts naming them
        // unfold under the portfolio; recursive ones would loop and are
        // unfolded manually in discharges. `#[unfold]` opts an item in
        // explicitly — typically a conditional step lemma whose side
        // conditions gate the rewrite to concrete data.
        let mut attr = String::new();
        if g.unfold || (g.keyword == "def" && !ghost_recursive(&g.text)) {
            attr.push_str("@[simp] ");
        }
        // `#[fact]`: the instantiation tier applies the theorem at the
        // argument tuples occurring in each obligation.
        if g.fact {
            attr.push_str("@[sable_fact] ");
        }
        let command = format!("{attr}{} {}", g.keyword, g.text);
        ingress.push(IngressFragment::command(
            command.clone(),
            if g.keyword == "def" {
                "definition"
            } else {
                "theorem"
            },
            head.clone(),
            g.span,
            format!("ghost `{}` declaration `{head}`", g.keyword),
        ));
        e.push(&command);
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
        for (_, ty) in &wf.binders {
            ingress.push(IngressFragment::term(
                ty.clone(),
                wf.span,
                format!("{} binder type", wf.desc),
            ));
        }
        ingress.push(IngressFragment::term(
            wf.result_ty,
            wf.span,
            format!("{} result type", wf.desc),
        ));
        let wrapped_text = format!("({})", wf.text);
        ingress.push(IngressFragment::term(
            wrapped_text.clone(),
            wf.span,
            wf.desc.clone(),
        ));
        let first = e.line + 1;
        e.push(&format!(
            "def {} {} : {} :=",
            wf.def_name,
            binder_list(&wf.binders),
            wf.result_ty
        ));
        e.push(&format!("  {wrapped_text}"));
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

    for (i, certificate) in vc.transition_certificates.iter().enumerate() {
        if exclude.certificates.contains(&certificate.thm_name) {
            continue;
        }
        names.certificates.insert(certificate.thm_name.clone());
        for (_, ty) in &certificate.binders {
            ingress.push(IngressFragment::term(
                ty.clone(),
                certificate.span(),
                format!("certificate `{}` binder type", certificate.name),
            ));
        }
        for (_, proposition) in &certificate.hyps {
            ingress.push(IngressFragment::term(
                proposition.clone(),
                certificate.span(),
                format!("certificate `{}` hypothesis", certificate.name),
            ));
        }
        ingress.push(IngressFragment::term(
            certificate.lean_goal(),
            certificate.span(),
            format!("certificate `{}` goal", certificate.name),
        ));
        ingress.push(IngressFragment::term(
            certificate.lean_proof(),
            certificate.span(),
            format!("certificate `{}` proof", certificate.name),
        ));
        let first = e.line + 1;
        e.push(&format!(
            "/-- `{}` — kernel-checked {} transition for `{}` -/",
            certificate.name,
            certificate.description(),
            doc_safe(&certificate.place().render())
        ));
        e.push(&format!(
            "theorem {} {}",
            certificate.thm_name,
            binder_list(&certificate.binders)
        ));
        for (hname, hprop) in &certificate.hyps {
            e.push(&format!("    ({hname} : {hprop})"));
        }
        e.push(&format!(
            "    : ({}) := {}",
            certificate.lean_goal(),
            certificate.lean_proof()
        ));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Certificate(i),
        });
    }

    for (i, certificate) in vc.argument_schedule_certificates.iter().enumerate() {
        if exclude.certificates.contains(&certificate.thm_name) {
            continue;
        }
        names.certificates.insert(certificate.thm_name.clone());
        ingress.push(IngressFragment::term(
            certificate.lean_goal(),
            certificate.span,
            format!("argument-schedule certificate `{}` goal", certificate.name),
        ));
        ingress.push(IngressFragment::term(
            certificate.lean_proof(),
            certificate.span,
            format!("argument-schedule certificate `{}` proof", certificate.name),
        ));
        let first = e.line + 1;
        e.push(&format!(
            "/-- `{}` — kernel-checked {} for {} -/",
            certificate.name,
            certificate.description(),
            doc_safe(&certificate.boundary())
        ));
        e.push(&format!(
            "theorem {} : ({}) := {}",
            certificate.thm_name,
            certificate.lean_goal(),
            certificate.lean_proof()
        ));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::ArgumentScheduleCertificate(i),
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
        for (_, ty) in &ob.binders {
            ingress.push(IngressFragment::term(
                ty.clone(),
                ob.span,
                format!("obligation `{}` binder type", ob.name),
            ));
        }
        for (_, proposition) in &ob.hyps {
            ingress.push(IngressFragment::term(
                proposition.clone(),
                ob.span,
                format!("obligation `{}` hypothesis", ob.name),
            ));
        }
        ingress.push(IngressFragment::term(
            ob.goal.clone(),
            ob.span,
            format!("obligation `{}` goal", ob.name),
        ));
        if let Some(discharge) = discharge {
            let mut proof = String::from("by\n");
            for line in discharge.script.lines() {
                proof.push_str("  ");
                proof.push_str(line);
                proof.push('\n');
            }
            ingress.push(IngressFragment::term(
                proof,
                discharge.span,
                format!("discharge of `{}`", ob.name),
            ));
        }
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
        ingress,
        map,
    }
}

/// Head name of a ghost `def`/`theorem` in Sable's deliberately narrow Lean
/// declaration-id spelling: ASCII identifier characters plus apostrophes.
/// The trusted parser independently checks the same identity before Lean sees
/// the generated document.
pub fn ghost_head_name(text: &str) -> String {
    text.trim_start()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || matches!(*c, '_' | '\''))
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
    s.replace("/-", "/ -").replace("-/", "- /")
}

/// Encode arbitrary UTF-8 metadata into an ASCII-only, single-line comment
/// payload. The bytes remain exact inputs to content addressing without
/// allowing decoded string escapes to terminate the generated comment.
fn comment_hex(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len() * 2);
    for byte in value.as_bytes() {
        use std::fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
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

/// Stable diagnostic emitted when Lean accepts a document but reports a
/// warning outside Sable's one compiler-owned, structured exception.
pub const UNEXPECTED_LEAN_WARNING_DIAGNOSTIC: &str = "proof.unexpected_lean_warning";

/// Stable diagnostic emitted when one user-derived Lean splice is not exactly
/// one permitted command/term under the pinned trusted parser.
pub const INVALID_LEAN_INGRESS_DIAGNOSTIC: &str = "proof.invalid_lean_ingress";

/// The generated-artifact directory (`import`able compiled modules) —
/// on `LEAN_PATH` for every check, whether or not it exists yet.
pub fn modules_dir(repo_root: &Path) -> PathBuf {
    repo_root.join(".sable-out").join("modules")
}

/// Exact repository-local inputs that can affect a generated proof. The FNV
/// identifier is only a compact directory/name tag; every reuse also compares
/// this complete map, so a hash collision fails closed.
pub(crate) const PROOF_POLICY_VERSION: &str = "confine-generated-lean-ingress-v3";
const PROOF_ENVIRONMENT_ID_PREFIX: &str = "proof-env-v4-fnv64:";

#[derive(Clone)]
pub struct ProofEnvironment {
    id: String,
    policy: Arc<str>,
    files: Arc<BTreeMap<String, Vec<u8>>>,
}

impl ProofEnvironment {
    /// Capture one immutable view before profile generation or dependency work.
    pub fn capture(repo_root: &Path) -> Result<Self, String> {
        Self::from_files(capture_proof_files(repo_root)?)
    }

    fn from_files(files: BTreeMap<String, Vec<u8>>) -> Result<Self, String> {
        Self::from_files_with_policy(files, PROOF_POLICY_VERSION)
    }

    fn from_files_with_policy(
        files: BTreeMap<String, Vec<u8>>,
        proof_policy: &str,
    ) -> Result<Self, String> {
        if files.is_empty() {
            return Err("proof environment contains no inputs".into());
        }
        if proof_policy.is_empty() || proof_policy.contains('\n') || proof_policy.contains('\r') {
            return Err("proof policy must be a nonempty single-line identity".into());
        }
        let id = proof_environment_id(&files, proof_policy);
        Ok(Self {
            id,
            policy: Arc::from(proof_policy),
            files: Arc::new(files),
        })
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub(crate) fn policy(&self) -> &str {
        &self.policy
    }

    /// Load a client-selected published snapshot without consulting the live
    /// checkout. This is how a long-lived daemon recovers the exact bytes named
    /// in a request after those checkout files have changed.
    pub fn load_published(repo_root: &Path, id: &str) -> Result<Self, String> {
        validate_environment_id(id)?;
        validate_proof_environment_dir(repo_root, id)?;
        let source = proof_environment_dir(repo_root, id).join("source");
        let environment = Self::capture(&source)?;
        if environment.id != id {
            return Err(format!(
                "published proof environment {} contains bytes for {}",
                source.display(),
                environment.id
            ));
        }
        environment.validate_snapshot(&source, "published source snapshot")?;
        Ok(environment)
    }

    /// Atomically publish a repo-shaped source snapshot. A racing process may
    /// win the rename, but it is accepted only after an exact byte-map match.
    pub fn materialize_source(&self, repo_root: &Path) -> Result<PathBuf, String> {
        let environment_dir = ensure_proof_environment_dir(repo_root, &self.id)?;
        let source = environment_dir.join("source");
        if std::fs::symlink_metadata(&source).is_ok() {
            self.validate_snapshot(&source, "published source snapshot")?;
            return Ok(source);
        }

        let temporary = unique_directory(&environment_dir, "source.tmp")?;
        let result = (|| {
            write_proof_files(&temporary, &self.files)?;
            write_proof_policy_marker(&temporary, &self.policy)?;
            self.validate_snapshot(&temporary, "temporary source snapshot")?;
            match std::fs::rename(&temporary, &source) {
                Ok(()) => {}
                Err(_error) if std::fs::symlink_metadata(&source).is_ok() => {
                    self.validate_snapshot(&source, "racing published source snapshot")?;
                    let _ = std::fs::remove_dir_all(&temporary);
                    return Ok(source.clone());
                }
                Err(error) => {
                    return Err(format!(
                        "cannot publish proof source snapshot {}: {error}",
                        source.display()
                    ));
                }
            }
            self.validate_snapshot(&source, "published source snapshot")?;
            Ok(source.clone())
        })();
        if result.is_err() && temporary.is_dir() {
            // The name is unique to this process/attempt; never clean a path a
            // different builder could own.
            let _ = std::fs::remove_dir_all(&temporary);
        }
        result
    }

    /// Build at the final stable path. Lake and Lean can embed absolute paths,
    /// so building elsewhere and renaming would not produce an immutable,
    /// reproducible workspace. A per-id advisory lock serializes processes;
    /// READY is written last and a READY workspace is never rebuilt.
    pub fn ensure_built(&self, repo_root: &Path) -> Result<PathBuf, String> {
        self.materialize_source(repo_root)?;
        let environment_dir = proof_environment_dir(repo_root, &self.id);
        let _lock = AdvisoryLock::acquire(&environment_dir.join("build.lock"), "proof-build")?;
        self.validate_snapshot(&environment_dir.join("source"), "published source snapshot")?;

        let built = environment_dir.join("built");
        let ready = built.join("READY");
        if std::fs::symlink_metadata(&ready).is_ok() {
            match self.validate_built(&built) {
                Ok(()) => return Ok(built),
                Err(_) => {
                    // READY is published atomically below, but older/crashed
                    // writers may have left a partial marker. Under this id's
                    // lock, an invalid marker is incomplete state, not a
                    // permanent poisoned cache entry.
                    remove_unready_built(&environment_dir, &built)?;
                }
            }
        }
        // The invalid-READY branch above has already removed `built`.
        if std::fs::symlink_metadata(&built).is_ok() {
            remove_unready_built(&environment_dir, &built)?;
        }

        std::fs::create_dir(&built)
            .map_err(|error| format!("cannot create proof build {}: {error}", built.display()))?;
        write_proof_files(&built, &self.files)?;
        write_proof_policy_marker(&built, &self.policy)?;
        self.validate_snapshot(&built, "unbuilt proof workspace")?;

        let _process_lock = ProofProcessLock::acquire(repo_root)?;
        build_proof_environment_serial(&built, &self.files)?;
        self.validate_snapshot(&built, "completed proof build")?;
        let output_digests = proof_build_output_digests(&built, &self.files)?;
        publish_ready(&built, &ready, &self.id, &self.policy, &output_digests)?;
        self.validate_built(&built)?;
        Ok(built)
    }

    pub fn validate_built(&self, built: &Path) -> Result<(), String> {
        self.validate_snapshot(built, "immutable proof build")?;
        let ready = built.join("READY");
        let metadata = std::fs::symlink_metadata(&ready).map_err(|error| {
            format!(
                "cannot inspect proof readiness {}: {error}",
                ready.display()
            )
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(format!(
                "proof readiness {} is not a regular file",
                ready.display()
            ));
        }
        let actual = std::fs::read(&ready)
            .map_err(|error| format!("cannot read proof readiness {}: {error}", ready.display()))?;
        let output_digests = proof_build_output_digests(built, &self.files)?;
        if !proof_ready_stamp_matches(&actual, &self.id, &self.policy, &output_digests) {
            return Err(format!(
                "proof readiness {} does not exactly match environment {}, verification policy `{}`, and the SHA-256 identities of its trusted outputs",
                ready.display(),
                self.id,
                self.policy,
            ));
        }
        Ok(())
    }

    fn validate_snapshot(&self, root: &Path, description: &str) -> Result<(), String> {
        let actual = capture_proof_files(root)?;
        if actual != *self.files {
            return Err(format!(
                "{description} {} does not exactly match proof environment {} (possible content-address collision)",
                root.display(),
                self.id
            ));
        }
        validate_proof_policy_marker(root, &self.policy, description)
    }
}

const PROOF_POLICY_MARKER_FILE: &str = ".sable-verification-policy";
const PROOF_READY_STAMP_VERSION: &str = "sable-proof-ready-v2";

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProofBuildOutputDigests {
    local_olean_sha256: BTreeMap<String, String>,
    proof_auditor_sha256: String,
}

fn proof_policy_marker(proof_policy: &str) -> String {
    format!("sable-verification-policy:{proof_policy}\n")
}

fn proof_policy_marker_matches(actual: Option<&[u8]>, proof_policy: &str) -> bool {
    actual.is_some_and(|actual| actual == proof_policy_marker(proof_policy).as_bytes())
}

fn write_proof_policy_marker(root: &Path, proof_policy: &str) -> Result<(), String> {
    let path = root.join(PROOF_POLICY_MARKER_FILE);
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .and_then(|mut file| file.write_all(proof_policy_marker(proof_policy).as_bytes()))
        .map_err(|error| {
            format!(
                "cannot write proof-policy marker {}: {error}",
                path.display()
            )
        })
}

fn validate_proof_policy_marker(
    root: &Path,
    proof_policy: &str,
    description: &str,
) -> Result<(), String> {
    let path = root.join(PROOF_POLICY_MARKER_FILE);
    let metadata = std::fs::symlink_metadata(&path).map_err(|error| {
        format!(
            "cannot inspect {description} policy {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "{description} policy {} is not a regular file",
            path.display()
        ));
    }
    let actual = std::fs::read(&path).map_err(|error| {
        format!(
            "cannot read {description} policy {}: {error}",
            path.display()
        )
    })?;
    if proof_policy_marker_matches(Some(&actual), proof_policy) {
        Ok(())
    } else {
        Err(format!(
            "{description} policy {} does not exactly match verification policy `{proof_policy}`",
            path.display()
        ))
    }
}

fn proof_ready_stamp(
    id: &str,
    proof_policy: &str,
    output_digests: &ProofBuildOutputDigests,
) -> String {
    let mut stamp = format!(
        "{PROOF_READY_STAMP_VERSION}\nproof-environment:{id}\n{}local-olean-count:{}\n",
        proof_policy_marker(proof_policy),
        output_digests.local_olean_sha256.len(),
    );
    for (path, digest) in &output_digests.local_olean_sha256 {
        stamp.push_str(&format!(
            "local-olean-path-utf8:{}\nlocal-olean-sha256:{digest}\n",
            comment_hex(path),
        ));
    }
    stamp.push_str(&format!(
        "proof-auditor-sha256:{}\n",
        output_digests.proof_auditor_sha256,
    ));
    stamp
}

fn proof_ready_stamp_matches(
    actual: &[u8],
    id: &str,
    proof_policy: &str,
    output_digests: &ProofBuildOutputDigests,
) -> bool {
    actual == proof_ready_stamp(id, proof_policy, output_digests).as_bytes()
}

fn proof_environment_id(files: &BTreeMap<String, Vec<u8>>, proof_policy: &str) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    hash = fingerprint_bytes(hash, b"sable-proof-policy\0");
    hash = fingerprint_bytes(hash, &(proof_policy.len() as u64).to_le_bytes());
    hash = fingerprint_bytes(hash, proof_policy.as_bytes());
    for (label, bytes) in files {
        hash = fingerprint_bytes(hash, &(label.len() as u64).to_le_bytes());
        hash = fingerprint_bytes(hash, label.as_bytes());
        hash = fingerprint_bytes(hash, &(bytes.len() as u64).to_le_bytes());
        hash = fingerprint_bytes(hash, bytes);
    }
    format!("{PROOF_ENVIRONMENT_ID_PREFIX}{hash:016x}")
}

const SERIAL_LAKE_TOOLCHAIN: &str = "leanprover/lean4:v4.32.2";
const SERIAL_LAKE_VERSION: &str = "Lake version 5.0.0-src+f3b06c7 (Lean version 4.32.2)";
const PROOF_TOOL_OVERRIDES: [&str; 23] = [
    "ELAN_TOOLCHAIN",
    "LEAN_PATH",
    "LEAN_SYSROOT",
    "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "LEAN",
    "LAKE",
    "LAKE_HOME",
    "LAKE_OVERRIDE_LEAN",
    "LAKE_CACHE_KEY",
    "LAKE_CACHE_ARTIFACT_ENDPOINT",
    "LAKE_CACHE_REVISION_ENDPOINT",
    "LAKE_CACHE_SERVICE",
    "LAKE_CACHE_DIR",
    "LAKE_PKG_URL_MAP",
    "RESERVOIR_API_BASE_URL",
    "RESERVOIR_API_URL",
    "LEAN_CC",
    "LEAN_AR",
    "CC",
    "AR",
    "CXX",
    "LD",
];

/// Build the captured local Lean library with Lake's asynchronous jobs forced
/// inline by the audited Lean 4.32 runtime and one import worker. An absent task
/// manager is the only hard scheduler bound: positive task-worker counts may be
/// exceeded to avoid deadlock. The two explicit repository targets build in one
/// serialized Lake workload with at most one Lean compiler runtime at a time.
fn build_proof_environment_serial(
    built: &Path,
    files: &BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    require_serial_lake_toolchain(files)?;
    require_closed_lake_manifest(files)?;
    let lean_dir = built.join("lean");
    require_serial_lake_version(&lean_dir)?;
    let output = serial_lake_build_command(&lean_dir)
        .output()
        .map_err(|error| format!("failed to run serial Lake proof build: {error}"))?;
    validate_serial_lake_build_output(
        output.status.success(),
        &output.stdout,
        &output.stderr,
        &lean_dir,
        &output.status.to_string(),
    )
}

fn validate_serial_lake_build_output(
    status_success: bool,
    stdout: &[u8],
    stderr: &[u8],
    lean_dir: &Path,
    status: &str,
) -> Result<(), String> {
    if !status_success {
        Err(format!(
            "serial Lake proof build failed with {status} in {}:\n{}{}",
            lean_dir.display(),
            String::from_utf8_lossy(stdout),
            String::from_utf8_lossy(stderr),
        ))
    } else if stdout.is_empty() && stderr.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "serial Lake proof build succeeded but emitted output; proof-environment builds fail closed on every warning or unclassified message in {}:\nstdout:\n{}\nstderr:\n{}",
            lean_dir.display(),
            String::from_utf8_lossy(stdout),
            String::from_utf8_lossy(stderr),
        ))
    }
}

/// PATH and elan command resolution remain part of the trusted host boundary.
/// Requiring the exact audited version before building fails closed when PATH
/// accidentally selects a direct or otherwise different Lake installation.
fn require_serial_lake_version(lean_dir: &Path) -> Result<(), String> {
    let output = serial_lake_version_command(lean_dir)
        .output()
        .map_err(|error| format!("failed to identify Lake for serial proof build: {error}"))?;
    validate_serial_lake_version(output.status.success(), &output.stdout, &output.stderr)
}

fn validate_serial_lake_version(
    status_success: bool,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<(), String> {
    let version_bytes = SERIAL_LAKE_VERSION.as_bytes();
    let exact_stdout = stdout == version_bytes
        || stdout.strip_suffix(b"\n") == Some(version_bytes)
        || stdout.strip_suffix(b"\r\n") == Some(version_bytes);
    if status_success && exact_stdout && stderr.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "serial proof build requires exact `{SERIAL_LAKE_VERSION}` from `lake --version` with no stderr; status_success={status_success}, stdout={:?}, stderr={:?}",
            String::from_utf8_lossy(stdout),
            String::from_utf8_lossy(stderr),
        ))
    }
}

fn require_serial_lake_toolchain(files: &BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let Some(bytes) = files.get("lean/lean-toolchain") else {
        return Err("serial proof build requires captured `lean/lean-toolchain` bytes".into());
    };
    let actual = std::str::from_utf8(bytes)
        .map_err(|error| format!("captured `lean/lean-toolchain` is not UTF-8: {error}"))?;
    let actual = actual
        .strip_suffix("\r\n")
        .or_else(|| actual.strip_suffix('\n'))
        .unwrap_or(actual);
    if actual == SERIAL_LAKE_TOOLCHAIN {
        Ok(())
    } else {
        Err(format!(
            "serial proof build has not been audited for captured toolchain `{actual}`; expected `{SERIAL_LAKE_TOOLCHAIN}`"
        ))
    }
}

fn require_closed_lake_manifest(files: &BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let Some(bytes) = files.get("lean/lake-manifest.json") else {
        return Err("proof build requires captured `lean/lake-manifest.json` bytes".into());
    };
    let manifest: serde_json::Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("captured `lean/lake-manifest.json` is invalid: {error}"))?;
    let object = manifest.as_object().ok_or_else(|| {
        "captured `lean/lake-manifest.json` must be one exact JSON object".to_owned()
    })?;
    let expected = serde_json::json!({
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "packages": [],
        "name": "sable",
        "lakeDir": ".lake",
        "fixedToolchain": false,
    });
    if object.len() == 6 && manifest == expected {
        Ok(())
    } else {
        Err(
            "proof builds admit exactly the current dependency-free Lake manifest; package dependencies or manifest layout changes require a reviewed proof-policy update"
                .into(),
        )
    }
}

fn serial_lake_command(lean_dir: &Path) -> Command {
    let mut command = Command::new("lake");
    sanitize_proof_child(&mut command);
    command
        // Lake 5 otherwise reads local artifact caches by default using a
        // compact trace. Proof outputs must be rebuilt from captured sources.
        .env("LAKE_ARTIFACT_CACHE", "false")
        .env("LAKE_RESTORE_ARTIFACTS", "false")
        .env("LAKE_NO_CACHE", "true")
        .env("LAKE_CONFIG", lean_dir.join("sable-lake-config.toml"))
        .env("LEAN_NUM_THREADS", "0")
        .env("LEAN_IMPORT_WORKERS", "1")
        .current_dir(lean_dir);
    command
}

fn sanitize_proof_child(command: &mut Command) {
    for name in PROOF_TOOL_OVERRIDES {
        command.env_remove(name);
    }
}

fn serial_lake_version_command(lean_dir: &Path) -> Command {
    let mut command = serial_lake_command(lean_dir);
    command.arg("--version");
    command
}

fn serial_lake_build_command(lean_dir: &Path) -> Command {
    let mut command = serial_lake_command(lean_dir);
    command.args(["--quiet", "build", "Sable", "sable-proof-audit"]);
    command
}

fn serial_lean_command(lean_dir: &Path) -> Command {
    let mut command = serial_lake_command(lean_dir);
    command.args(["env", "lean", "--json"]);
    command
}

fn serial_proof_auditor_command(lean_dir: &Path, auditor: &Path) -> Command {
    let mut command = serial_lake_command(lean_dir);
    command.args(["env"]).arg(auditor);
    command
}

fn publish_ready(
    built: &Path,
    ready: &Path,
    id: &str,
    proof_policy: &str,
    output_digests: &ProofBuildOutputDigests,
) -> Result<(), String> {
    let temporary = built.join(format!(
        ".READY.tmp.{}.{}",
        std::process::id(),
        NEXT_PROOF_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let result = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .and_then(|mut file| {
            file.write_all(proof_ready_stamp(id, proof_policy, output_digests).as_bytes())?;
            file.sync_all()
        })
        .and_then(|()| std::fs::rename(&temporary, ready));
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result.map_err(|error| {
        format!(
            "cannot publish proof-build readiness {}: {error}",
            ready.display()
        )
    })
}

/// Compatibility helper for callers that only need a fresh tag. Verification
/// paths carry `ProofEnvironment` itself and never rely on before/after hashes.
pub fn proof_environment_fingerprint(repo_root: &Path) -> Result<String, String> {
    ProofEnvironment::capture(repo_root).map(|environment| environment.id)
}

fn proof_environment_dir(repo_root: &Path, id: &str) -> PathBuf {
    repo_root
        .join(".sable-out")
        .join("proof-envs")
        .join(id.replace(':', "_"))
}

fn validate_environment_id(id: &str) -> Result<(), String> {
    let Some(hex) = id.strip_prefix(PROOF_ENVIRONMENT_ID_PREFIX) else {
        return Err(format!("invalid proof-environment id `{id}`"));
    };
    if hex.len() == 16 && hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Ok(())
    } else {
        Err(format!("invalid proof-environment id `{id}`"))
    }
}

fn ensure_proof_environment_dir(repo_root: &Path, id: &str) -> Result<PathBuf, String> {
    validate_environment_id(id)?;
    let output = repo_root.join(".sable-out");
    ensure_local_directory(&output)?;
    let environments = output.join("proof-envs");
    ensure_local_directory(&environments)?;
    let environment = proof_environment_dir(repo_root, id);
    ensure_local_directory(&environment)?;
    Ok(environment)
}

fn validate_proof_environment_dir(repo_root: &Path, id: &str) -> Result<(), String> {
    validate_environment_id(id)?;
    validate_local_directory(&repo_root.join(".sable-out"))?;
    validate_local_directory(&repo_root.join(".sable-out/proof-envs"))?;
    validate_local_directory(&proof_environment_dir(repo_root, id))
}

fn validate_local_directory(path: &Path) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect managed directory {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        Err(format!(
            "managed proof-environment path {} must be a local directory",
            path.display()
        ))
    } else {
        Ok(())
    }
}

fn ensure_local_directory(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => validate_local_directory(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            match std::fs::create_dir(path) {
                Ok(()) => Ok(()),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                    validate_local_directory(path)
                }
                Err(error) => Err(format!(
                    "cannot create managed directory {}: {error}",
                    path.display()
                )),
            }
        }
        Err(error) => Err(format!(
            "cannot inspect managed directory {}: {error}",
            path.display()
        )),
    }
}

fn capture_proof_files(repo_root: &Path) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let root_metadata = std::fs::symlink_metadata(repo_root).map_err(|error| {
        format!(
            "cannot inspect proof snapshot root {}: {error}",
            repo_root.display()
        )
    })?;
    if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
        return Err(format!(
            "proof snapshot root {} must be a local directory",
            repo_root.display()
        ));
    }
    let lean_relative = Path::new("lean");
    let lean_dir = repo_root.join(lean_relative);
    let lean_metadata = std::fs::symlink_metadata(&lean_dir).map_err(|error| {
        format!(
            "cannot inspect proof workspace {}: {error}",
            lean_dir.display()
        )
    })?;
    if lean_metadata.file_type().is_symlink() || !lean_metadata.is_dir() {
        return Err(format!(
            "proof workspace {} must be a repository-local directory",
            lean_dir.display()
        ));
    }

    let mut files = BTreeMap::new();
    for relative in [
        "lean/lean-toolchain",
        "lean/lakefile.toml",
        "lean/lake-manifest.json",
        "lean/sable-lake-config.toml",
        "lean/Sable.lean",
    ] {
        capture_proof_file(repo_root, Path::new(relative), &mut files)?;
    }
    capture_lean_tree(repo_root, lean_relative, &mut files)?;
    Ok(files)
}

fn capture_lean_tree(
    root: &Path,
    relative: &Path,
    files: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let directory_metadata = std::fs::symlink_metadata(&directory).map_err(|error| {
        format!(
            "cannot inspect proof source directory {}: {error}",
            directory.display()
        )
    })?;
    if directory_metadata.file_type().is_symlink() || !directory_metadata.is_dir() {
        return Err(format!(
            "proof source directory {} must be a local directory",
            directory.display()
        ));
    }
    let entries = std::fs::read_dir(&directory).map_err(|error| {
        format!(
            "cannot read proof source directory {}: {error}",
            directory.display()
        )
    })?;
    let mut children = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read an entry in {}: {error}", directory.display()))?;
    children.sort_by_key(std::fs::DirEntry::file_name);
    for child in children {
        if child.file_name().to_str() == Some(".lake") {
            continue;
        }
        let child_relative = relative.join(child.file_name());
        let path = child.path();
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot inspect proof source {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "proof source {} is a symlink; proof snapshots require local regular files",
                path.display()
            ));
        }
        if metadata.is_dir() {
            capture_lean_tree(root, &child_relative, files)?;
        } else if child_relative
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            capture_proof_file(root, &child_relative, files)?;
        }
    }
    Ok(())
}

fn capture_proof_file(
    root: &Path,
    relative: &Path,
    files: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    let label = relative
        .to_str()
        .ok_or_else(|| format!("proof input path {} is not UTF-8", relative.display()))?
        .replace(std::path::MAIN_SEPARATOR, "/");
    let path = root.join(relative);
    let metadata = std::fs::symlink_metadata(&path)
        .map_err(|error| format!("cannot inspect proof input {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "proof input {} must be a repository-local regular file",
            path.display()
        ));
    }
    let bytes = std::fs::read(&path)
        .map_err(|error| format!("cannot read proof input {}: {error}", path.display()))?;
    files.insert(label, bytes);
    Ok(())
}

fn write_proof_files(root: &Path, files: &BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    for (label, bytes) in files {
        let path = root.join(label);
        let parent = path
            .parent()
            .ok_or_else(|| format!("proof input `{label}` has no parent"))?;
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .and_then(|mut file| file.write_all(bytes))
            .map_err(|error| format!("cannot write proof input {}: {error}", path.display()))?;
    }
    Ok(())
}

fn unique_directory(parent: &Path, prefix: &str) -> Result<PathBuf, String> {
    for _ in 0..100 {
        let nonce = NEXT_PROOF_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = parent.join(format!(".{prefix}.{}.{}", std::process::id(), nonce));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
        }
    }
    Err(format!(
        "cannot allocate a unique proof snapshot directory in {}",
        parent.display()
    ))
}

static NEXT_PROOF_TEMP: AtomicU64 = AtomicU64::new(0);

fn remove_unready_built(environment_dir: &Path, built: &Path) -> Result<(), String> {
    if built.parent() != Some(environment_dir)
        || built.file_name().and_then(|name| name.to_str()) != Some("built")
    {
        return Err(format!(
            "refusing to replace out-of-scope proof build {}",
            built.display()
        ));
    }
    let metadata = std::fs::symlink_metadata(built).map_err(|error| {
        format!(
            "cannot inspect incomplete proof build {}: {error}",
            built.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "incomplete proof build {} is not an owned directory",
            built.display()
        ));
    }
    std::fs::remove_dir_all(built).map_err(|error| {
        format!(
            "cannot replace incomplete proof build {}: {error}",
            built.display()
        )
    })
}

fn expected_local_olean_paths(
    files: &BTreeMap<String, Vec<u8>>,
) -> Result<std::collections::BTreeSet<String>, String> {
    for required in ["lean/Sable.lean", "lean/SableProofAudit.lean"] {
        if !files.contains_key(required) {
            return Err(format!(
                "proof environment is missing trusted output root `{required}`"
            ));
        }
    }
    for label in files.keys().filter(|label| label.ends_with(".lean")) {
        if label != "lean/Sable.lean"
            && label != "lean/SableProofAudit.lean"
            && !label.starts_with("lean/Sable/")
        {
            return Err(format!(
                "proof environment contains unsupported Lean source root `{label}`; the trusted output layout is exactly `Sable.lean`, `SableProofAudit.lean`, and `Sable/**`"
            ));
        }
    }
    let expected = files
        .keys()
        .filter(|label| {
            label.as_str() == "lean/Sable.lean"
                || label.as_str() == "lean/SableProofAudit.lean"
                || label.starts_with("lean/Sable/")
        })
        .filter_map(|label| {
            label
                .strip_prefix("lean/")
                .and_then(|label| label.strip_suffix(".lean"))
                .map(|label| format!("{label}.olean"))
        })
        .collect::<std::collections::BTreeSet<_>>();
    if expected.is_empty() {
        Err("proof environment derives no trusted local `.olean` outputs".into())
    } else {
        Ok(expected)
    }
}

fn collect_local_olean_digests(
    root: &Path,
    relative: &Path,
    output: &mut BTreeMap<String, String>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let metadata = std::fs::symlink_metadata(&directory).map_err(|error| {
        format!(
            "cannot inspect local proof-output directory {}: {error}",
            directory.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "local proof-output directory {} is not a local directory",
            directory.display()
        ));
    }
    let mut entries = std::fs::read_dir(&directory)
        .map_err(|error| {
            format!(
                "cannot enumerate local proof outputs in {}: {error}",
                directory.display()
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            format!(
                "cannot enumerate an entry in local proof-output directory {}: {error}",
                directory.display()
            )
        })?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let child_relative = relative.join(entry.file_name());
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot inspect proof output {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "local proof output {} is a symlink",
                path.display()
            ));
        }
        let file_name = child_relative
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("proof output path {} is not UTF-8", path.display()))?;
        if unsupported_proof_output_name(file_name) {
            return Err(format!(
                "unsupported module-system/IR proof output {} would broaden the authenticated proof workspace",
                path.display()
            ));
        }
        if child_relative
            .extension()
            .is_some_and(|extension| extension == "olean")
        {
            if !metadata.is_file() {
                return Err(format!(
                    "local `.olean` proof output {} is not a regular file",
                    path.display()
                ));
            }
            let label = child_relative
                .to_str()
                .ok_or_else(|| format!("proof output path {} is not UTF-8", path.display()))?
                .replace(std::path::MAIN_SEPARATOR, "/");
            let bytes = std::fs::read(&path).map_err(|error| {
                format!("cannot hash local proof output {}: {error}", path.display())
            })?;
            let metadata_after = std::fs::symlink_metadata(&path).map_err(|error| {
                format!(
                    "cannot recheck local proof output {}: {error}",
                    path.display()
                )
            })?;
            if metadata_after.file_type().is_symlink() || !metadata_after.is_file() {
                return Err(format!(
                    "local proof output {} changed kind while being hashed",
                    path.display()
                ));
            }
            output.insert(label, crate::sha256::hex(&bytes));
        } else if metadata.is_dir() {
            collect_local_olean_digests(root, &child_relative, output)?;
        }
    }
    Ok(())
}

fn unsupported_proof_output_name(file_name: &str) -> bool {
    file_name.ends_with(".olean.server")
        || file_name.ends_with(".olean.private")
        || file_name.ends_with(".ir")
}

fn proof_build_output_digests(
    built: &Path,
    files: &BTreeMap<String, Vec<u8>>,
) -> Result<ProofBuildOutputDigests, String> {
    let expected = expected_local_olean_paths(files)?;
    let olean_root = built.join("lean/.lake/build/lib/lean");
    let mut local_olean_sha256 = BTreeMap::new();
    collect_local_olean_digests(&olean_root, Path::new(""), &mut local_olean_sha256)?;
    let actual = local_olean_sha256.keys().cloned().collect();
    if actual != expected {
        let missing = expected.difference(&actual).cloned().collect::<Vec<_>>();
        let unexpected = actual.difference(&expected).cloned().collect::<Vec<_>>();
        return Err(format!(
            "local proof outputs do not exactly match captured Lean sources; missing={missing:?}, unexpected={unexpected:?}"
        ));
    }
    let proof_auditor = proof_auditor_path(built);
    let metadata = std::fs::symlink_metadata(&proof_auditor).map_err(|error| {
        format!(
            "proof build is missing {}: {error}",
            proof_auditor.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "proof build output {} is not a regular file",
            proof_auditor.display()
        ));
    }
    let proof_auditor_bytes = std::fs::read(&proof_auditor).map_err(|error| {
        format!(
            "cannot hash trusted proof build output {}: {error}",
            proof_auditor.display()
        )
    })?;
    let metadata_after = std::fs::symlink_metadata(&proof_auditor).map_err(|error| {
        format!(
            "cannot recheck trusted proof build output {}: {error}",
            proof_auditor.display()
        )
    })?;
    if metadata_after.file_type().is_symlink() || !metadata_after.is_file() {
        return Err(format!(
            "proof build output {} changed kind while being hashed",
            proof_auditor.display()
        ));
    }
    Ok(ProofBuildOutputDigests {
        local_olean_sha256,
        proof_auditor_sha256: crate::sha256::hex(&proof_auditor_bytes),
    })
}

fn proof_auditor_path(built: &Path) -> PathBuf {
    built.join("lean/.lake/build/bin/sable-proof-audit")
}

fn fingerprint_bytes(mut hash: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

struct AdvisoryLock(File);

impl AdvisoryLock {
    fn acquire(path: &Path, description: &str) -> Result<Self, String> {
        if let Ok(metadata) = std::fs::symlink_metadata(path) {
            if metadata.file_type().is_symlink() || !metadata.is_file() {
                return Err(format!(
                    "{description} lock {} must be a local regular file",
                    path.display()
                ));
            }
        }
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)
            .map_err(|error| {
                format!("cannot open {description} lock {}: {error}", path.display())
            })?;
        // This crate's daemon already requires Unix sockets. `flock` keeps a
        // crashed process from leaving a permanent lock-directory tombstone.
        let result = unsafe { process_flock(file.as_raw_fd(), LOCK_EXCLUSIVE) };
        if result != 0 {
            return Err(format!(
                "cannot lock {description} lock {}: {}",
                path.display(),
                std::io::Error::last_os_error()
            ));
        }
        Ok(Self(file))
    }
}

impl Drop for AdvisoryLock {
    fn drop(&mut self) {
        let _ = unsafe { process_flock(self.0.as_raw_fd(), LOCK_UNLOCK) };
    }
}

/// Serialize every owned Lake/Lean/auditor child both between threads in this
/// compiler process and between compiler processes using the same repository.
/// `flock` alone is process-scoped on supported Unix hosts, so the mutex must
/// always be acquired first and held for the full child lifetime.
struct ProofProcessLock {
    _thread: MutexGuard<'static, ()>,
    _process: AdvisoryLock,
}

static PROOF_PROCESS_MUTEX: Mutex<()> = Mutex::new(());

impl ProofProcessLock {
    fn acquire(repo_root: &Path) -> Result<Self, String> {
        let thread = PROOF_PROCESS_MUTEX
            .lock()
            .map_err(|_| "in-process proof-process lock is poisoned".to_owned())?;
        let process = AdvisoryLock::acquire(&proof_process_lock_path(repo_root), "proof-process")?;
        Ok(Self {
            _thread: thread,
            _process: process,
        })
    }
}

fn proof_process_lock_path(repo_root: &Path) -> PathBuf {
    repo_root.join(".sable-out").join("proof-process.lock")
}

const LOCK_EXCLUSIVE: std::os::raw::c_int = 2;
const LOCK_UNLOCK: std::os::raw::c_int = 8;

unsafe extern "C" {
    #[link_name = "flock"]
    fn process_flock(
        fd: std::os::raw::c_int,
        operation: std::os::raw::c_int,
    ) -> std::os::raw::c_int;
}

/// The full search path is derived from the exact READY build and extended
/// only with this checkout's generated artifact directory.
pub fn lean_search_path(
    repo_root: &Path,
    environment: &ProofEnvironment,
) -> Result<String, String> {
    let built = environment.ensure_built(repo_root)?;
    let lean_dir = built.join("lean");
    let _process_lock = ProofProcessLock::acquire(repo_root)?;
    environment.validate_built(&built)?;
    // READY authenticates cached outputs, not the current PATH lookup. Couple
    // every cached Lake workload to the pinned version under the same lock.
    require_serial_lake_version(&lean_dir)?;
    let out = serial_lake_command(&lean_dir)
        // Lake otherwise prepends an ambient LEAN_PATH, which could make an
        // unauthenticated module shadow the content-addressed proof build.
        .env_remove("LEAN_PATH")
        .args(["env", "printenv", "LEAN_PATH"])
        .output()
        .map_err(|err| format!("failed to run `lake env`: {err}"))?;
    if !out.status.success() {
        return Err(format!(
            "`lake env printenv LEAN_PATH` failed with {}: stdout={:?}, stderr={:?}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        ));
    }
    if !out.stderr.is_empty() {
        return Err(format!(
            "`lake env printenv LEAN_PATH` emitted unexpected stderr: {:?}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let stdout = std::str::from_utf8(&out.stdout)
        .map_err(|error| format!("`lake env` LEAN_PATH is not UTF-8: {error}"))?;
    let Some(base) = stdout.strip_suffix('\n') else {
        return Err("`lake env` LEAN_PATH must be exactly one newline-terminated line".into());
    };
    if base.is_empty() || base.contains(['\n', '\r']) {
        return Err("`lake env` LEAN_PATH must be exactly one nonempty line".into());
    }
    environment.validate_built(&built)?;
    Ok(format!("{base}:{}", modules_dir(repo_root).display()))
}

#[derive(Debug)]
pub(crate) struct IngressAuditFailure {
    pub(crate) span: Span,
    pub(crate) description: String,
    pub(crate) message: String,
}

fn ingress_transport_failure(emitted: &Emitted, message: impl Into<String>) -> IngressAuditFailure {
    let (span, description) = emitted.ingress.first().map_or(
        (Span::new(0, 0), "generated Lean document".to_owned()),
        |fragment| (fragment.span, fragment.description.clone()),
    );
    IngressAuditFailure {
        span,
        description,
        message: message.into(),
    }
}

/// Authenticate every compiler-recorded user-derived parser boundary using
/// the content-hashed trusted auditor. Candidate generated modules are not
/// imported by this mode; the auditor loads extensions only from `Sable`.
pub(crate) fn audit_ingress(
    repo_root: &Path,
    environment: &ProofEnvironment,
    emitted: &Emitted,
) -> Result<(), IngressAuditFailure> {
    let request = serde_json::json!({
        "schema": "sable-proof-ingress-request-v1",
        "fragments": emitted.ingress.iter().map(|fragment| serde_json::json!({
            "category": fragment.category,
            "text": &fragment.text,
            "expected_kind": fragment.expected_kind,
            "expected_name": &fragment.expected_name,
        })).collect::<Vec<_>>(),
    });
    let request = serde_json::to_vec(&request).map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!("cannot encode the exact proof-ingress request: {error}"),
        )
    })?;
    let built = environment
        .ensure_built(repo_root)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    environment
        .validate_built(&built)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    let auditor = proof_auditor_path(&built);
    let metadata = std::fs::symlink_metadata(&auditor).map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!(
                "cannot inspect proof auditor {}: {error}",
                auditor.display()
            ),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(ingress_transport_failure(
            emitted,
            format!("proof auditor {} is not a regular file", auditor.display()),
        ));
    }
    let _process_lock = ProofProcessLock::acquire(repo_root)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    environment
        .validate_built(&built)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    let lean_dir = built.join("lean");
    require_serial_lake_version(&lean_dir)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    let mut command = serial_proof_auditor_command(&lean_dir, &auditor);
    let mut child = command
        // Lake prepends the authenticated workspace search path. The only
        // inherited addition is Sable's content-addressed generated modules.
        .env("LEAN_PATH", modules_dir(repo_root))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| {
            ingress_transport_failure(
                emitted,
                format!("failed to run proof-ingress auditor: {error}"),
            )
        })?;
    let write_result = child
        .stdin
        .take()
        .ok_or_else(|| "proof-ingress auditor stdin pipe is unavailable".to_owned())
        .and_then(|mut stdin| {
            stdin
                .write_all(&request)
                .map_err(|error| format!("cannot write proof-ingress request: {error}"))
        });
    if let Err(message) = write_result {
        let _ = child.kill();
        let _ = child.wait();
        return Err(ingress_transport_failure(emitted, message));
    }
    let output = child.wait_with_output().map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!("cannot wait for proof-ingress auditor: {error}"),
        )
    })?;
    environment
        .validate_built(&built)
        .map_err(|message| ingress_transport_failure(emitted, message))?;
    parse_ingress_audit_output(
        emitted,
        output.status.success(),
        &output.stdout,
        &output.stderr,
    )
}

fn parse_ingress_audit_output(
    emitted: &Emitted,
    status_success: bool,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<(), IngressAuditFailure> {
    let stdout = std::str::from_utf8(stdout).map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!("proof auditor stdout is not UTF-8: {error}"),
        )
    })?;
    let stderr = std::str::from_utf8(stderr).map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!("proof auditor stderr is not UTF-8: {error}"),
        )
    })?;
    if !status_success || !stderr.is_empty() {
        return Err(ingress_transport_failure(
            emitted,
            format!(
                "proof auditor transport failed: status_success={status_success}, stdout={stdout:?}, stderr={stderr:?}"
            ),
        ));
    }
    let Some(line) = stdout.strip_suffix('\n') else {
        return Err(ingress_transport_failure(
            emitted,
            "proof auditor stdout must be exactly one newline-terminated JSON result",
        ));
    };
    if line.is_empty() || line.contains('\n') || line.contains('\r') {
        return Err(ingress_transport_failure(
            emitted,
            "proof auditor stdout must contain exactly one JSON line",
        ));
    }
    let value: serde_json::Value = serde_json::from_str(line).map_err(|error| {
        ingress_transport_failure(
            emitted,
            format!("proof auditor result is not valid JSON: {error}"),
        )
    })?;
    let object = value.as_object().ok_or_else(|| {
        ingress_transport_failure(emitted, "proof auditor result must be a JSON object")
    })?;
    if object.get("schema").and_then(serde_json::Value::as_str)
        != Some("sable-proof-ingress-result-v1")
    {
        return Err(ingress_transport_failure(
            emitted,
            "proof auditor result has the wrong or missing schema",
        ));
    }
    let accepted = object
        .get("accepted")
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| {
            ingress_transport_failure(
                emitted,
                "proof auditor result lacks a Boolean `accepted` field",
            )
        })?;
    if accepted {
        if object.len() == 2 {
            return Ok(());
        }
        return Err(ingress_transport_failure(
            emitted,
            "accepted proof auditor result contains unknown fields",
        ));
    }
    let failure_kind = object
        .get("failure_kind")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            ingress_transport_failure(
                emitted,
                "rejected proof auditor result lacks `failure_kind`",
            )
        })?;
    let message = object
        .get("message")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            ingress_transport_failure(emitted, "rejected proof auditor result lacks `message`")
        })?;
    if failure_kind == "fragment" {
        if object.len() != 5 {
            return Err(ingress_transport_failure(
                emitted,
                "fragment rejection has missing or unknown fields",
            ));
        }
        let index = object
            .get("index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|index| usize::try_from(index).ok())
            .filter(|index| *index < emitted.ingress.len())
            .ok_or_else(|| {
                ingress_transport_failure(
                    emitted,
                    "fragment rejection has an invalid or out-of-range index",
                )
            })?;
        let fragment = &emitted.ingress[index];
        return Err(IngressAuditFailure {
            span: fragment.span,
            description: fragment.description.clone(),
            message: message.to_owned(),
        });
    }
    if object.len() != 4 {
        return Err(ingress_transport_failure(
            emitted,
            "auditor/request rejection has missing or unknown fields",
        ));
    }
    if !matches!(failure_kind, "transport" | "request" | "auditor") {
        return Err(ingress_transport_failure(
            emitted,
            "proof auditor result has an unsupported `failure_kind`",
        ));
    }
    Err(ingress_transport_failure(
        emitted,
        format!("proof auditor rejected its {failure_kind} boundary: {message}"),
    ))
}

/// Check a generated file against an immutable proof build. With `olean_out`,
/// additionally compile it into an importable generated-module artifact.
pub fn run_lean(
    repo_root: &Path,
    environment: &ProofEnvironment,
    lean_file: &Path,
    olean_out: Option<&Path>,
    expected_source: &str,
) -> Result<Vec<LeanMessage>, String> {
    let built = environment.ensure_built(repo_root)?;
    let lean_dir = built.join("lean");
    require_generated_source(lean_file, expected_source, "before Lean checking")?;

    let mut cmd = serial_lean_command(&lean_dir);
    // `lake env` prepends the authenticated proof workspace; generated
    // dependency modules are the only inherited addition.
    cmd.env("LEAN_PATH", modules_dir(repo_root));
    if let Some(olean) = olean_out {
        cmd.arg("--root")
            .arg(modules_dir(repo_root))
            .arg("-o")
            .arg(olean);
    }
    let _process_lock = ProofProcessLock::acquire(repo_root)?;
    environment.validate_built(&built)?;
    require_serial_lake_version(&lean_dir)?;
    let output = cmd
        .arg(lean_file)
        .output()
        .map_err(|err| format!("failed to run `lean`: {err}"))?;
    environment.validate_built(&built)?;
    require_generated_source(lean_file, expected_source, "while Lean was checking")?;

    let messages = parse_lean_output(&output.stdout, &output.stderr)?;

    // A failing process must also provide a structured Lean error, not merely
    // a nonzero status after otherwise well-formed transport.
    if !output.status.success() && messages.iter().all(|m| m.severity != "error") {
        return Err(format!(
            "lean exited with {} but produced no error messages:\n{}",
            output.status,
            std::str::from_utf8(&output.stdout)
                .expect("parse_lean_output already authenticated stdout as UTF-8"),
        ));
    }

    Ok(messages)
}

pub(crate) fn supported_diagnostic_severity(severity: &str) -> bool {
    matches!(severity, "error" | "warning" | "information")
}

pub(crate) fn parse_lean_output(stdout: &[u8], stderr: &[u8]) -> Result<Vec<LeanMessage>, String> {
    let stdout = std::str::from_utf8(stdout)
        .map_err(|error| format!("Lean stdout is not valid UTF-8: {error}"))?;
    let stderr = std::str::from_utf8(stderr)
        .map_err(|error| format!("Lean stderr is not valid UTF-8: {error}"))?;
    if !stderr.is_empty() {
        return Err(format!(
            "Lean emitted unexpected stderr outside its JSON diagnostic channel:\n{stderr}"
        ));
    }

    let mut messages = Vec::new();
    for (output_line, raw) in stdout.lines().enumerate() {
        if raw.is_empty() {
            continue;
        }
        let line = raw;
        let value = serde_json::from_str::<serde_json::Value>(line).map_err(|error| {
            format!(
                "Lean stdout line {} is not a JSON diagnostic: {error}: {line}",
                output_line + 1
            )
        })?;
        let severity = value
            .get("severity")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| {
                format!(
                    "Lean JSON diagnostic on stdout line {} lacks a string `severity`",
                    output_line + 1
                )
            })?;
        if !supported_diagnostic_severity(severity) {
            return Err(format!(
                "Lean JSON diagnostic on stdout line {} has unsupported severity `{severity}`",
                output_line + 1
            ));
        }
        let source_line = value
            .get("pos")
            .and_then(|position| position.get("line"))
            .and_then(serde_json::Value::as_u64)
            .and_then(|line| usize::try_from(line).ok())
            .ok_or_else(|| {
                format!(
                    "Lean JSON diagnostic on stdout line {} lacks an unsigned, in-range `pos.line`",
                    output_line + 1
                )
            })?;
        let data = value
            .get("data")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| {
                format!(
                    "Lean JSON diagnostic on stdout line {} lacks string `data`",
                    output_line + 1
                )
            })?;
        messages.push(LeanMessage {
            severity: severity.to_owned(),
            line: source_line,
            data: data.to_owned(),
        });
    }
    Ok(messages)
}

#[cfg(test)]
mod lean_output_policy_tests {
    use super::parse_lean_output;

    #[test]
    fn batch_transport_accepts_only_structured_known_diagnostics() {
        let stdout = concat!(
            "{\"severity\":\"error\",\"pos\":{\"line\":3},\"data\":\"bad proof\"}\n",
            "{\"severity\":\"warning\",\"pos\":{\"line\":4},\"data\":\"warning\"}\n",
            "{\"severity\":\"information\",\"pos\":{\"line\":5},\"data\":\"Try this:\"}\n",
        );
        let messages = parse_lean_output(stdout.as_bytes(), b"")
            .expect("all three owned Lean diagnostic severities are structured");
        assert_eq!(messages.len(), 3);
        assert_eq!(messages[0].severity, "error");
        assert_eq!(messages[0].line, 3);
        assert_eq!(messages[0].data, "bad proof");
        assert_eq!(messages[2].severity, "information");
        assert!(parse_lean_output(b"\n\n", b"").unwrap().is_empty());
    }

    #[test]
    fn batch_transport_rejects_lossy_or_unclassified_output() {
        assert!(parse_lean_output(&[0xff], b"").is_err());
        assert!(parse_lean_output(b"", &[0xff]).is_err());
        assert!(parse_lean_output(b"", b"warning outside JSON\n").is_err());

        for stdout in [
            b"Lean chatter\n".as_slice(),
            b"  \n".as_slice(),
            b"{not-json}\n".as_slice(),
            b"{}\n".as_slice(),
            b"{\"severity\":7,\"pos\":{\"line\":1},\"data\":\"x\"}\n".as_slice(),
            b"{\"severity\":\"hint\",\"pos\":{\"line\":1},\"data\":\"x\"}\n".as_slice(),
            b"{\"severity\":\"warning\",\"pos\":{},\"data\":\"x\"}\n".as_slice(),
            b"{\"severity\":\"warning\",\"pos\":{\"line\":-1},\"data\":\"x\"}\n".as_slice(),
            b"{\"severity\":\"warning\",\"pos\":{\"line\":1},\"data\":{}}\n".as_slice(),
        ] {
            assert!(
                parse_lean_output(stdout, b"").is_err(),
                "unclassified transport unexpectedly passed: {:?}",
                String::from_utf8_lossy(stdout)
            );
        }
    }
}

fn require_generated_source(path: &Path, expected: &str, phase: &str) -> Result<(), String> {
    let actual = std::fs::read_to_string(path).map_err(|error| {
        format!(
            "cannot read generated Lean file {}: {error}",
            path.display()
        )
    })?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "generated Lean file {} changed {phase}; retry the check",
            path.display()
        ))
    }
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
            Some(MapTarget::Certificate(i)) => {
                let certificate = &vc.transition_certificates[*i];
                diags.push(Diagnostic {
                    name: certificate.rejection_diagnostic_name().into(),
                    title: format!(
                        "Lean rejected {} transition certificate `{}`",
                        certificate.description(),
                        certificate.name
                    ),
                    span: certificate.span(),
                    label: certificate.rejection_label(),
                    notes: vec![
                        (
                            "certificate".into(),
                            format!(
                                "goal: {}\nthis fixed-proof theorem cannot be deferred, \
                                 assumed, or replaced by a user discharge",
                                certificate.lean_goal()
                            ),
                        ),
                        ("lean".into(), msg.data.clone()),
                    ],
                });
            }
            Some(MapTarget::ArgumentScheduleCertificate(i)) => {
                let certificate = &vc.argument_schedule_certificates[*i];
                diags.push(Diagnostic {
                    name: certificate.rejection_diagnostic_name().into(),
                    title: format!(
                        "Lean rejected {} certificate `{}`",
                        certificate.description(),
                        certificate.name
                    ),
                    span: certificate.span,
                    label: certificate.rejection_label(),
                    notes: vec![
                        (
                            "certificate".into(),
                            format!(
                                "goal: {}\nthis closed theorem cannot be deferred, assumed, \
                                 or replaced by a user discharge",
                                certificate.lean_goal()
                            ),
                        ),
                        ("lean".into(), msg.data.clone()),
                    ],
                });
            }
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

const EXPENSIVE_AUTOMATION_PREFIX: &str = "expensive automation: `grind` closed this goal using ";
const EXPENSIVE_AUTOMATION_MIDDLE: &str = "k of its ";
const EXPENSIVE_AUTOMATION_BUDGET_END: &str = "k-heartbeat budget — ";
const EXPENSIVE_AUTOMATION_SUGGESTED_END: &str =
    "a minimized `discharge` suggestion accompanies this warning";
const EXPENSIVE_AUTOMATION_SCRIPT_END: &str = "consider a `discharge` script";

fn compact_message_whitespace(message: &str) -> String {
    message.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Recognize the exact warning grammar emitted by `sable_grind`. Merely
/// containing the words "expensive automation" is not authority to survive
/// the warning gate: the measured and configured budgets must parse and obey
/// the threshold enforced by `lean/Sable/Auto.lean`.
fn is_expensive_automation_warning_text(message: &str) -> bool {
    let message = compact_message_whitespace(message);
    let Some(rest) = message.strip_prefix(EXPENSIVE_AUTOMATION_PREFIX) else {
        return false;
    };
    let Some((spent, rest)) = rest.split_once(EXPENSIVE_AUTOMATION_MIDDLE) else {
        return false;
    };
    let Some((budget, ending)) = rest.split_once(EXPENSIVE_AUTOMATION_BUDGET_END) else {
        return false;
    };
    let (Ok(spent), Ok(budget)) = (spent.parse::<u64>(), budget.parse::<u64>()) else {
        return false;
    };
    budget > 0
        && spent <= budget
        && u128::from(spent) * 5 >= u128::from(budget)
        && matches!(
            ending,
            EXPENSIVE_AUTOMATION_SUGGESTED_END | EXPENSIVE_AUTOMATION_SCRIPT_END
        )
}

fn is_recognized_warning(emitted: &Emitted, message: &LeanMessage) -> bool {
    if message.severity != "warning" || !is_expensive_automation_warning_text(&message.data) {
        return false;
    }
    emitted
        .map
        .iter()
        .find(|entry| entry.first_line <= message.line && message.line <= entry.last_line)
        .is_some_and(|entry| {
            matches!(
                entry.target,
                MapTarget::Obligation(_) | MapTarget::Discharged { .. }
            )
        })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DiagnosticDisposition {
    Ignore,
    ReportExpensiveAutomation,
    FatalUnexpected,
}

fn diagnostic_disposition(emitted: &Emitted, message: &LeanMessage) -> DiagnosticDisposition {
    if matches!(message.severity.as_str(), "error" | "information") {
        DiagnosticDisposition::Ignore
    } else if is_recognized_warning(emitted, message) {
        DiagnosticDisposition::ReportExpensiveAutomation
    } else {
        DiagnosticDisposition::FatalUnexpected
    }
}

fn warning_span(entry: Option<&MapEntry>, vc: &VcResult) -> Span {
    match entry.map(|entry| &entry.target) {
        Some(MapTarget::Clause { span, .. } | MapTarget::Discharged { span, .. }) => *span,
        Some(MapTarget::Certificate(index)) => vc
            .transition_certificates
            .get(*index)
            .map_or(Span::new(0, 0), |certificate| certificate.span()),
        Some(MapTarget::ArgumentScheduleCertificate(index)) => vc
            .argument_schedule_certificates
            .get(*index)
            .map_or(Span::new(0, 0), |certificate| certificate.span),
        Some(MapTarget::Obligation(index)) => vc
            .obligations
            .get(*index)
            .map_or(Span::new(0, 0), |obligation| obligation.span),
        None => Span::new(0, 0),
    }
}

/// Reject every Lean warning except the exact compiler-owned expensive-
/// automation diagnostic. In particular, Lean's warning for a declaration
/// containing `sorryAx` is fatal even though Lean exits successfully.
pub fn diagnose_unexpected_warnings(
    emitted: &Emitted,
    vc: &VcResult,
    messages: &[LeanMessage],
) -> Vec<Diagnostic> {
    messages
        .iter()
        // Errors are mapped by `diagnose`; structurally parsed information is
        // retained for `grind?` suggestions. Every other diagnostic severity
        // must be the one explicitly recognized warning below.
        .filter(|message| {
            diagnostic_disposition(emitted, message) == DiagnosticDisposition::FatalUnexpected
        })
        .map(|message| {
            let entry = emitted
                .map
                .iter()
                .find(|entry| entry.first_line <= message.line && message.line <= entry.last_line);
            Diagnostic {
                name: UNEXPECTED_LEAN_WARNING_DIAGNOSTIC.into(),
                title: format!(
                    "Lean emitted an unrecognized `{}` diagnostic",
                    message.severity
                ),
                span: warning_span(entry, vc),
                label: "verification fails closed on unrecognized Lean warnings".into(),
                notes: vec![
                    (
                        "lean".into(),
                        format!("line {}: {}", message.line, message.data),
                    ),
                    (
                        "policy".into(),
                        "only Sable's structured expensive-automation warning is non-fatal".into(),
                    ),
                ],
            }
        })
        .collect()
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
        if diagnostic_disposition(emitted, msg) != DiagnosticDisposition::ReportExpensiveAutomation
        {
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

#[cfg(test)]
mod warning_policy_tests {
    use super::{
        DiagnosticDisposition, Emitted, EmittedNames, LeanMessage, MapEntry, MapTarget,
        UNEXPECTED_LEAN_WARNING_DIAGNOSTIC, diagnostic_disposition,
        is_expensive_automation_warning_text, is_recognized_warning,
    };

    #[test]
    fn expensive_automation_warning_requires_the_exact_structured_shape() {
        for ending in [
            "a minimized `discharge` suggestion accompanies this warning",
            "consider a `discharge` script",
        ] {
            assert!(is_expensive_automation_warning_text(&format!(
                "expensive automation: `grind` closed this goal using 20k of its \
                 100k-heartbeat budget — {ending}"
            )));
        }

        for rejected in [
            "declaration uses 'sorry'",
            "expensive automation",
            "expensive automation: `grind` closed this goal using many of its 100k-heartbeat budget — consider a `discharge` script",
            "expensive automation: `grind` closed this goal using 19k of its 100k-heartbeat budget — consider a `discharge` script",
            "expensive automation: `grind` closed this goal using 101k of its 100k-heartbeat budget — consider a `discharge` script",
            "expensive automation: `grind` closed this goal using 20k of its 100k-heartbeat budget — consider a `discharge` script (forged suffix)",
        ] {
            assert!(
                !is_expensive_automation_warning_text(rejected),
                "{rejected}"
            );
        }
    }

    #[test]
    fn warning_exception_requires_owned_severity_and_source_target() {
        assert_eq!(
            UNEXPECTED_LEAN_WARNING_DIAGNOSTIC,
            "proof.unexpected_lean_warning"
        );
        let emitted = Emitted {
            lean_source: String::new(),
            names: EmittedNames::default(),
            ingress: Vec::new(),
            map: vec![MapEntry {
                first_line: 7,
                last_line: 9,
                target: MapTarget::Obligation(0),
            }],
        };
        let exact = LeanMessage {
            severity: "warning".into(),
            line: 8,
            data: "expensive automation: `grind` closed this goal using 20k of its \
                   100k-heartbeat budget — consider a `discharge` script"
                .into(),
        };
        assert!(is_recognized_warning(&emitted, &exact));

        let outside_owned_target = LeanMessage {
            severity: exact.severity.clone(),
            line: 10,
            data: exact.data.clone(),
        };
        assert!(!is_recognized_warning(&emitted, &outside_owned_target));
        let unknown_severity = LeanMessage {
            severity: "hint".into(),
            line: exact.line,
            data: exact.data,
        };
        assert!(!is_recognized_warning(&emitted, &unknown_severity));
    }

    #[test]
    fn allowed_expensive_warning_cannot_mask_a_sorry_warning() {
        let emitted = Emitted {
            lean_source: String::new(),
            names: EmittedNames::default(),
            ingress: Vec::new(),
            map: vec![MapEntry {
                first_line: 7,
                last_line: 9,
                target: MapTarget::Obligation(0),
            }],
        };
        let allowed = LeanMessage {
            severity: "warning".into(),
            line: 8,
            data: "expensive automation: `grind` closed this goal using 20k of its \
                   100k-heartbeat budget — consider a `discharge` script"
                .into(),
        };
        let sorry = LeanMessage {
            severity: "warning".into(),
            line: 8,
            data: "declaration uses 'sorry'".into(),
        };
        assert_eq!(
            diagnostic_disposition(&emitted, &allowed),
            DiagnosticDisposition::ReportExpensiveAutomation
        );
        assert_eq!(
            diagnostic_disposition(&emitted, &sorry),
            DiagnosticDisposition::FatalUnexpected
        );
        assert_eq!(
            [&allowed, &sorry]
                .into_iter()
                .filter(|message| {
                    diagnostic_disposition(&emitted, message)
                        == DiagnosticDisposition::FatalUnexpected
                })
                .count(),
            1
        );
    }
}

/// Deduplicate: one obligation can produce several lean messages.
pub fn dedup_by_name(diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen = std::collections::HashSet::new();
    diags
        .into_iter()
        .filter(|d| seen.insert((d.name.clone(), d.span.start)))
        .collect()
}

#[cfg(test)]
mod proof_build_tests {
    use super::*;
    use std::ffi::OsStr;

    struct TempProofTree(PathBuf);

    impl Drop for TempProofTree {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn emitted_with_ingress() -> Emitted {
        Emitted {
            lean_source: String::new(),
            names: EmittedNames::default(),
            ingress: vec![
                IngressFragment::term("True", Span::new(2, 3), "first fragment"),
                IngressFragment::term("False", Span::new(7, 11), "second fragment"),
            ],
            map: Vec::new(),
        }
    }

    #[test]
    fn comment_metadata_is_byte_exact_ascii_on_one_line() {
        assert_eq!(comment_hex("safe"), "73616665");
        assert_eq!(
            comment_hex("line\ncarriage\rnull\0unit\u{1f}é"),
            "6c696e650a63617272696167650d6e756c6c00756e69741fc3a9"
        );
        for byte in comment_hex("\n\r\0\u{1f}").bytes() {
            assert!(byte.is_ascii_hexdigit());
        }
    }

    #[test]
    fn generated_doc_metadata_cannot_change_comment_nesting() {
        let safe = doc_safe("source /- nested -/ then -/ escaped /- again");
        assert!(!safe.contains("/-"));
        assert!(!safe.contains("-/"));
        assert_eq!(safe, "source / - nested - / then - / escaped / - again");
    }

    #[test]
    fn ghost_identity_keeps_lean_apostrophes() {
        assert_eq!(
            ghost_head_name("emod_nonneg' (x m : Int) : True := True.intro"),
            "emod_nonneg'"
        );
        assert_eq!(
            ghost_head_name("  ordinary_name : Nat := 0"),
            "ordinary_name"
        );
    }

    #[test]
    fn ingress_auditor_transport_accepts_only_the_exact_result_schema() {
        let emitted = emitted_with_ingress();
        let accepted = b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":true}\n";
        parse_ingress_audit_output(&emitted, true, accepted, b"")
            .expect("the exact accepted result passes");

        for stdout in [
            b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":true}".as_slice(),
            b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":true}\r\n".as_slice(),
            b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":true,\"extra\":0}\n"
                .as_slice(),
            b"ok\n".as_slice(),
        ] {
            assert!(parse_ingress_audit_output(&emitted, true, stdout, b"").is_err());
        }
        assert!(parse_ingress_audit_output(&emitted, false, accepted, b"").is_err());
        assert!(parse_ingress_audit_output(&emitted, true, accepted, b"warning\n").is_err());
        let forged_kind = b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":false,\"failure_kind\":\"forged\",\"message\":\"accepted by loose parser\"}\n";
        assert!(parse_ingress_audit_output(&emitted, true, forged_kind, b"").is_err());
    }

    #[test]
    fn dependency_and_module_system_outputs_require_a_policy_review() {
        let exact_manifest = include_bytes!("../../lean/lake-manifest.json").to_vec();
        let exact = BTreeMap::from([("lean/lake-manifest.json".into(), exact_manifest)]);
        require_closed_lake_manifest(&exact)
            .expect("the captured dependency-free manifest is the admitted workspace");

        for manifest in [
            serde_json::json!({
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": [{"name": "unreviewed"}],
                "name": "sable",
                "lakeDir": ".lake",
                "fixedToolchain": false,
            }),
            serde_json::json!({
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": [],
                "name": "sable",
                "lakeDir": ".lake",
                "fixedToolchain": false,
                "unknown": true,
            }),
        ] {
            let files = BTreeMap::from([(
                "lean/lake-manifest.json".into(),
                serde_json::to_vec(&manifest).expect("test manifest serializes"),
            )]);
            assert!(require_closed_lake_manifest(&files).is_err());
        }
        assert!(require_closed_lake_manifest(&BTreeMap::new()).is_err());

        for rejected in [
            "Sable.olean.server",
            "Sable.olean.private",
            "Sable.ir",
            "nested.ir",
        ] {
            assert!(unsupported_proof_output_name(rejected));
        }
        for admitted in ["Sable.olean", "Sable.ilean", "Sable.c", "Sable.o"] {
            assert!(!unsupported_proof_output_name(admitted));
        }
    }

    #[test]
    fn proof_output_digest_walk_requires_the_exact_regular_output_set() {
        let built = unique_directory(&std::env::temp_dir(), "sable-proof-output-test")
            .expect("create isolated proof-output tree");
        let _cleanup = TempProofTree(built.clone());
        let olean_root = built.join("lean/.lake/build/lib/lean");
        let auditor = proof_auditor_path(&built);
        std::fs::create_dir_all(olean_root.join("Sable"))
            .expect("create nested proof-output directory");
        std::fs::create_dir_all(auditor.parent().expect("auditor has a parent"))
            .expect("create auditor output directory");
        std::fs::write(olean_root.join("Sable.olean"), b"root olean").expect("write root olean");
        std::fs::write(
            olean_root.join("SableProofAudit.olean"),
            b"auditor library olean",
        )
        .expect("write auditor library olean");
        std::fs::write(olean_root.join("Sable/Fixture.olean"), b"fixture olean")
            .expect("write nested olean");
        std::fs::write(&auditor, b"native auditor").expect("write native auditor");

        let files = BTreeMap::from([
            ("lean/Sable.lean".into(), b"import Sable.Fixture".to_vec()),
            ("lean/SableProofAudit.lean".into(), b"import Sable".to_vec()),
            (
                "lean/Sable/Fixture.lean".into(),
                b"def fixture := 0".to_vec(),
            ),
        ]);
        let exact = proof_build_output_digests(&built, &files)
            .expect("the exact regular output set is accepted");
        assert_eq!(
            exact.local_olean_sha256.keys().cloned().collect::<Vec<_>>(),
            [
                "Sable.olean",
                "Sable/Fixture.olean",
                "SableProofAudit.olean"
            ]
        );

        std::fs::remove_file(olean_root.join("Sable/Fixture.olean"))
            .expect("remove expected nested olean");
        assert!(
            proof_build_output_digests(&built, &files)
                .expect_err("a missing local olean fails closed")
                .contains("missing")
        );
        std::fs::write(olean_root.join("Sable/Fixture.olean"), b"fixture olean")
            .expect("restore expected nested olean");

        std::fs::write(olean_root.join("Unexpected.olean"), b"unexpected")
            .expect("write unexpected local olean");
        assert!(
            proof_build_output_digests(&built, &files)
                .expect_err("an unexpected local olean fails closed")
                .contains("unexpected")
        );
        std::fs::remove_file(olean_root.join("Unexpected.olean"))
            .expect("remove unexpected local olean");

        std::fs::write(olean_root.join("Sable.ir"), b"unsupported ir")
            .expect("write unsupported IR output");
        assert!(
            proof_build_output_digests(&built, &files)
                .expect_err("an unsupported module-system output fails closed")
                .contains("unsupported module-system/IR proof output")
        );
        std::fs::remove_file(olean_root.join("Sable.ir")).expect("remove unsupported IR output");

        std::fs::remove_file(olean_root.join("Sable.olean")).expect("remove regular root olean");
        std::fs::create_dir(olean_root.join("Sable.olean"))
            .expect("replace root olean with a directory");
        assert!(
            proof_build_output_digests(&built, &files)
                .expect_err("a nonregular olean fails closed")
                .contains("not a regular file")
        );
    }

    #[test]
    fn ingress_auditor_rejection_maps_only_an_authenticated_fragment_index() {
        let emitted = emitted_with_ingress();
        let rejection = b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":false,\"failure_kind\":\"fragment\",\"message\":\"escaped parser boundary\",\"index\":1}\n";
        let failure = parse_ingress_audit_output(&emitted, true, rejection, b"")
            .expect_err("fragment rejection fails closed");
        assert_eq!(failure.span, Span::new(7, 11));
        assert_eq!(failure.description, "second fragment");
        assert_eq!(failure.message, "escaped parser boundary");

        let out_of_range = b"{\"schema\":\"sable-proof-ingress-result-v1\",\"accepted\":false,\"failure_kind\":\"fragment\",\"message\":\"forged\",\"index\":2}\n";
        let failure = parse_ingress_audit_output(&emitted, true, out_of_range, b"")
            .expect_err("an out-of-range diagnostic index fails as transport evidence");
        assert_eq!(failure.span, Span::new(2, 3));
        assert_eq!(failure.description, "first fragment");
    }

    fn assert_serial_lake_command_base(command: &Command, lean_dir: &Path) {
        assert_eq!(command.get_program(), OsStr::new("lake"));
        assert_eq!(command.get_current_dir(), Some(lean_dir));
        let envs = command.get_envs().collect::<Vec<_>>();
        assert!(envs.contains(&(OsStr::new("LEAN_IMPORT_WORKERS"), Some(OsStr::new("1")))));
        assert!(envs.contains(&(OsStr::new("LEAN_NUM_THREADS"), Some(OsStr::new("0")))));
        assert!(envs.contains(&(OsStr::new("LAKE_ARTIFACT_CACHE"), Some(OsStr::new("false")))));
        assert!(envs.contains(&(
            OsStr::new("LAKE_RESTORE_ARTIFACTS"),
            Some(OsStr::new("false"))
        )));
        assert!(envs.contains(&(OsStr::new("LAKE_NO_CACHE"), Some(OsStr::new("true")))));
        let lake_config = lean_dir.join("sable-lake-config.toml");
        assert!(envs.contains(&(OsStr::new("LAKE_CONFIG"), Some(lake_config.as_os_str()),)));
        for name in PROOF_TOOL_OVERRIDES {
            assert!(
                envs.contains(&(OsStr::new(name), None)),
                "proof workload command must remove ambient override {name}"
            );
        }
        assert_eq!(envs.len(), PROOF_TOOL_OVERRIDES.len() + 6);
    }

    #[test]
    fn fresh_and_cached_workload_commands_pin_one_environment_and_trusted_targets() {
        let lean_dir = Path::new("proof-environment/lean");
        let version = serial_lake_version_command(lean_dir);
        assert_serial_lake_command_base(&version, lean_dir);
        assert_eq!(
            version.get_args().collect::<Vec<_>>(),
            ["--version"].iter().map(OsStr::new).collect::<Vec<_>>()
        );

        let build = serial_lake_build_command(lean_dir);
        assert_serial_lake_command_base(&build, lean_dir);
        assert_eq!(
            build.get_args().collect::<Vec<_>>(),
            ["--quiet", "build", "Sable", "sable-proof-audit"]
                .iter()
                .map(OsStr::new)
                .collect::<Vec<_>>()
        );

        let lean = serial_lean_command(lean_dir);
        assert_serial_lake_command_base(&lean, lean_dir);
        assert_eq!(
            lean.get_args().collect::<Vec<_>>(),
            ["env", "lean", "--json"]
                .iter()
                .map(OsStr::new)
                .collect::<Vec<_>>()
        );

        let auditor_path = Path::new("proof-environment/lean/.lake/build/bin/sable-proof-audit");
        let auditor = serial_proof_auditor_command(lean_dir, auditor_path);
        assert_serial_lake_command_base(&auditor, lean_dir);
        assert_eq!(
            auditor.get_args().collect::<Vec<_>>(),
            [OsStr::new("env"), auditor_path.as_os_str()]
        );
    }

    #[test]
    fn serial_lake_version_parser_authenticates_one_exact_clean_line() {
        for stdout in [
            SERIAL_LAKE_VERSION.as_bytes().to_vec(),
            format!("{SERIAL_LAKE_VERSION}\n").into_bytes(),
            format!("{SERIAL_LAKE_VERSION}\r\n").into_bytes(),
        ] {
            validate_serial_lake_version(true, &stdout, b"")
                .expect("the exact audited Lake and Lean version must pass");
        }

        for (status_success, stdout, stderr) in [
            (false, SERIAL_LAKE_VERSION.as_bytes(), b"".as_slice()),
            (
                true,
                b"Lake version 5.0.0-src+other (Lean version 4.32.2)".as_slice(),
                b"".as_slice(),
            ),
            (
                true,
                b"Lake version 5.0.0-src+f3b06c7 (Lean version 4.33.0)".as_slice(),
                b"".as_slice(),
            ),
            (
                true,
                SERIAL_LAKE_VERSION.as_bytes(),
                b"unexpected warning\n".as_slice(),
            ),
        ] {
            assert!(
                validate_serial_lake_version(status_success, stdout, stderr).is_err(),
                "status, stdout, and stderr must all match the audited preflight"
            );
        }

        let extra_line = format!("{SERIAL_LAKE_VERSION}\nextra\n");
        assert!(validate_serial_lake_version(true, extra_line.as_bytes(), b"").is_err());
    }

    #[test]
    fn serial_lake_build_output_fails_closed_on_every_message() {
        let lean_dir = Path::new("proof-environment/lean");
        validate_serial_lake_build_output(true, b"", b"", lean_dir, "exit status: 0")
            .expect("an exact silent successful build is accepted");

        for (status_success, stdout, stderr) in [
            (false, b"".as_slice(), b"".as_slice()),
            (
                true,
                b"warning: declaration uses sorry\n".as_slice(),
                b"".as_slice(),
            ),
            (true, b"build message\n".as_slice(), b"".as_slice()),
            (true, b"".as_slice(), b"warning on stderr\n".as_slice()),
        ] {
            assert!(
                validate_serial_lake_build_output(
                    status_success,
                    stdout,
                    stderr,
                    lean_dir,
                    if status_success {
                        "exit status: 0"
                    } else {
                        "exit status: 1"
                    },
                )
                .is_err(),
                "a failed or noisy proof-environment build must not publish READY"
            );
        }
    }

    #[test]
    fn proof_environment_identity_binds_warning_policy_and_rejects_old_domains() {
        let files = BTreeMap::from([
            (
                "lean/lean-toolchain".into(),
                b"leanprover/lean4:v4.32.2\n".to_vec(),
            ),
            ("lean/Sable.lean".into(), b"import Sable.Auto\n".to_vec()),
        ]);
        let current = proof_environment_id(&files, PROOF_POLICY_VERSION);
        assert!(current.starts_with(PROOF_ENVIRONMENT_ID_PREFIX));
        let environment =
            ProofEnvironment::from_files(files.clone()).expect("nonempty captured environment");
        assert_eq!(environment.id(), current);
        assert_eq!(environment.policy(), PROOF_POLICY_VERSION);
        assert_ne!(
            current,
            proof_environment_id(&files, "accept-lean-warnings-legacy")
        );
        assert!(ProofEnvironment::from_files_with_policy(files.clone(), "").is_err());
        assert!(ProofEnvironment::from_files_with_policy(files.clone(), "policy\nforged").is_err());
        validate_environment_id(&current).expect("the current v4 identity is loadable");
        assert!(
            validate_environment_id("proof-env-v2-fnv64:0123456789abcdef").is_err(),
            "an old READY/prelude workspace must not be loadable under the new policy"
        );
        assert!(
            validate_environment_id("proof-env-v3-fnv64:0123456789abcdef").is_err(),
            "the pre-final warning-policy workspace must remain unreachable"
        );

        assert!(proof_policy_marker_matches(
            Some(proof_policy_marker(PROOF_POLICY_VERSION).as_bytes()),
            PROOF_POLICY_VERSION,
        ));
        assert!(!proof_policy_marker_matches(
            Some(proof_policy_marker("accept-lean-warnings-legacy").as_bytes()),
            PROOF_POLICY_VERSION,
        ));
        assert!(
            !proof_policy_marker_matches(None, PROOF_POLICY_VERSION),
            "a published source snapshot with no exact policy marker fails closed"
        );
        let output_digests = ProofBuildOutputDigests {
            local_olean_sha256: BTreeMap::from([
                (
                    "Sable.olean".into(),
                    crate::sha256::hex(b"exact Sable.olean"),
                ),
                (
                    "SableProofAudit.olean".into(),
                    crate::sha256::hex(b"exact auditor olean"),
                ),
            ]),
            proof_auditor_sha256: crate::sha256::hex(b"exact proof auditor"),
        };
        let exact_ready = proof_ready_stamp(&current, PROOF_POLICY_VERSION, &output_digests);
        assert!(proof_ready_stamp_matches(
            exact_ready.as_bytes(),
            &current,
            PROOF_POLICY_VERSION,
            &output_digests,
        ));
        assert!(
            !proof_ready_stamp_matches(
                format!("{current}\n").as_bytes(),
                &current,
                PROOF_POLICY_VERSION,
                &output_digests,
            ),
            "legacy existence-only READY evidence must not be reusable"
        );
        assert!(
            !proof_ready_stamp_matches(
                proof_ready_stamp(&current, "accept-lean-warnings-legacy", &output_digests,)
                    .as_bytes(),
                &current,
                PROOF_POLICY_VERSION,
                &output_digests,
            ),
            "even an id collision cannot hide an exact policy mismatch"
        );
        let swapped = ProofBuildOutputDigests {
            local_olean_sha256: BTreeMap::from([
                (
                    "Sable.olean".into(),
                    output_digests.proof_auditor_sha256.clone(),
                ),
                (
                    "SableProofAudit.olean".into(),
                    output_digests.local_olean_sha256["Sable.olean"].clone(),
                ),
            ]),
            proof_auditor_sha256: output_digests.local_olean_sha256["SableProofAudit.olean"]
                .clone(),
        };
        assert!(
            !proof_ready_stamp_matches(
                exact_ready.as_bytes(),
                &current,
                PROOF_POLICY_VERSION,
                &swapped,
            ),
            "READY binds each trusted output to its role, not just a digest set"
        );
        assert!(
            !proof_ready_stamp_matches(
                exact_ready
                    .replace("sable-proof-ready-v2", "sable-proof-ready-v1")
                    .as_bytes(),
                &current,
                PROOF_POLICY_VERSION,
                &output_digests,
            ),
            "old READY schemas fail closed"
        );
        assert!(
            !proof_ready_stamp_matches(
                format!("{exact_ready}unknown-field:forged\n").as_bytes(),
                &current,
                PROOF_POLICY_VERSION,
                &output_digests,
            ),
            "unknown or duplicate READY data fails the exact-byte comparison"
        );
    }

    #[test]
    fn serial_lake_scheduler_fails_closed_outside_the_audited_toolchain() {
        for bytes in [
            b"leanprover/lean4:v4.32.2".as_slice(),
            b"leanprover/lean4:v4.32.2\n".as_slice(),
            b"leanprover/lean4:v4.32.2\r\n".as_slice(),
        ] {
            let files = BTreeMap::from([("lean/lean-toolchain".into(), bytes.to_vec())]);
            require_serial_lake_toolchain(&files)
                .expect("the pinned Lean 4.32.2 runtime has audited zero-worker semantics");
        }

        let wrong = BTreeMap::from([(
            "lean/lean-toolchain".into(),
            b"leanprover/lean4:v4.33.0\n".to_vec(),
        )]);
        assert!(
            require_serial_lake_toolchain(&wrong)
                .expect_err("an unaudited runtime must fail before Lake starts")
                .contains("has not been audited")
        );
        assert!(
            require_serial_lake_toolchain(&BTreeMap::new())
                .expect_err("missing toolchain bytes must fail before Lake starts")
                .contains("requires captured")
        );
    }

    #[test]
    fn obsolete_package_configuration_override_cannot_return() {
        let source = include_str!("lean.rs");
        let obsolete_argument = ["-K", "jobs", "=", "1"].concat();
        assert!(
            !source.contains(&obsolete_argument),
            "a package configuration override is not a Lake scheduler bound"
        );
    }
}

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
use std::collections::{BTreeMap, BTreeSet};
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

/// Ordered compiler-authored declaration roots expected from one generated
/// module. This is deliberately separate from [`EmittedNames`]: the latter is
/// import-subtraction metadata, while this carrier preserves declaration kind,
/// source order, and the structural roots needed by the compiled-envelope
/// auditor in the next tranche. Recording it grants no cache authority: B0
/// does not yet compare these roots or their bodies with a candidate `.olean`.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedDeclarationEnvelope {
    pub(crate) roots: Vec<ExpectedDeclarationRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedDeclarationRoot {
    pub(crate) name: String,
    pub(crate) kind: ExpectedDeclarationKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExpectedDeclarationKind {
    Structure {
        fields: Vec<String>,
    },
    Definition {
        recursive: bool,
        noncomputable: bool,
        simp: bool,
    },
    Theorem {
        simp: bool,
        sable_fact: bool,
    },
    /// Compiler-authored final command. It is an identity/inventory canary,
    /// not an attestation that cached declaration bodies came from source.
    TerminalSentinel,
}

pub(crate) const DECLARATION_AUDIT_SUBJECT_SCHEMA: &str = "sable-declaration-audit-subject-v1";

/// Exact source-side identity of one generated Lean module. The final source
/// digest and full typed envelope make cache-hit reconstruction lossless; this
/// value does not authenticate any `.olean` or grant reuse authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationModuleSubject {
    pub(crate) module_name: String,
    pub(crate) generated_source_sha256: String,
    pub(crate) declaration_envelope: ExpectedDeclarationEnvelope,
}

/// Canonical source-side subject for the future compiled-declaration auditor.
/// Dependencies remain in exact emitted import order and retain their complete
/// declaration envelopes. B1a deliberately omits candidate/dependency `.olean`
/// digests, replay results, and accepted evidence, so these bytes are neither a
/// transport request nor cache authority yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationAuditSubject {
    pub(crate) schema: &'static str,
    pub(crate) proof_environment_id: String,
    pub(crate) proof_policy: String,
    pub(crate) candidate: DeclarationModuleSubject,
    pub(crate) dependencies: Vec<DeclarationModuleSubject>,
}

impl DeclarationAuditSubject {
    pub(crate) fn new(
        proof_environment_id: impl Into<String>,
        proof_policy: impl Into<String>,
        candidate: DeclarationModuleSubject,
        dependencies: Vec<DeclarationModuleSubject>,
    ) -> Self {
        Self {
            schema: DECLARATION_AUDIT_SUBJECT_SCHEMA,
            proof_environment_id: proof_environment_id.into(),
            proof_policy: proof_policy.into(),
            candidate,
            dependencies,
        }
    }

    /// Compact JSON over struct fields and ordered vectors is the single
    /// canonical serialization. No maps or platform paths enter the subject.
    pub(crate) fn canonical_json(&self) -> Vec<u8> {
        let mut json = String::new();
        json.push_str("{\"schema\":");
        push_json_string(&mut json, self.schema);
        json.push_str(",\"proof_environment_id\":");
        push_json_string(&mut json, &self.proof_environment_id);
        json.push_str(",\"proof_policy\":");
        push_json_string(&mut json, &self.proof_policy);
        json.push_str(",\"candidate\":");
        self.candidate.push_canonical_json(&mut json);
        json.push_str(",\"dependencies\":[");
        for (index, dependency) in self.dependencies.iter().enumerate() {
            if index != 0 {
                json.push(',');
            }
            dependency.push_canonical_json(&mut json);
        }
        json.push_str("]}");
        json.into_bytes()
    }
}

fn push_json_string(output: &mut String, value: &str) {
    output.push_str(
        &serde_json::to_string(value).expect("serializing a Rust string to JSON cannot fail"),
    );
}

impl DeclarationModuleSubject {
    fn push_canonical_json(&self, output: &mut String) {
        output.push_str("{\"module_name\":");
        push_json_string(output, &self.module_name);
        output.push_str(",\"generated_source_sha256\":");
        push_json_string(output, &self.generated_source_sha256);
        output.push_str(",\"declaration_envelope\":");
        self.declaration_envelope.push_canonical_json(output);
        output.push('}');
    }
}

impl ExpectedDeclarationEnvelope {
    fn push_canonical_json(&self, output: &mut String) {
        output.push_str("{\"roots\":[");
        for (index, root) in self.roots.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            root.push_canonical_json(output);
        }
        output.push_str("]}");
    }
}

impl ExpectedDeclarationRoot {
    fn push_canonical_json(&self, output: &mut String) {
        output.push_str("{\"name\":");
        push_json_string(output, &self.name);
        match &self.kind {
            ExpectedDeclarationKind::Structure { fields } => {
                output.push_str(",\"kind\":\"structure\",\"fields\":[");
                for (index, field) in fields.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    push_json_string(output, field);
                }
                output.push(']');
            }
            ExpectedDeclarationKind::Definition {
                recursive,
                noncomputable,
                simp,
            } => {
                output.push_str(",\"kind\":\"definition\",\"recursive\":");
                output.push_str(if *recursive { "true" } else { "false" });
                output.push_str(",\"noncomputable\":");
                output.push_str(if *noncomputable { "true" } else { "false" });
                output.push_str(",\"simp\":");
                output.push_str(if *simp { "true" } else { "false" });
            }
            ExpectedDeclarationKind::Theorem { simp, sable_fact } => {
                output.push_str(",\"kind\":\"theorem\",\"simp\":");
                output.push_str(if *simp { "true" } else { "false" });
                output.push_str(",\"sable_fact\":");
                output.push_str(if *sable_fact { "true" } else { "false" });
            }
            ExpectedDeclarationKind::TerminalSentinel => {
                output.push_str(",\"kind\":\"terminal_sentinel\"");
            }
        }
        output.push('}');
    }
}

impl ExpectedDeclarationEnvelope {
    fn push_structure(&mut self, name: String, fields: Vec<String>) {
        self.roots.push(ExpectedDeclarationRoot {
            name,
            kind: ExpectedDeclarationKind::Structure { fields },
        });
    }

    fn push_proof_definition(&mut self, name: String, recursive: bool, simp: bool) {
        self.roots.push(ExpectedDeclarationRoot {
            name,
            kind: ExpectedDeclarationKind::Definition {
                recursive,
                noncomputable: true,
                simp,
            },
        });
    }

    fn push_theorem(&mut self, name: String, simp: bool, sable_fact: bool) {
        self.roots.push(ExpectedDeclarationRoot {
            name,
            kind: ExpectedDeclarationKind::Theorem { simp, sable_fact },
        });
    }

    fn push_terminal_sentinel(&mut self, name: String) {
        self.roots.push(ExpectedDeclarationRoot {
            name,
            kind: ExpectedDeclarationKind::TerminalSentinel,
        });
    }
}

pub struct Emitted {
    pub lean_source: String,
    /// What this file declares (after exclusion filtering).
    pub names: EmittedNames,
    /// Exact user-derived Lean fragments whose parser boundaries must be
    /// authenticated before this document may be submitted to Lean.
    pub(crate) ingress: Vec<IngressFragment>,
    pub(crate) declaration_envelope: ExpectedDeclarationEnvelope,
    map: Vec<MapEntry>,
}

impl DeclarationModuleSubject {
    pub(crate) fn from_emitted(module_name: impl Into<String>, emitted: &Emitted) -> Self {
        Self {
            module_name: module_name.into(),
            generated_source_sha256: crate::sha256::hex(emitted.lean_source.as_bytes()),
            declaration_envelope: emitted.declaration_envelope.clone(),
        }
    }
}

/// Generated content before its module name is known. The artifact name is
/// derived from these bytes; [`EmittedDraft::finish`] then appends the unique
/// terminal sentinel without introducing a source/name hash cycle.
pub struct EmittedDraft {
    lean_source: String,
    names: EmittedNames,
    ingress: Vec<IngressFragment>,
    declaration_envelope: ExpectedDeclarationEnvelope,
    map: Vec<MapEntry>,
}

impl EmittedDraft {
    pub fn lean_source(&self) -> &str {
        &self.lean_source
    }

    pub fn finish(mut self, module_name: &str) -> Emitted {
        let sentinel = terminal_sentinel_name(module_name, &self.lean_source);
        debug_assert!(self.lean_source.ends_with('\n'));
        self.lean_source
            .push_str(&format!("theorem {sentinel} : True := True.intro\n"));
        self.declaration_envelope.push_terminal_sentinel(sentinel);
        Emitted {
            lean_source: self.lean_source,
            names: self.names,
            ingress: self.ingress,
            declaration_envelope: self.declaration_envelope,
            map: self.map,
        }
    }
}

const TERMINAL_SENTINEL_DOMAIN: &[u8] = b"sable-generated-terminal-sentinel-v1";

fn terminal_sentinel_name(module_name: &str, pre_sentinel_source: &str) -> String {
    let mut framed = Vec::with_capacity(
        TERMINAL_SENTINEL_DOMAIN.len() + module_name.len() + pre_sentinel_source.len() + 24,
    );
    append_framed(&mut framed, TERMINAL_SENTINEL_DOMAIN);
    append_framed(&mut framed, module_name.as_bytes());
    append_framed(&mut framed, pre_sentinel_source.as_bytes());
    format!("SableGenerated.complete_{}", crate::sha256::hex(&framed))
}

fn append_framed(output: &mut Vec<u8>, value: &[u8]) {
    let len = u64::try_from(value.len()).expect("generated Lean input length fits u64");
    output.extend_from_slice(&len.to_be_bytes());
    output.extend_from_slice(value);
}

const INGRESS_REQUEST_SCHEMA: &str = "sable-proof-ingress-request-v2";
const INGRESS_RESULT_SCHEMA: &str = "sable-proof-ingress-result-v2";
const DECLARATION_INVENTORY_REQUEST_SCHEMA: &str = "sable-declaration-inventory-request-v1";
const DECLARATION_INVENTORY_RESULT_SCHEMA: &str = "sable-declaration-inventory-result-v1";
const DECLARATION_OBSERVATION_SCHEMA: &str = "sable-declaration-observation-v1";

/// Exact recursive Lean `Name` identity. Printable names are insufficient for
/// hygienic components, so the transport preserves anonymous/str/num shape.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ObservedName {
    Anonymous,
    Str {
        prefix: Box<ObservedName>,
        value: String,
    },
    Num {
        prefix: Box<ObservedName>,
        value: u64,
    },
}

/// Observed header flags for one direct import in serialized `ModuleData`.
/// This records bytes produced by Lean; it does not authenticate the imported
/// module or make the candidate acceptable.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObservedModuleImport {
    pub(crate) module: ObservedName,
    pub(crate) import_all: bool,
    pub(crate) is_exported: bool,
    pub(crate) is_meta: bool,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObservedConstantKind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quotient,
    Inductive,
    Constructor,
    Recursor,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObservedConstantSafety {
    Safe,
    Unsafe,
    Partial,
}

/// One index in the parallel `ModuleData.constNames`/`constants` arrays.
/// Either side may be absent so malformed unequal arrays remain observable
/// rather than being silently truncated by `zip`.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObservedConstantSlot {
    pub(crate) const_name: Option<ObservedName>,
    pub(crate) info_name: Option<ObservedName>,
    pub(crate) kind: Option<ObservedConstantKind>,
    pub(crate) safety: Option<ObservedConstantSafety>,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObservedExtensionFamily {
    pub(crate) name: ObservedName,
    pub(crate) count: usize,
}

/// Strictly parsed, observational output from `Lean.readModuleData`.
/// No candidate declarations have been imported, replayed, or accepted, and
/// this value must never authorize cache reuse or raise proof assurance.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationModuleInventory {
    pub(crate) observational: bool,
    pub(crate) is_module: bool,
    pub(crate) imports: Vec<ObservedModuleImport>,
    pub(crate) constants: Vec<ObservedConstantSlot>,
    pub(crate) extra_const_names: Vec<ObservedName>,
    pub(crate) extension_families: Vec<ObservedExtensionFamily>,
}

/// Source-side role of one explicit declaration that the coarse inventory
/// preflight can match by exact structural name and `ConstantInfo` kind.
/// These roles deliberately do not claim body, type, attribute, or ownership
/// correspondence.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclarationInventoryExplicitRole {
    StructureRoot {
        root_index: usize,
    },
    DefinitionRoot {
        root_index: usize,
    },
    TheoremRoot {
        root_index: usize,
    },
    TerminalSentinel {
        root_index: usize,
    },
    StructureField {
        root_index: usize,
        field_index: usize,
    },
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationInventoryExplicitMatch {
    pub(crate) role: DeclarationInventoryExplicitRole,
    pub(crate) name: ObservedName,
    pub(crate) slot_index: usize,
    pub(crate) kind: ObservedConstantKind,
}

/// One candidate-local constant not covered by the explicit source envelope.
/// Its Lean safety bit is known to be `safe`, but that is not a declaration-
/// policy verdict: the constant remains wholly unclassified.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationInventoryUnclassifiedConstant {
    pub(crate) name: ObservedName,
    pub(crate) slot_index: usize,
    pub(crate) kind: ObservedConstantKind,
}

/// Coarse, denial-only result over one already-bound raw inventory. Success
/// means only that the narrow rejection rules ran and the explicit names had
/// compatible top-level kinds. It is never candidate acceptance and grants no
/// cache or proof authority; every unmatched constant stays visible below.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationInventoryPreflight {
    pub(crate) observational: bool,
    pub(crate) authoritative: bool,
    pub(crate) explicit_matches: Vec<DeclarationInventoryExplicitMatch>,
    pub(crate) unclassified_constants: Vec<DeclarationInventoryUnclassifiedConstant>,
}

/// An opaque, compiler-owned path reserved for a future freshly compiled
/// declaration-observation candidate. The dormant compound helper writes it
/// only as an ephemeral input to inventory; it is never published and the path
/// itself grants no authority.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct DeclarationCandidateOlean {
    expected_module_name: String,
    directory: PathBuf,
    path: PathBuf,
}

#[cfg_attr(not(test), allow(dead_code))]
impl DeclarationCandidateOlean {
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for DeclarationCandidateOlean {
    fn drop(&mut self) {
        // Remove only exact regular files Lean may derive from the owned `-o`
        // path. Traditional generated modules produce just `.olean`; a future
        // `module` source may also attempt server/private/IR sidecars, which
        // this tranche rejects but must still clean without following links.
        for path in declaration_candidate_output_paths(self) {
            if std::fs::symlink_metadata(&path)
                .is_ok_and(|metadata| !metadata.file_type().is_symlink() && metadata.is_file())
            {
                let _ = std::fs::remove_file(path);
            }
        }
        if std::fs::symlink_metadata(&self.directory)
            .is_ok_and(|metadata| !metadata.file_type().is_symlink() && metadata.is_dir())
        {
            let _ = std::fs::remove_dir(&self.directory);
        }
    }
}

fn declaration_candidate_output_paths(candidate: &DeclarationCandidateOlean) -> [PathBuf; 4] {
    let mut server = candidate.path.as_os_str().to_owned();
    server.push(".server");
    let mut private = candidate.path.as_os_str().to_owned();
    private.push(".private");
    [
        candidate.path.clone(),
        PathBuf::from(server),
        PathBuf::from(private),
        candidate.path.with_extension("ir"),
    ]
}

/// Compiler-owned temporary source directory whose exact `<module>.lean` file
/// gives Lean the expected module name under an explicit `--root`. The source
/// and directory are removed only when they retain the narrow owned shape;
/// unexpected residual files are deliberately left visible and rejected.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, PartialEq, Eq)]
struct DeclarationCandidateSource {
    expected_module_name: String,
    directory: PathBuf,
    path: PathBuf,
}

impl Drop for DeclarationCandidateSource {
    fn drop(&mut self) {
        if std::fs::symlink_metadata(&self.path)
            .is_ok_and(|metadata| !metadata.file_type().is_symlink() && metadata.is_file())
        {
            let _ = std::fs::remove_file(&self.path);
        }
        // `remove_dir` is intentionally nonrecursive and succeeds only when no
        // unmodeled compiler output or replacement entry remains.
        if std::fs::symlink_metadata(&self.directory)
            .is_ok_and(|metadata| !metadata.file_type().is_symlink() && metadata.is_dir())
        {
            let _ = std::fs::remove_dir(&self.directory);
        }
    }
}

/// In-memory binding between one exact source-side subject and one stable raw
/// `ModuleData` observation. It is deliberately non-authoritative: no field
/// attests declaration bodies, imports the candidate, authorizes cache reuse,
/// or raises proof assurance. In particular, `expected_module_name` comes from
/// the source subject; `readModuleData` does not authenticate a module name.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationModuleObservation {
    schema: &'static str,
    observational: bool,
    authoritative: bool,
    expected_module_name: String,
    proof_environment_id: String,
    proof_policy: String,
    declaration_subject: DeclarationAuditSubject,
    declaration_subject_json: Vec<u8>,
    declaration_subject_sha256: String,
    proof_ready_bytes: Vec<u8>,
    proof_ready_sha256_before: String,
    proof_ready_sha256_after: String,
    candidate_olean_sha256_before: String,
    candidate_olean_sha256_after: String,
    inventory_request: Vec<u8>,
    inventory_request_sha256: String,
    inventory_result: Vec<u8>,
    inventory_result_sha256: String,
    inventory: DeclarationModuleInventory,
}

/// Dormant one-workload result that binds strict batch compilation to the raw
/// declaration inventory. It remains observational and non-authoritative:
/// the temporary candidate is deleted before this value reaches its caller,
/// and no cache, manifest, publication, or proof-assurance path consumes it.
/// The nonce-bearing absolute source path may affect Lean metadata or bytes,
/// so its candidate digest is specifically not a final-artifact identity.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompiledDeclarationObservation {
    observational: bool,
    authoritative: bool,
    ephemeral_source_root: PathBuf,
    ephemeral_source_path: PathBuf,
    ephemeral_candidate_root: PathBuf,
    ephemeral_candidate_path: PathBuf,
    source_sha256_before: String,
    source_sha256_after_compile: String,
    source_sha256_after_inventory: String,
    lean_stdout: Vec<u8>,
    lean_stdout_sha256: String,
    lean_messages: Vec<LeanMessage>,
    declaration: DeclarationModuleObservation,
    inventory_preflight: DeclarationInventoryPreflight,
}

#[cfg_attr(not(test), allow(dead_code))]
impl DeclarationModuleObservation {
    /// Exact, framed-by-fields evidence bytes for later policy work. The full
    /// source subject, READY bytes, request, and result are retained alongside
    /// their SHA-256 digests; this in-memory encoding is not an accepted
    /// manifest and is never consulted by cache reuse.
    pub(crate) fn canonical_json(&self) -> Vec<u8> {
        debug_assert_eq!(self.schema, DECLARATION_OBSERVATION_SCHEMA);
        debug_assert!(self.observational);
        debug_assert!(!self.authoritative);
        debug_assert_eq!(
            self.declaration_subject.canonical_json(),
            self.declaration_subject_json
        );

        let ready = std::str::from_utf8(&self.proof_ready_bytes)
            .expect("validated proof READY bytes remain UTF-8");
        let request = std::str::from_utf8(&self.inventory_request)
            .expect("compiler-authored declaration inventory request remains UTF-8");
        let result = std::str::from_utf8(&self.inventory_result)
            .expect("strictly parsed declaration inventory result remains UTF-8");
        let subject = std::str::from_utf8(&self.declaration_subject_json)
            .expect("compiler-authored declaration subject remains UTF-8");

        let mut json = String::new();
        json.push_str("{\"schema\":");
        push_json_string(&mut json, self.schema);
        json.push_str(",\"observational\":true,\"authoritative\":false");
        json.push_str(",\"expected_module_name\":");
        push_json_string(&mut json, &self.expected_module_name);
        json.push_str(",\"proof_environment_id\":");
        push_json_string(&mut json, &self.proof_environment_id);
        json.push_str(",\"proof_policy\":");
        push_json_string(&mut json, &self.proof_policy);
        json.push_str(",\"declaration_audit_subject\":");
        json.push_str(subject);
        json.push_str(",\"declaration_audit_subject_sha256\":");
        push_json_string(&mut json, &self.declaration_subject_sha256);
        json.push_str(",\"proof_ready_utf8\":");
        push_json_string(&mut json, ready);
        json.push_str(",\"proof_ready_sha256_before\":");
        push_json_string(&mut json, &self.proof_ready_sha256_before);
        json.push_str(",\"proof_ready_sha256_after\":");
        push_json_string(&mut json, &self.proof_ready_sha256_after);
        json.push_str(",\"candidate_olean_sha256_before\":");
        push_json_string(&mut json, &self.candidate_olean_sha256_before);
        json.push_str(",\"candidate_olean_sha256_after\":");
        push_json_string(&mut json, &self.candidate_olean_sha256_after);
        json.push_str(",\"inventory_request_utf8\":");
        push_json_string(&mut json, request);
        json.push_str(",\"inventory_request_sha256\":");
        push_json_string(&mut json, &self.inventory_request_sha256);
        json.push_str(",\"inventory_result_utf8\":");
        push_json_string(&mut json, result);
        json.push_str(",\"inventory_result_sha256\":");
        push_json_string(&mut json, &self.inventory_result_sha256);
        json.push('}');
        json.into_bytes()
    }

    pub(crate) fn canonical_sha256(&self) -> String {
        crate::sha256::hex(&self.canonical_json())
    }
}

#[derive(Clone)]
pub(crate) struct IngressFragment {
    category: &'static str,
    text: String,
    expected_kind: &'static str,
    expected_name: String,
    expected_modifiers: String,
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
            expected_modifiers: String::new(),
            span,
            description: description.into(),
        }
    }

    fn command(
        text: impl Into<String>,
        expected_kind: &'static str,
        expected_name: impl Into<String>,
        expected_modifiers: impl Into<String>,
        span: Span,
        description: impl Into<String>,
    ) -> Self {
        Self {
            category: "command",
            text: text.into(),
            expected_kind,
            expected_name: expected_name.into(),
            expected_modifiers: expected_modifiers.into(),
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
) -> EmittedDraft {
    let mut e = Emitter {
        buf: String::new(),
        line: 0,
    };
    let mut map = Vec::new();
    let mut names = EmittedNames::default();
    let mut ingress = Vec::new();
    let mut declaration_envelope = ExpectedDeclarationEnvelope::default();

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
        declaration_envelope.push_structure(
            lean_name.clone(),
            r.fields
                .iter()
                .map(|field| format!("{lean_name}.{}", field.name))
                .collect(),
        );
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
        declaration_envelope.push_proof_definition(format!("{lean_name}.layout"), false, false);
        e.push(&format!(
            "noncomputable def layout : Sable.Layout := ⟨{}, {}⟩",
            r.layout.size, r.layout.align
        ));
        declaration_envelope.push_theorem(format!("{lean_name}.layout_size"), true, false);
        e.push(&format!(
            "@[simp] theorem layout_size : layout.size = {} := rfl",
            r.layout.size
        ));
        declaration_envelope.push_theorem(format!("{lean_name}.layout_align"), true, false);
        e.push(&format!(
            "@[simp] theorem layout_align : layout.align = {} := rfl",
            r.layout.align
        ));
        for field in &r.fields {
            declaration_envelope.push_proof_definition(
                format!("{lean_name}.{}Offset", field.name),
                false,
                false,
            );
            e.push(&format!(
                "noncomputable def {}Offset : Int := {}",
                field.name, field.offset
            ));
        }
        let mut exponent = 0u32;
        let mut align = r.layout.align;
        while align > 1 {
            align /= 2;
            exponent += 1;
        }
        declaration_envelope.push_theorem(format!("{lean_name}.layout_wf"), false, false);
        e.push("theorem layout_wf : layout.wf := by");
        e.push(&format!(
            "  refine ⟨by decide, by decide, ⟨{exponent}, rfl⟩⟩"
        ));
        for field in &r.fields {
            declaration_envelope.push_theorem(
                format!("{lean_name}.{}_fits", field.name),
                false,
                false,
            );
            e.push(&format!(
                "theorem {}_fits : Sable.Layout.fieldFits layout {} {}Offset := by simp [Sable.Layout.fieldFits, layout, {}Offset, {}]",
                field.name, field.layout, field.name, field.name, field.layout
            ));
        }
        for left in 0..r.fields.len() {
            for right in (left + 1)..r.fields.len() {
                let lfield = &r.fields[left];
                let rfield = &r.fields[right];
                declaration_envelope.push_theorem(
                    format!("{lean_name}.{}_{}_disjoint", lfield.name, rfield.name),
                    false,
                    false,
                );
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
        declaration_envelope.push_proof_definition(format!("{lean_name}.wf"), false, false);
        e.push(&format!(
            "noncomputable def wf (value : {lean_name}) : Prop :="
        ));
        e.push(&format!("  {wf_body}"));
        // A plain `def` is invisible to `simp`; the explicit unfolding
        // lemma is what lets automation read the field facts out of a
        // `wf` hypothesis (an elementwise array fact included).
        declaration_envelope.push_theorem(format!("{lean_name}.wf_iff"), true, false);
        e.push(&format!(
            "@[simp] theorem wf_iff (value : {lean_name}) : wf value ↔ ({wf_body}) := Iff.rfl"
        ));
        declaration_envelope.push_proof_definition(format!("{lean_name}.cellWf"), false, false);
        e.push(&format!(
            "noncomputable def cellWf (cell : Sable.PointsToView {lean_name}) : Prop :="
        ));
        e.push("  cell.layout = layout ∧ 0 ≤ cell.off ∧ cell.off % cell.layout.align = 0 ∧");
        e.push("    match cell.state with | .uninit => True | .init value => wf value");
        declaration_envelope.push_proof_definition(format!("{lean_name}.fromSpan"), false, false);
        e.push(&format!(
            "noncomputable def fromSpan (span : Sable.SpanView) : Sable.PointsToView {lean_name} :="
        ));
        e.push("  { alloc := span.alloc, off := span.off, layout := layout, state := .uninit }");
        for theorem in [
            "fromSpan_alloc",
            "fromSpan_off",
            "fromSpan_layout",
            "fromSpan_state",
        ] {
            declaration_envelope.push_theorem(format!("{lean_name}.{theorem}"), true, false);
        }
        e.push("@[simp] theorem fromSpan_alloc (span : Sable.SpanView) : (fromSpan span).alloc = span.alloc := rfl");
        e.push("@[simp] theorem fromSpan_off (span : Sable.SpanView) : (fromSpan span).off = span.off := rfl");
        e.push("@[simp] theorem fromSpan_layout (span : Sable.SpanView) : (fromSpan span).layout = layout := rfl");
        e.push("@[simp] theorem fromSpan_state (span : Sable.SpanView) : (fromSpan span).state = .uninit := rfl");
        declaration_envelope.push_proof_definition(format!("{lean_name}.toSpan"), false, false);
        e.push(&format!(
            "noncomputable def toSpan (cell : Sable.PointsToView {lean_name}) : Sable.SpanView :="
        ));
        e.push("  { alloc := cell.alloc, off := cell.off, len := cell.layout.size,");
        e.push("    bytes := ⟨cell.layout.size, fun _ => .init 0⟩ }");
        for theorem in ["toSpan_alloc", "toSpan_off", "toSpan_len"] {
            declaration_envelope.push_theorem(format!("{lean_name}.{theorem}"), true, false);
        }
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
        names.classes.insert(lean_name.clone());
        declaration_envelope.push_structure(
            lean_name.clone(),
            c.fields
                .iter()
                .map(|(field, _)| format!("{lean_name}.{field}"))
                .collect(),
        );
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
        let recursive = g.keyword == "def" && ghost_recursive(&g.text);
        let simp = g.unfold || (g.keyword == "def" && !recursive);
        let mut attr = String::new();
        if simp {
            attr.push_str("@[simp] ");
        }
        // `#[fact]`: the instantiation tier applies the theorem at the
        // argument tuples occurring in each obligation.
        if g.fact {
            attr.push_str("@[sable_fact] ");
        }
        let (command, expected_modifiers) = if g.keyword == "def" {
            declaration_envelope.push_proof_definition(head.clone(), recursive, simp);
            (
                format!("{attr}noncomputable def {}", g.text),
                format!("{attr}noncomputable "),
            )
        } else {
            declaration_envelope.push_theorem(head.clone(), simp, g.fact);
            (format!("{attr}theorem {}", g.text), attr)
        };
        ingress.push(IngressFragment::command(
            command.clone(),
            if g.keyword == "def" {
                "definition"
            } else {
                "theorem"
            },
            head.clone(),
            expected_modifiers,
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
        declaration_envelope.push_proof_definition(wf.def_name.clone(), false, false);
        e.push(&format!(
            "noncomputable def {} {} : {} :=",
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
        declaration_envelope.push_theorem(certificate.thm_name.clone(), false, false);
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
        declaration_envelope.push_theorem(certificate.thm_name.clone(), false, false);
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
        declaration_envelope.push_theorem(ob.thm_name.clone(), false, false);
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

    EmittedDraft {
        lean_source: e.buf,
        names,
        ingress,
        declaration_envelope,
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

fn require_generated_module_name(module_name: &str) -> Result<(), String> {
    if module_name.is_empty()
        || module_name
            .bytes()
            .next()
            .is_some_and(|byte| byte.is_ascii_digit())
        || !module_name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    {
        return Err(format!(
            "declaration observation expected module name `{module_name}` is not one compiler-authored Lean file stem"
        ));
    }
    Ok(())
}

/// Allocate an empty, process-and-attempt-unique output directory and path for
/// a future fresh Lean compilation. The caller must compile directly to this
/// exact path before
/// passing the opaque token to [`observe_declaration_module`]. B1d exercises
/// this only in its dormant compound helper; production integration remains
/// deliberately absent.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn unique_declaration_candidate_olean(
    repo_root: &Path,
    expected_module_name: &str,
) -> Result<DeclarationCandidateOlean, String> {
    if !repo_root.is_absolute() {
        return Err(format!(
            "declaration observation repository root {} must be absolute",
            repo_root.display()
        ));
    }
    require_generated_module_name(expected_module_name)?;
    let parent = modules_dir(repo_root);
    let parent_metadata = std::fs::symlink_metadata(&parent).map_err(|error| {
        format!(
            "cannot inspect declaration observation directory {}: {error}",
            parent.display()
        )
    })?;
    if parent_metadata.file_type().is_symlink() || !parent_metadata.is_dir() {
        return Err(format!(
            "declaration observation directory {} is not a regular non-symlink directory",
            parent.display()
        ));
    }
    let directory = unique_directory(
        &parent,
        &format!("{expected_module_name}.declaration-output"),
    )?;
    Ok(DeclarationCandidateOlean {
        expected_module_name: expected_module_name.to_owned(),
        path: directory.join(format!("{expected_module_name}.olean")),
        directory,
    })
}

fn require_regular_directory(path: &Path, description: &str) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {description} {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "{description} {} is not a regular non-symlink directory",
            path.display()
        ));
    }
    Ok(())
}

fn ensure_declaration_observation_modules_dir(repo_root: &Path) -> Result<PathBuf, String> {
    if !repo_root.is_absolute() {
        return Err(format!(
            "declaration observation repository root {} must be absolute",
            repo_root.display()
        ));
    }
    let output = repo_root.join(".sable-out");
    match std::fs::create_dir(&output) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(error) => {
            return Err(format!(
                "cannot create compiler output directory {}: {error}",
                output.display()
            ));
        }
    }
    require_regular_directory(&output, "compiler output directory")?;
    let modules = modules_dir(repo_root);
    match std::fs::create_dir(&modules) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(error) => {
            return Err(format!(
                "cannot create declaration observation directory {}: {error}",
                modules.display()
            ));
        }
    }
    require_regular_directory(&modules, "declaration observation directory")?;
    Ok(modules)
}

fn unique_declaration_candidate_source(
    repo_root: &Path,
    expected_module_name: &str,
    source: &str,
) -> Result<DeclarationCandidateSource, String> {
    require_generated_module_name(expected_module_name)?;
    let modules = ensure_declaration_observation_modules_dir(repo_root)?;
    let directory = unique_directory(
        &modules,
        &format!("{expected_module_name}.declaration-source"),
    )?;
    let candidate = DeclarationCandidateSource {
        expected_module_name: expected_module_name.to_owned(),
        path: directory.join(format!("{expected_module_name}.lean")),
        directory,
    };
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&candidate.path)
        .and_then(|mut file| {
            file.write_all(source.as_bytes())?;
            file.sync_all()
        })
        .map_err(|error| {
            format!(
                "cannot write declaration observation source {}: {error}",
                candidate.path.display()
            )
        })?;
    validate_declaration_candidate_source(repo_root, &candidate)?;
    Ok(candidate)
}

fn validate_declaration_candidate_source(
    repo_root: &Path,
    candidate: &DeclarationCandidateSource,
) -> Result<(), String> {
    if !repo_root.is_absolute()
        || !candidate.directory.is_absolute()
        || !candidate.path.is_absolute()
    {
        return Err("declaration observation source paths must be absolute".into());
    }
    require_generated_module_name(&candidate.expected_module_name)?;
    let modules = modules_dir(repo_root);
    require_regular_directory(&modules, "declaration observation directory")?;
    let expected_file_name = format!("{}.lean", candidate.expected_module_name);
    if candidate.directory.parent() != Some(modules.as_path())
        || candidate.path.parent() != Some(candidate.directory.as_path())
        || candidate.path.file_name().and_then(|name| name.to_str())
            != Some(expected_file_name.as_str())
    {
        return Err(format!(
            "declaration observation source {} is outside its compiler-owned module-root shape",
            candidate.path.display()
        ));
    }
    require_regular_directory(&candidate.directory, "declaration observation source root")?;
    let entries = std::fs::read_dir(&candidate.directory)
        .map_err(|error| {
            format!(
                "cannot enumerate declaration observation source root {}: {error}",
                candidate.directory.display()
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            format!(
                "cannot enumerate an entry in declaration observation source root {}: {error}",
                candidate.directory.display()
            )
        })?;
    if entries.len() != 1 || entries[0].path() != candidate.path {
        return Err(format!(
            "declaration observation source root {} must contain exactly its owned source file",
            candidate.directory.display()
        ));
    }
    let metadata = std::fs::symlink_metadata(&candidate.path).map_err(|error| {
        format!(
            "cannot inspect declaration observation source {}: {error}",
            candidate.path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "declaration observation source {} is not a regular non-symlink file",
            candidate.path.display()
        ));
    }
    Ok(())
}

/// Exact repository-local inputs that can affect a generated proof. The FNV
/// identifier is only a compact directory/name tag; every reuse also compares
/// this complete map, so a hash collision fails closed.
pub(crate) const PROOF_POLICY_VERSION: &str = "confine-generated-lean-ingress-v4";
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
const PROOF_READY_STAMP_VERSION: &str = "sable-proof-ready-v3";

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProofBuildOutputDigests {
    local_olean_sha256: BTreeMap<String, String>,
    proof_auditor_sha256: String,
    declaration_inventory_sha256: String,
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
        "proof-auditor-sha256:{}\ndeclaration-inventory-sha256:{}\n",
        output_digests.proof_auditor_sha256, output_digests.declaration_inventory_sha256,
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
/// exceeded to avoid deadlock. The three explicit repository targets build in one
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
    command.args([
        "--quiet",
        "build",
        "Sable",
        "sable-proof-audit",
        "sable-declaration-audit",
    ]);
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

/// Dormant B1b command shape for the observational ModuleData inventory. It is
/// sanitized and READY-bound now, but production verification does not invoke
/// it until a later tranche defines and reviews the compiled audit policy.
#[cfg_attr(not(test), allow(dead_code))]
fn serial_declaration_inventory_command(lean_dir: &Path, inventory: &Path) -> Command {
    let mut command = serial_lake_command(lean_dir);
    command.args(["env"]).arg(inventory);
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
    for required in [
        "lean/Sable.lean",
        "lean/SableProofAudit.lean",
        "lean/SableDeclarationAudit.lean",
    ] {
        if !files.contains_key(required) {
            return Err(format!(
                "proof environment is missing trusted output root `{required}`"
            ));
        }
    }
    for label in files.keys().filter(|label| label.ends_with(".lean")) {
        if label != "lean/Sable.lean"
            && label != "lean/SableProofAudit.lean"
            && label != "lean/SableDeclarationAudit.lean"
            && !label.starts_with("lean/Sable/")
        {
            return Err(format!(
                "proof environment contains unsupported Lean source root `{label}`; the trusted output layout is exactly `Sable.lean`, `SableProofAudit.lean`, `SableDeclarationAudit.lean`, and `Sable/**`"
            ));
        }
    }
    let expected = files
        .keys()
        .filter(|label| {
            label.as_str() == "lean/Sable.lean"
                || label.as_str() == "lean/SableProofAudit.lean"
                || label.as_str() == "lean/SableDeclarationAudit.lean"
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

fn proof_build_executable_digest(path: &Path, description: &str) -> Result<String, String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        format!(
            "proof build is missing {description} {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "proof build output {description} {} is not a regular file",
            path.display()
        ));
    }
    let bytes = std::fs::read(path).map_err(|error| {
        format!(
            "cannot hash trusted proof build output {description} {}: {error}",
            path.display()
        )
    })?;
    let metadata_after = std::fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot recheck trusted proof build output {description} {}: {error}",
            path.display()
        )
    })?;
    if metadata_after.file_type().is_symlink() || !metadata_after.is_file() {
        return Err(format!(
            "proof build output {description} {} changed kind while being hashed",
            path.display()
        ));
    }
    Ok(crate::sha256::hex(&bytes))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactObservedFile {
    bytes: Vec<u8>,
    sha256: String,
}

/// Read one observation input only when it remains a regular non-symlink file
/// across the read. The outer pre/post reads around the serialized child are
/// still required: this inner check only closes kind/length changes during one
/// hash operation. Same-user swap-and-restore remains part of the trusted-host
/// boundary, as it does for the existing proof-build identities.
#[allow(dead_code)]
fn observe_regular_file(path: &Path, description: &str) -> Result<ExactObservedFile, String> {
    let metadata_before = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {description} {}: {error}", path.display()))?;
    if metadata_before.file_type().is_symlink() || !metadata_before.is_file() {
        return Err(format!(
            "{description} {} is not a regular non-symlink file",
            path.display()
        ));
    }
    let bytes = std::fs::read(path)
        .map_err(|error| format!("cannot read {description} {}: {error}", path.display()))?;
    let metadata_after = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot recheck {description} {}: {error}", path.display()))?;
    let byte_len = u64::try_from(bytes.len())
        .map_err(|_| format!("{description} {} is too large", path.display()))?;
    if metadata_after.file_type().is_symlink()
        || !metadata_after.is_file()
        || metadata_before.len() != byte_len
        || metadata_after.len() != byte_len
    {
        return Err(format!(
            "{description} {} changed kind or length while being hashed",
            path.display()
        ));
    }
    Ok(ExactObservedFile {
        sha256: crate::sha256::hex(&bytes),
        bytes,
    })
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
    Ok(ProofBuildOutputDigests {
        local_olean_sha256,
        proof_auditor_sha256: proof_build_executable_digest(
            &proof_auditor_path(built),
            "proof-ingress auditor",
        )?,
        declaration_inventory_sha256: proof_build_executable_digest(
            &declaration_inventory_path(built),
            "observational declaration inventory",
        )?,
    })
}

fn proof_auditor_path(built: &Path) -> PathBuf {
    built.join("lean/.lake/build/bin/sable-proof-audit")
}

fn declaration_inventory_path(built: &Path) -> PathBuf {
    built.join("lean/.lake/build/bin/sable-declaration-audit")
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

fn ingress_audit_request(emitted: &Emitted) -> Result<Vec<u8>, serde_json::Error> {
    serde_json::to_vec(&serde_json::json!({
        "schema": INGRESS_REQUEST_SCHEMA,
        "fragments": emitted.ingress.iter().map(|fragment| serde_json::json!({
            "category": fragment.category,
            "text": &fragment.text,
            "expected_kind": fragment.expected_kind,
            "expected_name": &fragment.expected_name,
            "expected_modifiers": &fragment.expected_modifiers,
        })).collect::<Vec<_>>(),
    }))
}

/// Construct the exact request understood by the observational declaration
/// inventory executable. B1b deliberately has no production call site.
#[cfg_attr(not(test), allow(dead_code))]
fn declaration_inventory_request(candidate_olean: &Path) -> Result<Vec<u8>, String> {
    let candidate_olean = candidate_olean.to_str().ok_or_else(|| {
        format!(
            "declaration inventory candidate path {} is not UTF-8",
            candidate_olean.display()
        )
    })?;
    if candidate_olean.is_empty() {
        return Err("declaration inventory candidate path must be nonempty".into());
    }
    serde_json::to_vec(&serde_json::json!({
        "schema": DECLARATION_INVENTORY_REQUEST_SCHEMA,
        "candidate_olean": candidate_olean,
    }))
    .map_err(|error| format!("cannot encode declaration inventory request: {error}"))
}

fn exact_inventory_object<'a>(
    value: &'a serde_json::Value,
    fields: &[&str],
    description: &str,
) -> Result<&'a serde_json::Map<String, serde_json::Value>, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{description} must be a JSON object"))?;
    if object.len() != fields.len() || fields.iter().any(|field| !object.contains_key(*field)) {
        return Err(format!(
            "{description} must contain exactly fields {fields:?}, got {:?}",
            object.keys().collect::<Vec<_>>()
        ));
    }
    Ok(object)
}

fn inventory_string(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
    description: &str,
) -> Result<String, String> {
    object
        .get(field)
        .and_then(serde_json::Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{description} field `{field}` must be a string"))
}

fn inventory_bool(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
    description: &str,
) -> Result<bool, String> {
    object
        .get(field)
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| format!("{description} field `{field}` must be a Boolean"))
}

fn inventory_array<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    field: &str,
    description: &str,
) -> Result<&'a Vec<serde_json::Value>, String> {
    object
        .get(field)
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| format!("{description} field `{field}` must be an array"))
}

fn inventory_optional_string(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
    description: &str,
) -> Result<Option<String>, String> {
    match object.get(field) {
        Some(serde_json::Value::Null) => Ok(None),
        Some(serde_json::Value::String(value)) => Ok(Some(value.clone())),
        _ => Err(format!(
            "{description} field `{field}` must be a string or null"
        )),
    }
}

fn parse_observed_name(
    value: &serde_json::Value,
    description: &str,
) -> Result<ObservedName, String> {
    if value.is_null() {
        return Ok(ObservedName::Anonymous);
    }
    let object = value
        .as_object()
        .ok_or_else(|| format!("{description} must be a structural Lean name"))?;
    if object.contains_key("str") {
        let object = exact_inventory_object(value, &["str"], description)?;
        let parts = object["str"]
            .as_array()
            .filter(|parts| parts.len() == 2)
            .ok_or_else(|| format!("{description} `str` must contain prefix and value"))?;
        let prefix = parse_observed_name(&parts[0], &format!("{description} prefix"))?;
        let value = parts[1]
            .as_str()
            .ok_or_else(|| format!("{description} `str` value must be a string"))?;
        return Ok(ObservedName::Str {
            prefix: Box::new(prefix),
            value: value.to_owned(),
        });
    }
    if object.contains_key("num") {
        let object = exact_inventory_object(value, &["num"], description)?;
        let parts = object["num"]
            .as_array()
            .filter(|parts| parts.len() == 2)
            .ok_or_else(|| format!("{description} `num` must contain prefix and value"))?;
        let prefix = parse_observed_name(&parts[0], &format!("{description} prefix"))?;
        let value = parts[1]
            .as_u64()
            .ok_or_else(|| format!("{description} `num` value must be a u64"))?;
        return Ok(ObservedName::Num {
            prefix: Box::new(prefix),
            value,
        });
    }
    Err(format!(
        "{description} must be anonymous, `str`, or `num`, got fields {:?}",
        object.keys().collect::<Vec<_>>()
    ))
}

fn inventory_optional_name(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
    description: &str,
) -> Result<Option<ObservedName>, String> {
    let value = object
        .get(field)
        .ok_or_else(|| format!("{description} lacks field `{field}`"))?;
    if value.is_null() {
        return Ok(None);
    }
    let present =
        exact_inventory_object(value, &["some"], &format!("{description} field `{field}`"))?;
    parse_observed_name(
        &present["some"],
        &format!("{description} field `{field}` value"),
    )
    .map(Some)
}

fn parse_observed_constant_kind(value: &str) -> Result<ObservedConstantKind, String> {
    match value {
        "axiom" => Ok(ObservedConstantKind::Axiom),
        "definition" => Ok(ObservedConstantKind::Definition),
        "theorem" => Ok(ObservedConstantKind::Theorem),
        "opaque" => Ok(ObservedConstantKind::Opaque),
        "quotient" => Ok(ObservedConstantKind::Quotient),
        "inductive" => Ok(ObservedConstantKind::Inductive),
        "constructor" => Ok(ObservedConstantKind::Constructor),
        "recursor" => Ok(ObservedConstantKind::Recursor),
        other => Err(format!(
            "declaration inventory constant has unsupported kind `{other}`"
        )),
    }
}

fn parse_observed_constant_safety(value: &str) -> Result<ObservedConstantSafety, String> {
    match value {
        "safe" => Ok(ObservedConstantSafety::Safe),
        "unsafe" => Ok(ObservedConstantSafety::Unsafe),
        "partial" => Ok(ObservedConstantSafety::Partial),
        other => Err(format!(
            "declaration inventory constant has unsupported safety `{other}`"
        )),
    }
}

/// Parse one exact canonical output line from the observational inventory
/// executable. Requiring byte-for-byte canonical JSON also rejects duplicate
/// fields, alternative field order, and whitespace that `serde_json::Value`
/// would otherwise normalize away.
#[cfg_attr(not(test), allow(dead_code))]
fn parse_declaration_inventory_output(
    status_success: bool,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<DeclarationModuleInventory, String> {
    let stdout = std::str::from_utf8(stdout)
        .map_err(|error| format!("declaration inventory stdout is not UTF-8: {error}"))?;
    let stderr = std::str::from_utf8(stderr)
        .map_err(|error| format!("declaration inventory stderr is not UTF-8: {error}"))?;
    if !status_success || !stderr.is_empty() {
        return Err(format!(
            "declaration inventory transport failed: status_success={status_success}, stdout={stdout:?}, stderr={stderr:?}"
        ));
    }
    let Some(line) = stdout.strip_suffix('\n') else {
        return Err(
            "declaration inventory stdout must be exactly one newline-terminated JSON result"
                .into(),
        );
    };
    if line.is_empty() || line.contains(['\n', '\r']) {
        return Err("declaration inventory stdout must contain exactly one JSON line".into());
    }
    let value: serde_json::Value = serde_json::from_str(line)
        .map_err(|error| format!("declaration inventory result is not valid JSON: {error}"))?;
    let canonical = serde_json::to_vec(&value)
        .map_err(|error| format!("cannot reproduce declaration inventory JSON: {error}"))?;
    if canonical != line.as_bytes() {
        return Err("declaration inventory result is not the exact canonical JSON encoding".into());
    }
    let object = value
        .as_object()
        .ok_or_else(|| "declaration inventory result must be a JSON object".to_owned())?;
    if object.get("schema").and_then(serde_json::Value::as_str)
        != Some(DECLARATION_INVENTORY_RESULT_SCHEMA)
    {
        return Err("declaration inventory result has the wrong or missing schema".into());
    }
    if object
        .get("observational")
        .and_then(serde_json::Value::as_bool)
        != Some(true)
    {
        return Err("declaration inventory result must identify itself as observational".into());
    }
    if object.contains_key("error_kind") || object.contains_key("message") {
        let object = exact_inventory_object(
            &value,
            &["schema", "observational", "error_kind", "message"],
            "declaration inventory rejection",
        )?;
        let kind = inventory_string(object, "error_kind", "declaration inventory rejection")?;
        if !matches!(kind.as_str(), "transport" | "request" | "inventory") {
            return Err(format!(
                "declaration inventory rejection has unsupported error kind `{kind}`"
            ));
        }
        let message = inventory_string(object, "message", "declaration inventory rejection")?;
        return Err(format!(
            "declaration inventory rejected its {kind} boundary: {message}"
        ));
    }

    let object = exact_inventory_object(
        &value,
        &[
            "schema",
            "observational",
            "is_module",
            "imports",
            "constants",
            "extra_const_names",
            "extension_families",
        ],
        "declaration inventory result",
    )?;
    let is_module = inventory_bool(object, "is_module", "declaration inventory result")?;

    let mut imports = Vec::new();
    for (index, value) in inventory_array(object, "imports", "declaration inventory result")?
        .iter()
        .enumerate()
    {
        let description = format!("declaration inventory import {index}");
        let import = exact_inventory_object(
            value,
            &["module", "import_all", "is_exported", "is_meta"],
            &description,
        )?;
        imports.push(ObservedModuleImport {
            module: parse_observed_name(
                &import["module"],
                &format!("{description} field `module`"),
            )?,
            import_all: inventory_bool(import, "import_all", &description)?,
            is_exported: inventory_bool(import, "is_exported", &description)?,
            is_meta: inventory_bool(import, "is_meta", &description)?,
        });
    }

    let mut constants = Vec::new();
    for (index, value) in inventory_array(object, "constants", "declaration inventory result")?
        .iter()
        .enumerate()
    {
        let description = format!("declaration inventory constant slot {index}");
        let constant = exact_inventory_object(
            value,
            &["const_name", "info_name", "kind", "safety"],
            &description,
        )?;
        let const_name = inventory_optional_name(constant, "const_name", &description)?;
        let info_name = inventory_optional_name(constant, "info_name", &description)?;
        let kind = inventory_optional_string(constant, "kind", &description)?;
        let safety = inventory_optional_string(constant, "safety", &description)?;
        if const_name.is_none() && info_name.is_none() {
            return Err(format!(
                "{description} has neither side of the parallel arrays"
            ));
        }
        let (kind, safety) = match info_name.as_ref() {
            Some(_) => {
                let kind = kind
                    .ok_or_else(|| format!("{description} has constant information but no kind"))?;
                let safety = safety.ok_or_else(|| {
                    format!("{description} has constant information but no safety")
                })?;
                (
                    Some(parse_observed_constant_kind(&kind)?),
                    Some(parse_observed_constant_safety(&safety)?),
                )
            }
            None => {
                if kind.is_some() || safety.is_some() {
                    return Err(format!(
                        "{description} has kind or safety without constant information"
                    ));
                }
                (None, None)
            }
        };
        constants.push(ObservedConstantSlot {
            const_name,
            info_name,
            kind,
            safety,
        });
    }

    let extra_const_names =
        inventory_array(object, "extra_const_names", "declaration inventory result")?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                parse_observed_name(
                    value,
                    &format!("declaration inventory extra constant name {index}"),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

    let mut extension_families = Vec::new();
    for (index, value) in
        inventory_array(object, "extension_families", "declaration inventory result")?
            .iter()
            .enumerate()
    {
        let description = format!("declaration inventory extension family {index}");
        let extension = exact_inventory_object(value, &["name", "count"], &description)?;
        let count = extension
            .get("count")
            .and_then(serde_json::Value::as_u64)
            .and_then(|count| usize::try_from(count).ok())
            .ok_or_else(|| format!("{description} field `count` must be a usize"))?;
        extension_families.push(ObservedExtensionFamily {
            name: parse_observed_name(&extension["name"], &format!("{description} field `name`"))?,
            count,
        });
    }

    Ok(DeclarationModuleInventory {
        observational: true,
        is_module,
        imports,
        constants,
        extra_const_names,
        extension_families,
    })
}

/// Convert Sable's deliberately narrow compiler-owned Lean name spelling to
/// the exact recursive `Name.str` shape emitted by Lean. This does not parse
/// arbitrary Lean identifiers: numeric, quoted, hygienic, empty, and non-ASCII
/// components are rejected instead of being compared through display text.
fn observed_ascii_dotted_name(name: &str) -> Result<ObservedName, String> {
    if name.is_empty() {
        return Err("expected Lean declaration name is empty".into());
    }
    let mut observed = ObservedName::Anonymous;
    for component in name.split('.') {
        let bytes = component.as_bytes();
        let Some(first) = bytes.first().copied() else {
            return Err(format!(
                "expected Lean declaration name `{name}` has an empty component"
            ));
        };
        if !(first.is_ascii_alphabetic() || first == b'_')
            || (first == b'_' && bytes.len() == 1)
            || !bytes[1..]
                .iter()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(*byte, b'_' | b'\''))
        {
            return Err(format!(
                "expected Lean declaration name `{name}` is outside the pinned ASCII dotted/apostrophe spelling"
            ));
        }
        observed = ObservedName::Str {
            prefix: Box::new(observed),
            value: component.to_owned(),
        };
    }
    Ok(observed)
}

fn observed_name_has_terminal_sentinel_prefix(name: &ObservedName) -> bool {
    match name {
        ObservedName::Anonymous => false,
        ObservedName::Str { prefix, value } => {
            matches!(
                prefix.as_ref(),
                ObservedName::Str {
                    prefix: outer,
                    value: namespace,
                } if matches!(outer.as_ref(), ObservedName::Anonymous)
                    && namespace == "SableGenerated"
                    && value.starts_with("complete_")
            ) || observed_name_has_terminal_sentinel_prefix(prefix)
        }
        ObservedName::Num { prefix, .. } => observed_name_has_terminal_sentinel_prefix(prefix),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedInventoryDeclaration {
    role: DeclarationInventoryExplicitRole,
    name: ObservedName,
}

fn explicit_inventory_kind_matches(
    role: &DeclarationInventoryExplicitRole,
    kind: ObservedConstantKind,
) -> bool {
    match role {
        DeclarationInventoryExplicitRole::StructureRoot { .. } => {
            kind == ObservedConstantKind::Inductive
        }
        DeclarationInventoryExplicitRole::DefinitionRoot { .. } => {
            kind == ObservedConstantKind::Definition
        }
        DeclarationInventoryExplicitRole::TheoremRoot { .. }
        | DeclarationInventoryExplicitRole::TerminalSentinel { .. } => {
            kind == ObservedConstantKind::Theorem
        }
        // Lean records projections whose result is in `Prop` as theorem
        // constants; data-valued projections are ordinary definitions.
        DeclarationInventoryExplicitRole::StructureField { .. } => matches!(
            kind,
            ObservedConstantKind::Definition | ObservedConstantKind::Theorem
        ),
    }
}

/// Apply only the coarse rejection rules supported by the raw v1 inventory.
/// This intentionally does not inspect types/bodies, prove auxiliary
/// attribution, authenticate imports or a module header, interpret extension
/// payloads, or close transitive axioms.
fn preflight_declaration_inventory(
    envelope: &ExpectedDeclarationEnvelope,
    inventory: &DeclarationModuleInventory,
) -> Result<DeclarationInventoryPreflight, String> {
    let Some(last_root_index) = envelope.roots.len().checked_sub(1) else {
        return Err("declaration inventory preflight expected a nonempty envelope".into());
    };
    for (root_index, root) in envelope.roots.iter().enumerate() {
        let is_terminal = matches!(&root.kind, ExpectedDeclarationKind::TerminalSentinel);
        if is_terminal != (root_index == last_root_index) {
            return Err(
                "declaration inventory preflight requires exactly one terminal sentinel and requires it to be the final explicit root"
                    .into(),
            );
        }
    }

    let mut expected_names = BTreeSet::new();
    let mut expected = Vec::new();
    for (root_index, root) in envelope.roots.iter().enumerate() {
        let role = match &root.kind {
            ExpectedDeclarationKind::Structure { .. } => {
                DeclarationInventoryExplicitRole::StructureRoot { root_index }
            }
            ExpectedDeclarationKind::Definition { .. } => {
                DeclarationInventoryExplicitRole::DefinitionRoot { root_index }
            }
            ExpectedDeclarationKind::Theorem { .. } => {
                DeclarationInventoryExplicitRole::TheoremRoot { root_index }
            }
            ExpectedDeclarationKind::TerminalSentinel => {
                DeclarationInventoryExplicitRole::TerminalSentinel { root_index }
            }
        };
        let name = observed_ascii_dotted_name(&root.name)?;
        if !expected_names.insert(name.clone()) {
            return Err(format!(
                "declaration inventory preflight has duplicate explicit structural name `{}`",
                root.name
            ));
        }
        expected.push(ExpectedInventoryDeclaration { role, name });

        if let ExpectedDeclarationKind::Structure { fields } = &root.kind {
            for (field_index, field) in fields.iter().enumerate() {
                let name = observed_ascii_dotted_name(field)?;
                if !expected_names.insert(name.clone()) {
                    return Err(format!(
                        "declaration inventory preflight has duplicate explicit structural name `{field}`"
                    ));
                }
                expected.push(ExpectedInventoryDeclaration {
                    role: DeclarationInventoryExplicitRole::StructureField {
                        root_index,
                        field_index,
                    },
                    name,
                });
            }
        }
    }
    let expected_sentinel = expected
        .iter()
        .find(|declaration| {
            matches!(
                &declaration.role,
                DeclarationInventoryExplicitRole::TerminalSentinel { .. }
            )
        })
        .expect("the envelope shape check established one terminal sentinel")
        .name
        .clone();
    if !observed_name_has_terminal_sentinel_prefix(&expected_sentinel) {
        return Err(
            "declaration inventory preflight expected terminal sentinel is outside its reserved structural prefix"
                .into(),
        );
    }

    if !inventory.observational {
        return Err("declaration inventory preflight requires observational inventory data".into());
    }
    if inventory.is_module {
        return Err(
            "declaration inventory preflight rejects module-system/multipart candidates".into(),
        );
    }
    if !inventory.extra_const_names.is_empty() {
        return Err(format!(
            "declaration inventory preflight rejects {} code-generation extra constant name(s)",
            inventory.extra_const_names.len()
        ));
    }

    let mut constants_by_name = BTreeMap::new();
    let mut constants = Vec::with_capacity(inventory.constants.len());
    for (slot_index, slot) in inventory.constants.iter().enumerate() {
        let (Some(const_name), Some(info_name), Some(kind), Some(safety)) = (
            slot.const_name.as_ref(),
            slot.info_name.as_ref(),
            slot.kind,
            slot.safety,
        ) else {
            return Err(format!(
                "declaration inventory preflight constant slot {slot_index} does not contain both names, kind, and safety"
            ));
        };
        if const_name != info_name {
            return Err(format!(
                "declaration inventory preflight constant slot {slot_index} has mismatched structural names"
            ));
        }
        if matches!(const_name, ObservedName::Anonymous) {
            return Err(format!(
                "declaration inventory preflight constant slot {slot_index} has an anonymous name"
            ));
        }
        match safety {
            ObservedConstantSafety::Safe => {}
            ObservedConstantSafety::Unsafe => {
                return Err(format!(
                    "declaration inventory preflight rejects unsafe constant in slot {slot_index}"
                ));
            }
            ObservedConstantSafety::Partial => {
                return Err(format!(
                    "declaration inventory preflight rejects partial constant in slot {slot_index}"
                ));
            }
        }
        if kind == ObservedConstantKind::Axiom {
            return Err(format!(
                "declaration inventory preflight rejects candidate axiom in slot {slot_index}"
            ));
        }
        if observed_name_has_terminal_sentinel_prefix(const_name)
            && const_name != &expected_sentinel
        {
            return Err(format!(
                "declaration inventory preflight rejects an unexpected declaration under the reserved terminal-sentinel prefix in slot {slot_index}"
            ));
        }
        if constants_by_name
            .insert(const_name.clone(), (slot_index, kind))
            .is_some()
        {
            return Err(format!(
                "declaration inventory preflight has duplicate constant structural name in slot {slot_index}"
            ));
        }
        constants.push((slot_index, const_name.clone(), kind));
    }

    let mut explicit_matches = Vec::with_capacity(expected.len());
    let mut matched_names = BTreeSet::new();
    for declaration in expected {
        let Some(&(slot_index, kind)) = constants_by_name.get(&declaration.name) else {
            return Err(format!(
                "declaration inventory preflight is missing explicit declaration {:?}",
                declaration.role
            ));
        };
        if !explicit_inventory_kind_matches(&declaration.role, kind) {
            return Err(format!(
                "declaration inventory preflight explicit declaration {:?} has incompatible observed kind {:?}",
                declaration.role, kind
            ));
        }
        matched_names.insert(declaration.name.clone());
        explicit_matches.push(DeclarationInventoryExplicitMatch {
            role: declaration.role,
            name: declaration.name,
            slot_index,
            kind,
        });
    }

    let unclassified_constants = constants
        .into_iter()
        .filter(|(_, name, _)| !matched_names.contains(name))
        .map(
            |(slot_index, name, kind)| DeclarationInventoryUnclassifiedConstant {
                name,
                slot_index,
                kind,
            },
        )
        .collect();
    Ok(DeclarationInventoryPreflight {
        observational: true,
        authoritative: false,
        explicit_matches,
        unclassified_constants,
    })
}

fn preflight_declaration_observation(
    observation: &DeclarationModuleObservation,
) -> Result<DeclarationInventoryPreflight, String> {
    if !observation.observational || observation.authoritative {
        return Err(
            "declaration inventory preflight requires a bound non-authoritative observation".into(),
        );
    }
    preflight_declaration_inventory(
        &observation
            .declaration_subject
            .candidate
            .declaration_envelope,
        &observation.inventory,
    )
}

fn validate_declaration_observation_subject(
    proof_environment_id: &str,
    proof_policy: &str,
    subject: &DeclarationAuditSubject,
    expected_emitted: &Emitted,
    candidate: &DeclarationCandidateOlean,
) -> Result<Vec<u8>, String> {
    if subject.schema != DECLARATION_AUDIT_SUBJECT_SCHEMA {
        return Err(format!(
            "declaration observation subject has unsupported schema `{}`",
            subject.schema
        ));
    }
    if subject.proof_environment_id != proof_environment_id {
        return Err(format!(
            "declaration observation subject names proof environment `{}`, expected `{proof_environment_id}`",
            subject.proof_environment_id
        ));
    }
    if subject.proof_policy != proof_policy {
        return Err(format!(
            "declaration observation subject names proof policy `{}`, expected `{proof_policy}`",
            subject.proof_policy
        ));
    }
    require_generated_module_name(&subject.candidate.module_name)?;
    if subject.candidate.module_name != candidate.expected_module_name {
        return Err(format!(
            "declaration observation candidate path is reserved for expected module `{}`, but the source subject names `{}`",
            candidate.expected_module_name, subject.candidate.module_name
        ));
    }
    require_terminal_sentinel_for_module(expected_emitted, &subject.candidate.module_name)
        .map_err(|failure| failure.message)?;
    let expected_candidate = DeclarationModuleSubject::from_emitted(
        candidate.expected_module_name.clone(),
        expected_emitted,
    );
    if subject.candidate != expected_candidate {
        return Err(format!(
            "declaration observation candidate subject does not exactly match the generated source digest and typed envelope for expected module `{}`",
            subject.candidate.module_name
        ));
    }
    Ok(subject.canonical_json())
}

#[allow(dead_code)]
fn validate_declaration_candidate_path(
    repo_root: &Path,
    candidate: &DeclarationCandidateOlean,
) -> Result<(), String> {
    if !repo_root.is_absolute()
        || !candidate.directory.is_absolute()
        || !candidate.path.is_absolute()
    {
        return Err("declaration observation paths must be absolute".into());
    }
    let parent = modules_dir(repo_root);
    if candidate.directory.parent() != Some(parent.as_path())
        || candidate.path.parent() != Some(candidate.directory.as_path())
    {
        return Err(format!(
            "declaration observation candidate {} is outside the compiler-owned generated-module directory",
            candidate.path.display()
        ));
    }
    let parent_metadata = std::fs::symlink_metadata(&parent).map_err(|error| {
        format!(
            "cannot inspect declaration observation directory {}: {error}",
            parent.display()
        )
    })?;
    if parent_metadata.file_type().is_symlink() || !parent_metadata.is_dir() {
        return Err(format!(
            "declaration observation directory {} is not a regular non-symlink directory",
            parent.display()
        ));
    }
    require_regular_directory(
        &candidate.directory,
        "declaration observation candidate output root",
    )?;
    require_generated_module_name(&candidate.expected_module_name)?;
    let expected_file_name = format!("{}.olean", candidate.expected_module_name);
    if candidate.path.file_name().and_then(|name| name.to_str())
        != Some(expected_file_name.as_str())
    {
        return Err(format!(
            "declaration observation candidate {} does not use its exact expected module file name",
            candidate.path.display()
        ));
    }
    let directory_name = candidate
        .directory
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            format!(
                "declaration observation candidate output root {} has no UTF-8 file name",
                candidate.directory.display()
            )
        })?;
    let prefix = format!(
        ".{}.declaration-output.{}.",
        candidate.expected_module_name,
        std::process::id()
    );
    let nonce = directory_name
        .strip_prefix(&prefix)
        .filter(|tail| !tail.is_empty() && tail.bytes().all(|byte| byte.is_ascii_digit()))
        .ok_or_else(|| {
            format!(
                "declaration observation candidate output root {} is not one compiler-allocated temporary directory",
                candidate.directory.display()
            )
        })?;
    nonce.parse::<u64>().map_err(|_| {
        format!(
            "declaration observation candidate output root {} has an out-of-range allocation nonce",
            candidate.directory.display()
        )
    })?;
    Ok(())
}

#[derive(Clone, Copy)]
enum DeclarationCandidateOutputState {
    Empty,
    TraditionalOlean,
}

fn require_declaration_candidate_output_state(
    candidate: &DeclarationCandidateOlean,
    expected: DeclarationCandidateOutputState,
) -> Result<(), String> {
    let mut entries = std::fs::read_dir(&candidate.directory)
        .map_err(|error| {
            format!(
                "cannot enumerate declaration observation candidate output root {}: {error}",
                candidate.directory.display()
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            format!(
                "cannot enumerate an entry in declaration observation candidate output root {}: {error}",
                candidate.directory.display()
            )
        })?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    match expected {
        DeclarationCandidateOutputState::Empty if entries.is_empty() => Ok(()),
        DeclarationCandidateOutputState::TraditionalOlean
            if entries.len() == 1 && entries[0].path() == candidate.path =>
        {
            let metadata = std::fs::symlink_metadata(&candidate.path).map_err(|error| {
                format!(
                    "cannot inspect declaration observation candidate {}: {error}",
                    candidate.path.display()
                )
            })?;
            if metadata.file_type().is_symlink() || !metadata.is_file() {
                return Err(format!(
                    "declaration observation candidate {} is not a regular non-symlink file",
                    candidate.path.display()
                ));
            }
            Ok(())
        }
        _ => Err(format!(
            "declaration observation candidate output root {} contains an unexpected multipart, IR, or unowned output set: {:?}",
            candidate.directory.display(),
            entries
                .iter()
                .map(std::fs::DirEntry::file_name)
                .collect::<Vec<_>>()
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn bind_declaration_observation(
    proof_environment_id: &str,
    proof_policy: &str,
    subject: &DeclarationAuditSubject,
    expected_emitted: &Emitted,
    candidate: &DeclarationCandidateOlean,
    proof_ready_before: ExactObservedFile,
    proof_ready_after: ExactObservedFile,
    candidate_before: ExactObservedFile,
    candidate_after: ExactObservedFile,
    inventory_request: Vec<u8>,
    inventory_status_success: bool,
    inventory_result: Vec<u8>,
    inventory_stderr: Vec<u8>,
) -> Result<DeclarationModuleObservation, String> {
    let declaration_subject_json = validate_declaration_observation_subject(
        proof_environment_id,
        proof_policy,
        subject,
        expected_emitted,
        candidate,
    )?;
    let expected_request = declaration_inventory_request(candidate.path())?;
    if inventory_request != expected_request {
        return Err(
            "declaration observation did not use the exact request for its candidate path".into(),
        );
    }
    for (description, observed) in [
        ("proof READY before", &proof_ready_before),
        ("proof READY after", &proof_ready_after),
        ("candidate `.olean` before", &candidate_before),
        ("candidate `.olean` after", &candidate_after),
    ] {
        if observed.sha256 != crate::sha256::hex(&observed.bytes) {
            return Err(format!(
                "declaration observation {description} SHA-256 does not match its exact bytes"
            ));
        }
    }
    if proof_ready_before.bytes != proof_ready_after.bytes
        || proof_ready_before.sha256 != proof_ready_after.sha256
    {
        return Err("proof READY bytes changed during declaration observation".into());
    }
    if candidate_before.bytes != candidate_after.bytes
        || candidate_before.sha256 != candidate_after.sha256
    {
        return Err("candidate `.olean` bytes changed during declaration observation".into());
    }
    if proof_ready_before.bytes.is_empty() {
        return Err("proof READY bytes are empty during declaration observation".into());
    }
    std::str::from_utf8(&proof_ready_before.bytes)
        .map_err(|error| format!("proof READY bytes are not UTF-8: {error}"))?;
    let inventory = parse_declaration_inventory_output(
        inventory_status_success,
        &inventory_result,
        &inventory_stderr,
    )?;
    let declaration_subject_sha256 = crate::sha256::hex(&declaration_subject_json);
    let inventory_request_sha256 = crate::sha256::hex(&inventory_request);
    let inventory_result_sha256 = crate::sha256::hex(&inventory_result);
    Ok(DeclarationModuleObservation {
        schema: DECLARATION_OBSERVATION_SCHEMA,
        observational: true,
        authoritative: false,
        expected_module_name: subject.candidate.module_name.clone(),
        proof_environment_id: proof_environment_id.to_owned(),
        proof_policy: proof_policy.to_owned(),
        declaration_subject: subject.clone(),
        declaration_subject_json,
        declaration_subject_sha256,
        proof_ready_bytes: proof_ready_before.bytes,
        proof_ready_sha256_before: proof_ready_before.sha256,
        proof_ready_sha256_after: proof_ready_after.sha256,
        candidate_olean_sha256_before: candidate_before.sha256,
        candidate_olean_sha256_after: candidate_after.sha256,
        inventory_request,
        inventory_request_sha256,
        inventory_result,
        inventory_result_sha256,
        inventory,
    })
}

fn observe_declaration_module_locked(
    _process_lock: &ProofProcessLock,
    repo_root: &Path,
    environment: &ProofEnvironment,
    built: &Path,
    subject: &DeclarationAuditSubject,
    expected_emitted: &Emitted,
    candidate: &DeclarationCandidateOlean,
    proof_ready_before: ExactObservedFile,
) -> Result<DeclarationModuleObservation, String> {
    validate_declaration_candidate_path(repo_root, candidate)?;
    validate_declaration_observation_subject(
        environment.id(),
        environment.policy(),
        subject,
        expected_emitted,
        candidate,
    )?;
    let request = declaration_inventory_request(candidate.path())?;
    let ready = built.join("READY");
    let inventory_executable = declaration_inventory_path(&built);
    let lean_dir = built.join("lean");

    environment.validate_built(&built)?;
    validate_declaration_candidate_path(repo_root, candidate)?;
    require_declaration_candidate_output_state(
        candidate,
        DeclarationCandidateOutputState::TraditionalOlean,
    )?;
    let candidate_before = observe_regular_file(
        candidate.path(),
        "declaration observation candidate `.olean`",
    )?;
    let inventory_metadata = std::fs::symlink_metadata(&inventory_executable).map_err(|error| {
        format!(
            "cannot inspect observational declaration inventory {}: {error}",
            inventory_executable.display()
        )
    })?;
    if inventory_metadata.file_type().is_symlink() || !inventory_metadata.is_file() {
        return Err(format!(
            "observational declaration inventory {} is not a regular file",
            inventory_executable.display()
        ));
    }
    require_serial_lake_version(&lean_dir)?;

    let mut command = serial_declaration_inventory_command(&lean_dir, &inventory_executable);
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to run observational declaration inventory: {error}"))?;
    let write_result = child
        .stdin
        .take()
        .ok_or_else(|| "declaration inventory stdin pipe is unavailable".to_owned())
        .and_then(|mut stdin| {
            stdin
                .write_all(&request)
                .map_err(|error| format!("cannot write declaration inventory request: {error}"))
        });
    if let Err(message) = write_result {
        let _ = child.kill();
        let _ = child.wait();
        return Err(message);
    }
    let output = child
        .wait_with_output()
        .map_err(|error| format!("cannot wait for observational declaration inventory: {error}"))?;

    let candidate_after = observe_regular_file(
        candidate.path(),
        "declaration observation candidate `.olean`",
    )?;
    require_declaration_candidate_output_state(
        candidate,
        DeclarationCandidateOutputState::TraditionalOlean,
    )?;
    environment.validate_built(&built)?;
    let proof_ready_after = observe_regular_file(&ready, "proof READY")?;
    bind_declaration_observation(
        environment.id(),
        environment.policy(),
        subject,
        expected_emitted,
        candidate,
        proof_ready_before,
        proof_ready_after,
        candidate_before,
        candidate_after,
        request,
        output.status.success(),
        output.stdout,
        output.stderr,
    )
}

/// Observe one explicit, freshly compiled temporary `.olean` under the same
/// global proof-workload serialization as Lean and the ingress auditor. This
/// dormant B1c helper only binds exact bytes and `readModuleData` inventory; it
/// neither imports/replays the candidate nor makes any acceptance decision.
/// No production verification, publication, cache-hit, or assurance path calls
/// it in this tranche.
#[allow(dead_code)]
pub(crate) fn observe_declaration_module(
    repo_root: &Path,
    environment: &ProofEnvironment,
    subject: &DeclarationAuditSubject,
    expected_emitted: &Emitted,
    candidate: &DeclarationCandidateOlean,
) -> Result<DeclarationModuleObservation, String> {
    validate_declaration_candidate_path(repo_root, candidate)?;
    validate_declaration_observation_subject(
        environment.id(),
        environment.policy(),
        subject,
        expected_emitted,
        candidate,
    )?;
    // `ensure_built` may itself acquire the non-reentrant process mutex on a
    // cold build, so resolve the immutable build before entering this workload.
    let built = environment.ensure_built(repo_root)?;
    let ready = built.join("READY");
    let process_lock = ProofProcessLock::acquire(repo_root)?;
    environment.validate_built(&built)?;
    let proof_ready_before = observe_regular_file(&ready, "proof READY")?;
    observe_declaration_module_locked(
        &process_lock,
        repo_root,
        environment,
        &built,
        subject,
        expected_emitted,
        candidate,
        proof_ready_before,
    )
}

fn require_exact_observed_source(
    observed: &ExactObservedFile,
    expected_source: &str,
    phase: &str,
) -> Result<(), String> {
    if observed.sha256 != crate::sha256::hex(&observed.bytes) {
        return Err(format!(
            "declaration observation source SHA-256 does not match its exact bytes {phase}"
        ));
    }
    if observed.bytes != expected_source.as_bytes() {
        return Err(format!(
            "declaration observation source bytes changed {phase}"
        ));
    }
    Ok(())
}

fn require_absent_candidate(candidate: &DeclarationCandidateOlean) -> Result<(), String> {
    require_declaration_candidate_output_state(candidate, DeclarationCandidateOutputState::Empty)
}

fn require_declaration_temporary_path_absent(path: &Path, description: &str) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "cannot confirm that {description} {} was removed: {error}",
            path.display()
        )),
        Ok(_) => Err(format!(
            "{description} {} remains after its compiler-owned lifecycle",
            path.display()
        )),
    }
}

/// Compile and inventory one exact generated module as a single serialized,
/// ephemeral observation. It authenticates every recorded ingress fragment
/// before allowing Lean to execute the generated source. This helper remains
/// deliberately dormant: no production verification, artifact publication,
/// cache, or assurance path invokes or consumes it.
/// The nonce-bearing source path may affect `.olean` bytes, so the returned
/// digest cannot identify a future stable-path artifact without a new policy.
#[allow(dead_code)]
pub(crate) fn compile_and_observe_declaration_module(
    repo_root: &Path,
    environment: &ProofEnvironment,
    emitted: &Emitted,
    subject: &DeclarationAuditSubject,
) -> Result<CompiledDeclarationObservation, String> {
    // Compilation executes elaborators and tactics, so even this dormant,
    // non-authoritative observation must pass the trusted parser boundary
    // before generated source is materialized or the Lean compiler executes it.
    audit_ingress(repo_root, environment, emitted).map_err(|failure| failure.message)?;

    // A cold immutable proof build may acquire the same non-reentrant process
    // mutex, so it must be resolved before this one compound workload begins.
    let built = environment.ensure_built(repo_root)?;
    ensure_declaration_observation_modules_dir(repo_root)?;
    let expected_module_name = subject.candidate.module_name.clone();
    let ready = built.join("READY");
    let process_lock = ProofProcessLock::acquire(repo_root)?;
    environment.validate_built(&built)?;
    let observation = {
        // These tokens are scoped inside the already-held process lock, so
        // reverse-order Drop cleanup always finishes before another
        // cooperating proof workload can enter this repository.
        let source = unique_declaration_candidate_source(
            repo_root,
            &expected_module_name,
            &emitted.lean_source,
        )?;
        let candidate = unique_declaration_candidate_olean(repo_root, &expected_module_name)?;
        validate_declaration_observation_subject(
            environment.id(),
            environment.policy(),
            subject,
            emitted,
            &candidate,
        )?;
        validate_declaration_candidate_source(repo_root, &source)?;
        validate_declaration_candidate_path(repo_root, &candidate)?;

        let command = generated_lean_command(
            &built.join("lean"),
            &modules_dir(repo_root),
            &source.path,
            Some((&source.directory, candidate.path())),
        );
        require_absent_candidate(&candidate)?;
        let proof_ready_before = observe_regular_file(&ready, "proof READY")?;
        let source_before = observe_regular_file(&source.path, "declaration observation source")?;
        require_exact_observed_source(&source_before, &emitted.lean_source, "before compilation")?;

        let lean_output = run_lean_locked(
            &process_lock,
            environment,
            &built,
            &source.path,
            &emitted.lean_source,
            command,
        )?;
        require_observational_compilation_acceptance(emitted, &lean_output)?;
        validate_declaration_candidate_source(repo_root, &source)?;
        let source_after_compile =
            observe_regular_file(&source.path, "declaration observation source")?;
        require_exact_observed_source(
            &source_after_compile,
            &emitted.lean_source,
            "after compilation",
        )?;

        let declaration = observe_declaration_module_locked(
            &process_lock,
            repo_root,
            environment,
            &built,
            subject,
            emitted,
            &candidate,
            proof_ready_before,
        )?;
        validate_declaration_candidate_source(repo_root, &source)?;
        let source_after_inventory =
            observe_regular_file(&source.path, "declaration observation source")?;
        require_exact_observed_source(
            &source_after_inventory,
            &emitted.lean_source,
            "after inventory",
        )?;
        if source_before.bytes != source_after_compile.bytes
            || source_before.bytes != source_after_inventory.bytes
        {
            return Err(
                "declaration observation source did not remain byte-identical across compilation and inventory"
                .into(),
            );
        }
        let inventory_preflight = preflight_declaration_observation(&declaration)?;

        CompiledDeclarationObservation {
            observational: true,
            authoritative: false,
            ephemeral_source_root: source.directory.clone(),
            ephemeral_source_path: source.path.clone(),
            ephemeral_candidate_root: candidate.directory.clone(),
            ephemeral_candidate_path: candidate.path.clone(),
            source_sha256_before: source_before.sha256,
            source_sha256_after_compile: source_after_compile.sha256,
            source_sha256_after_inventory: source_after_inventory.sha256,
            lean_stdout_sha256: crate::sha256::hex(&lean_output.stdout),
            lean_stdout: lean_output.stdout,
            lean_messages: lean_output.messages,
            declaration,
            inventory_preflight,
        }
    };

    for (path, description) in [
        (&observation.ephemeral_source_path, "ephemeral source file"),
        (
            &observation.ephemeral_source_root,
            "ephemeral source directory",
        ),
        (
            &observation.ephemeral_candidate_path,
            "ephemeral candidate file",
        ),
        (
            &observation.ephemeral_candidate_root,
            "ephemeral candidate directory",
        ),
    ] {
        require_declaration_temporary_path_absent(path, description)?;
    }
    drop(process_lock);
    Ok(observation)
}

fn terminal_sentinel_preimage(
    emitted: &Emitted,
) -> Result<(&ExpectedDeclarationRoot, &str), IngressAuditFailure> {
    let Some(root) = emitted.declaration_envelope.roots.last() else {
        return Err(ingress_transport_failure(
            emitted,
            "generated Lean declaration envelope lacks its terminal sentinel",
        ));
    };
    if !matches!(&root.kind, ExpectedDeclarationKind::TerminalSentinel) {
        return Err(ingress_transport_failure(
            emitted,
            "generated Lean declaration envelope does not end in its terminal sentinel",
        ));
    }
    let command = format!("theorem {} : True := True.intro\n", root.name);
    if !emitted.lean_source.ends_with(&command) {
        return Err(ingress_transport_failure(
            emitted,
            "generated Lean source does not end in its recorded terminal sentinel",
        ));
    }
    let pre_sentinel_source = emitted
        .lean_source
        .strip_suffix(&command)
        .expect("the exact terminal command was checked as a suffix");
    Ok((root, pre_sentinel_source))
}

fn require_terminal_sentinel(emitted: &Emitted) -> Result<(), IngressAuditFailure> {
    terminal_sentinel_preimage(emitted).map(|_| ())
}

fn require_terminal_sentinel_for_module(
    emitted: &Emitted,
    expected_module_name: &str,
) -> Result<(), IngressAuditFailure> {
    let (root, pre_sentinel_source) = terminal_sentinel_preimage(emitted)?;
    let expected_name = terminal_sentinel_name(expected_module_name, pre_sentinel_source);
    if root.name != expected_name {
        return Err(ingress_transport_failure(
            emitted,
            format!(
                "generated Lean terminal sentinel does not bind expected module `{expected_module_name}`"
            ),
        ));
    }
    Ok(())
}

/// Authenticate every compiler-recorded user-derived parser boundary using
/// the content-hashed trusted auditor. Candidate generated modules are not
/// imported by this mode; the auditor loads extensions only from `Sable`.
pub(crate) fn audit_ingress(
    repo_root: &Path,
    environment: &ProofEnvironment,
    emitted: &Emitted,
) -> Result<(), IngressAuditFailure> {
    require_terminal_sentinel(emitted)?;
    let request = ingress_audit_request(emitted).map_err(|error| {
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
    if object.get("schema").and_then(serde_json::Value::as_str) != Some(INGRESS_RESULT_SCHEMA) {
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

struct StrictBatchLeanOutput {
    status_success: bool,
    stdout: Vec<u8>,
    messages: Vec<LeanMessage>,
}

fn generated_lean_command(
    lean_dir: &Path,
    generated_modules: &Path,
    lean_file: &Path,
    compile_output: Option<(&Path, &Path)>,
) -> Command {
    let mut cmd = serial_lean_command(&lean_dir);
    // `lake env` prepends the authenticated proof workspace; generated
    // dependency modules are the only inherited addition.
    cmd.env("LEAN_PATH", generated_modules);
    if let Some((module_root, olean)) = compile_output {
        cmd.arg("--root").arg(module_root).arg("-o").arg(olean);
    }
    cmd.arg(lean_file);
    cmd
}

fn run_lean_locked(
    _process_lock: &ProofProcessLock,
    environment: &ProofEnvironment,
    built: &Path,
    lean_file: &Path,
    expected_source: &str,
    mut command: Command,
) -> Result<StrictBatchLeanOutput, String> {
    environment.validate_built(built)?;
    require_generated_source(lean_file, expected_source, "before Lean checking")?;
    require_serial_lake_version(&built.join("lean"))?;
    let output = command
        .output()
        .map_err(|err| format!("failed to run `lean`: {err}"))?;
    environment.validate_built(built)?;
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

    Ok(StrictBatchLeanOutput {
        status_success: output.status.success(),
        stdout: output.stdout,
        messages,
    })
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
    require_generated_source(lean_file, expected_source, "before Lean checking")?;
    let generated_modules = modules_dir(repo_root);
    let command = generated_lean_command(
        &built.join("lean"),
        &generated_modules,
        lean_file,
        olean_out.map(|output| (generated_modules.as_path(), output)),
    );
    let process_lock = ProofProcessLock::acquire(repo_root)?;
    run_lean_locked(
        &process_lock,
        environment,
        &built,
        lean_file,
        expected_source,
        command,
    )
    .map(|output| output.messages)
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

fn require_observational_compilation_acceptance(
    emitted: &Emitted,
    output: &StrictBatchLeanOutput,
) -> Result<(), String> {
    if let Some(message) = output
        .messages
        .iter()
        .find(|message| message.severity == "error")
    {
        return Err(format!(
            "declaration observation Lean compilation reported an error on line {}: {}",
            message.line, message.data
        ));
    }
    if !output.status_success {
        return Err(
            "declaration observation Lean compilation exited unsuccessfully without an accepted result"
                .into(),
        );
    }
    if let Some(message) = output.messages.iter().find(|message| {
        diagnostic_disposition(emitted, message) == DiagnosticDisposition::FatalUnexpected
    }) {
        return Err(format!(
            "declaration observation Lean compilation emitted an unrecognized `{}` diagnostic on line {}: {}",
            message.severity, message.line, message.data
        ));
    }
    Ok(())
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
        DiagnosticDisposition, Emitted, EmittedNames, ExpectedDeclarationEnvelope, LeanMessage,
        MapEntry, MapTarget, UNEXPECTED_LEAN_WARNING_DIAGNOSTIC, diagnostic_disposition,
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
            declaration_envelope: ExpectedDeclarationEnvelope::default(),
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
            declaration_envelope: ExpectedDeclarationEnvelope::default(),
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
            declaration_envelope: ExpectedDeclarationEnvelope::default(),
            map: Vec::new(),
        }
    }

    fn empty_vc() -> VcResult {
        VcResult {
            ghosts: Vec::new(),
            classes: Vec::new(),
            records: Vec::new(),
            clause_wfs: Vec::new(),
            obligations: Vec::new(),
            transition_certificates: Vec::new(),
            argument_schedule_certificates: Vec::new(),
            trust: crate::vcgen::TrustManifest::default(),
            machine: crate::vcgen::MachineManifest::default(),
        }
    }

    fn draft_with_source(source: &str) -> EmittedDraft {
        EmittedDraft {
            lean_source: source.to_owned(),
            names: EmittedNames::default(),
            ingress: Vec::new(),
            declaration_envelope: ExpectedDeclarationEnvelope::default(),
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
    fn terminal_sentinel_is_framed_module_unique_and_last() {
        let pre_sentinel = "import Sable\n\n";
        let module = "SableGenerated_example_deadbeef";
        let expected_name = terminal_sentinel_name(module, pre_sentinel);
        let digest = expected_name
            .strip_prefix("SableGenerated.complete_")
            .expect("the sentinel has the reserved compiler prefix");
        assert_eq!(digest.len(), 64);
        assert!(digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert_ne!(
            expected_name,
            terminal_sentinel_name("SableGenerated_other_deadbeef", pre_sentinel)
        );
        assert_ne!(
            expected_name,
            terminal_sentinel_name(module, "import Sable\nopen Sable\n")
        );
        assert_ne!(
            terminal_sentinel_name("ab", "c\n"),
            terminal_sentinel_name("a", "bc\n"),
            "length framing prevents concatenation ambiguity"
        );

        let emitted = draft_with_source(pre_sentinel).finish(module);
        assert!(
            emitted
                .lean_source
                .ends_with(&format!("theorem {expected_name} : True := True.intro\n"))
        );
        assert_eq!(
            emitted.declaration_envelope.roots.last(),
            Some(&ExpectedDeclarationRoot {
                name: expected_name,
                kind: ExpectedDeclarationKind::TerminalSentinel,
            })
        );

        let mut missing = draft_with_source(pre_sentinel).finish(module);
        missing.declaration_envelope.roots.pop();
        assert!(require_terminal_sentinel(&missing).is_err());
        let mut nonterminal = draft_with_source(pre_sentinel).finish(module);
        nonterminal.lean_source.push_str("-- forged suffix\n");
        assert!(require_terminal_sentinel(&nonterminal).is_err());
    }

    fn declaration_module_fixture(
        module_name: &str,
        source_digest: &str,
    ) -> DeclarationModuleSubject {
        DeclarationModuleSubject {
            module_name: module_name.into(),
            generated_source_sha256: source_digest.into(),
            declaration_envelope: ExpectedDeclarationEnvelope {
                roots: vec![
                    ExpectedDeclarationRoot {
                        name: format!("{module_name}.Record"),
                        kind: ExpectedDeclarationKind::Structure {
                            fields: vec![
                                format!("{module_name}.Record.left"),
                                format!("{module_name}.Record.right"),
                            ],
                        },
                    },
                    ExpectedDeclarationRoot {
                        name: format!("{module_name}.definition"),
                        kind: ExpectedDeclarationKind::Definition {
                            recursive: true,
                            noncomputable: true,
                            simp: false,
                        },
                    },
                    ExpectedDeclarationRoot {
                        name: format!("{module_name}.fact"),
                        kind: ExpectedDeclarationKind::Theorem {
                            simp: true,
                            sable_fact: true,
                        },
                    },
                    ExpectedDeclarationRoot {
                        name: format!("{module_name}.complete"),
                        kind: ExpectedDeclarationKind::TerminalSentinel,
                    },
                ],
            },
        }
    }

    fn exact_observed_file(bytes: &[u8]) -> ExactObservedFile {
        ExactObservedFile {
            bytes: bytes.to_vec(),
            sha256: crate::sha256::hex(bytes),
        }
    }

    fn empty_declaration_inventory_result() -> Vec<u8> {
        concat!(
            r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
            "\n"
        )
        .as_bytes()
        .to_vec()
    }

    fn preflight_name(name: &str) -> ObservedName {
        observed_ascii_dotted_name(name).expect("fixture uses the pinned explicit-name spelling")
    }

    fn preflight_slot(name: ObservedName, kind: ObservedConstantKind) -> ObservedConstantSlot {
        ObservedConstantSlot {
            const_name: Some(name.clone()),
            info_name: Some(name),
            kind: Some(kind),
            safety: Some(ObservedConstantSafety::Safe),
        }
    }

    fn declaration_preflight_fixture() -> (ExpectedDeclarationEnvelope, DeclarationModuleInventory)
    {
        let envelope = ExpectedDeclarationEnvelope {
            roots: vec![
                ExpectedDeclarationRoot {
                    name: "Root.Record".into(),
                    kind: ExpectedDeclarationKind::Structure {
                        fields: vec!["Root.Record.data".into(), "Root.Record.proof".into()],
                    },
                },
                ExpectedDeclarationRoot {
                    name: "Root.definition".into(),
                    kind: ExpectedDeclarationKind::Definition {
                        recursive: true,
                        noncomputable: true,
                        simp: false,
                    },
                },
                ExpectedDeclarationRoot {
                    name: "Root.fact".into(),
                    kind: ExpectedDeclarationKind::Theorem {
                        simp: true,
                        sable_fact: true,
                    },
                },
                ExpectedDeclarationRoot {
                    name: "SableGenerated.complete_deadbeef".into(),
                    kind: ExpectedDeclarationKind::TerminalSentinel,
                },
            ],
        };
        let private_auxiliary = ObservedName::Num {
            prefix: Box::new(ObservedName::Str {
                prefix: Box::new(ObservedName::Anonymous),
                value: "_private".into(),
            }),
            value: 7,
        };
        // The explicit constants are intentionally not in envelope order.
        // The private numeric name and constructor remain unclassified.
        let inventory = DeclarationModuleInventory {
            observational: true,
            is_module: false,
            imports: vec![ObservedModuleImport {
                module: preflight_name("Sable"),
                import_all: true,
                is_exported: false,
                is_meta: false,
            }],
            constants: vec![
                preflight_slot(private_auxiliary, ObservedConstantKind::Opaque),
                preflight_slot(
                    preflight_name("SableGenerated.complete_deadbeef"),
                    ObservedConstantKind::Theorem,
                ),
                preflight_slot(
                    preflight_name("Root.Record.proof"),
                    ObservedConstantKind::Theorem,
                ),
                preflight_slot(
                    preflight_name("Root.Record"),
                    ObservedConstantKind::Inductive,
                ),
                preflight_slot(
                    preflight_name("Root.Record.data"),
                    ObservedConstantKind::Definition,
                ),
                preflight_slot(
                    preflight_name("Root.definition"),
                    ObservedConstantKind::Definition,
                ),
                preflight_slot(preflight_name("Root.fact"), ObservedConstantKind::Theorem),
                preflight_slot(
                    preflight_name("Root.Record.mk"),
                    ObservedConstantKind::Constructor,
                ),
                preflight_slot(
                    preflight_name("Root.unclassifiedQuotient"),
                    ObservedConstantKind::Quotient,
                ),
            ],
            extra_const_names: Vec::new(),
            extension_families: vec![ObservedExtensionFamily {
                name: preflight_name("Lean.exampleExtension"),
                count: 2,
            }],
        };
        (envelope, inventory)
    }

    #[test]
    fn declaration_audit_subject_has_one_exact_ordered_serialization() {
        let subject = DeclarationAuditSubject::new(
            "proof-environment-exact",
            "proof-policy-exact",
            declaration_module_fixture("Root", "root-source-sha256"),
            vec![declaration_module_fixture("Dep", "dep-source-sha256")],
        );
        let json = String::from_utf8(subject.canonical_json()).expect("canonical JSON is UTF-8");
        assert_eq!(
            json,
            r#"{"schema":"sable-declaration-audit-subject-v1","proof_environment_id":"proof-environment-exact","proof_policy":"proof-policy-exact","candidate":{"module_name":"Root","generated_source_sha256":"root-source-sha256","declaration_envelope":{"roots":[{"name":"Root.Record","kind":"structure","fields":["Root.Record.left","Root.Record.right"]},{"name":"Root.definition","kind":"definition","recursive":true,"noncomputable":true,"simp":false},{"name":"Root.fact","kind":"theorem","simp":true,"sable_fact":true},{"name":"Root.complete","kind":"terminal_sentinel"}]}},"dependencies":[{"module_name":"Dep","generated_source_sha256":"dep-source-sha256","declaration_envelope":{"roots":[{"name":"Dep.Record","kind":"structure","fields":["Dep.Record.left","Dep.Record.right"]},{"name":"Dep.definition","kind":"definition","recursive":true,"noncomputable":true,"simp":false},{"name":"Dep.fact","kind":"theorem","simp":true,"sable_fact":true},{"name":"Dep.complete","kind":"terminal_sentinel"}]}}]}"#
        );
        serde_json::from_str::<serde_json::Value>(&json)
            .expect("canonical subject remains valid JSON");
    }

    #[test]
    fn declaration_audit_subject_escapes_every_string_field() {
        let mut candidate = declaration_module_fixture("Root", "root-source");
        candidate.module_name = "Root\"\\\n".into();
        candidate.declaration_envelope.roots[0].name = "name\"\\\n".into();
        let subject = DeclarationAuditSubject::new(
            "proof\nenvironment",
            "policy\"\\",
            candidate,
            vec![declaration_module_fixture("Dep\t", "dep-source")],
        );
        let json = subject.canonical_json();
        let parsed: serde_json::Value =
            serde_json::from_slice(&json).expect("all subject strings are JSON escaped");
        assert_eq!(parsed["proof_environment_id"], "proof\nenvironment");
        assert_eq!(parsed["proof_policy"], "policy\"\\");
        assert_eq!(parsed["candidate"]["module_name"], "Root\"\\\n");
        assert_eq!(
            parsed["candidate"]["declaration_envelope"]["roots"][0]["name"],
            "name\"\\\n"
        );
        assert_eq!(parsed["dependencies"][0]["module_name"], "Dep\t");
    }

    #[test]
    fn declaration_dependency_identity_binds_order_source_envelope_and_policy() {
        let dependency_a = declaration_module_fixture("A", "source-a");
        let dependency_b = declaration_module_fixture("B", "source-b");
        let candidate = declaration_module_fixture("Root", "root-source");
        let canonical = |proof_environment: &str,
                         proof_policy: &str,
                         dependencies: Vec<DeclarationModuleSubject>| {
            DeclarationAuditSubject::new(
                proof_environment,
                proof_policy,
                candidate.clone(),
                dependencies,
            )
            .canonical_json()
        };
        let exact = canonical(
            "proof-environment",
            "proof-policy",
            vec![dependency_a.clone(), dependency_b.clone()],
        );
        assert_ne!(
            exact,
            canonical(
                "proof-environment",
                "proof-policy",
                vec![dependency_b.clone(), dependency_a.clone()]
            ),
            "dependency order is part of the future request subject"
        );
        let mut changed_source = dependency_a.clone();
        changed_source.generated_source_sha256 = "changed-source-a".into();
        assert_ne!(
            exact,
            canonical(
                "proof-environment",
                "proof-policy",
                vec![changed_source, dependency_b.clone()]
            )
        );
        let mut changed_attribute = dependency_a.clone();
        let ExpectedDeclarationKind::Theorem { sable_fact, .. } =
            &mut changed_attribute.declaration_envelope.roots[2].kind
        else {
            panic!("fixture root 2 is a theorem")
        };
        *sable_fact = false;
        assert_ne!(
            exact,
            canonical(
                "proof-environment",
                "proof-policy",
                vec![changed_attribute, dependency_b.clone()]
            )
        );
        assert_ne!(
            exact,
            canonical(
                "different-proof-environment",
                "proof-policy",
                vec![dependency_a.clone(), dependency_b.clone()]
            )
        );
        assert_ne!(
            exact,
            canonical(
                "proof-environment",
                "different-proof-policy",
                vec![dependency_a, dependency_b]
            )
        );
    }

    #[test]
    fn declaration_observation_candidate_path_is_scoped_unique_and_self_cleaning() {
        let root = unique_directory(
            &std::env::temp_dir(),
            "sable-declaration-observation-path-test",
        )
        .expect("create isolated observation path tree");
        let _cleanup = TempProofTree(root.clone());
        std::fs::create_dir_all(modules_dir(&root)).expect("create generated-module directory");

        let first = unique_declaration_candidate_olean(&root, "Root_module")
            .expect("allocate first candidate capability");
        let second = unique_declaration_candidate_olean(&root, "Root_module")
            .expect("allocate second candidate capability");
        assert_ne!(first.path(), second.path());
        assert_eq!(first.path().parent(), Some(first.directory.as_path()));
        assert_eq!(first.directory.parent(), Some(modules_dir(&root).as_path()));
        assert!(first.path().is_absolute());
        assert_eq!(
            first.path().file_name().and_then(|name| name.to_str()),
            Some("Root_module.olean")
        );
        assert!(
            first
                .directory
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with(".Root_module.declaration-output."))
        );

        let first_path = first.path().to_path_buf();
        let first_directory = first.directory.clone();
        std::fs::write(&first_path, b"future temporary candidate")
            .expect("write only the capability-owned candidate path");
        require_declaration_candidate_output_state(
            &first,
            DeclarationCandidateOutputState::TraditionalOlean,
        )
        .expect("one regular traditional olean is the exact admitted output set");
        let server_sidecar = declaration_candidate_output_paths(&first)[1].clone();
        std::fs::write(&server_sidecar, b"future module-system sidecar")
            .expect("write rejected sidecar fixture");
        assert!(
            require_declaration_candidate_output_state(
                &first,
                DeclarationCandidateOutputState::TraditionalOlean,
            )
            .is_err()
        );
        drop(first);
        assert!(
            std::fs::symlink_metadata(&first_path).is_err(),
            "dropping the capability removes its regular temporary candidate"
        );
        assert!(std::fs::symlink_metadata(&server_sidecar).is_err());
        assert!(std::fs::symlink_metadata(&first_directory).is_err());

        assert!(unique_declaration_candidate_olean(&root, "../escape").is_err());
        assert!(unique_declaration_candidate_olean(Path::new("relative"), "Root_module").is_err());
        drop(second);
    }

    #[test]
    fn declaration_compilation_source_lifecycle_is_exact_and_nonrecursive() {
        let root = unique_directory(
            &std::env::temp_dir(),
            "sable-declaration-compilation-source-test",
        )
        .expect("create isolated compilation source tree");
        let _cleanup = TempProofTree(root.clone());
        let exact_source = "import Sable\n\n";

        let source = unique_declaration_candidate_source(&root, "Root_module", exact_source)
            .expect("allocate exact temporary source");
        assert_eq!(
            source.path.file_name().and_then(|name| name.to_str()),
            Some("Root_module.lean")
        );
        assert_eq!(source.path.parent(), Some(source.directory.as_path()));
        assert_eq!(
            source.directory.parent(),
            Some(modules_dir(&root).as_path())
        );
        validate_declaration_candidate_source(&root, &source)
            .expect("one exact regular source is the complete workspace");
        let observed = observe_regular_file(&source.path, "test source")
            .expect("observe exact regular source");
        require_exact_observed_source(&observed, exact_source, "in the test")
            .expect("source bytes and digest match");
        let source_dir = source.directory.clone();
        let source_path = source.path.clone();
        drop(source);
        assert!(std::fs::symlink_metadata(&source_path).is_err());
        assert!(std::fs::symlink_metadata(&source_dir).is_err());

        let changed = unique_declaration_candidate_source(&root, "Changed", exact_source)
            .expect("allocate mutation fixture");
        std::fs::write(&changed.path, "import Sable\n-- changed\n").expect("mutate owned fixture");
        let changed_bytes = observe_regular_file(&changed.path, "changed test source")
            .expect("observe changed source");
        assert!(
            require_exact_observed_source(&changed_bytes, exact_source, "after mutation").is_err()
        );
        drop(changed);

        let residual = unique_declaration_candidate_source(&root, "Residual", exact_source)
            .expect("allocate residual fixture");
        let residual_dir = residual.directory.clone();
        let residual_source = residual.path.clone();
        std::fs::write(residual_dir.join("unexpected.output"), b"unmodeled")
            .expect("write unexpected residual");
        assert!(validate_declaration_candidate_source(&root, &residual).is_err());
        drop(residual);
        assert!(std::fs::symlink_metadata(&residual_source).is_err());
        assert!(
            residual_dir.is_dir(),
            "nonrecursive cleanup leaves an unexpected residual visible"
        );

        let preexisting = unique_declaration_candidate_olean(&root, "Preexisting")
            .expect("allocate output capability");
        std::fs::write(preexisting.path(), b"preexisting candidate")
            .expect("create candidate before compilation");
        assert!(require_absent_candidate(&preexisting).is_err());
        drop(preexisting);
    }

    #[test]
    fn declaration_compilation_source_rejects_a_replacement_symlink() {
        use std::os::unix::fs::symlink;

        let root = unique_directory(
            &std::env::temp_dir(),
            "sable-declaration-compilation-symlink-test",
        )
        .expect("create isolated symlink test tree");
        let _cleanup = TempProofTree(root.clone());
        let source = unique_declaration_candidate_source(&root, "Root_module", "import Sable\n")
            .expect("allocate source fixture");
        let target = root.join("attacker-controlled.lean");
        std::fs::write(&target, "import Sable\n").expect("write symlink target");
        std::fs::remove_file(&source.path).expect("replace owned source fixture");
        symlink(&target, &source.path).expect("install replacement symlink");
        assert!(validate_declaration_candidate_source(&root, &source).is_err());
        assert!(observe_regular_file(&source.path, "replacement source").is_err());
        let source_dir = source.directory.clone();
        drop(source);
        assert!(
            source_dir.is_dir(),
            "cleanup refuses to follow or remove a replacement symlink"
        );
    }

    #[test]
    fn declaration_compilation_gate_requires_exit_zero_no_errors_and_owned_warnings() {
        let emitted = Emitted {
            lean_source: String::new(),
            names: EmittedNames::default(),
            ingress: Vec::new(),
            declaration_envelope: ExpectedDeclarationEnvelope::default(),
            map: vec![MapEntry {
                first_line: 7,
                last_line: 9,
                target: MapTarget::Obligation(0),
            }],
        };
        let allowed_warning = LeanMessage {
            severity: "warning".into(),
            line: 8,
            data: "expensive automation: `grind` closed this goal using 20k of its \
                   100k-heartbeat budget — consider a `discharge` script"
                .into(),
        };
        let information = LeanMessage {
            severity: "information".into(),
            line: 8,
            data: "Try this:\n  grind only [foo]".into(),
        };
        require_observational_compilation_acceptance(
            &emitted,
            &StrictBatchLeanOutput {
                status_success: true,
                stdout: Vec::new(),
                messages: vec![allowed_warning.clone(), information],
            },
        )
        .expect("the existing owned expensive-automation exception remains nonfatal");

        for output in [
            StrictBatchLeanOutput {
                status_success: false,
                stdout: Vec::new(),
                messages: Vec::new(),
            },
            StrictBatchLeanOutput {
                status_success: false,
                stdout: Vec::new(),
                messages: vec![LeanMessage {
                    severity: "error".into(),
                    line: 1,
                    data: "failed proof".into(),
                }],
            },
            StrictBatchLeanOutput {
                status_success: true,
                stdout: Vec::new(),
                messages: vec![LeanMessage {
                    severity: "error".into(),
                    line: 1,
                    data: "error despite exit zero".into(),
                }],
            },
            StrictBatchLeanOutput {
                status_success: true,
                stdout: Vec::new(),
                messages: vec![LeanMessage {
                    severity: "warning".into(),
                    line: 8,
                    data: "declaration uses 'sorry'".into(),
                }],
            },
            StrictBatchLeanOutput {
                status_success: true,
                stdout: Vec::new(),
                messages: vec![LeanMessage {
                    severity: allowed_warning.severity.clone(),
                    line: 10,
                    data: allowed_warning.data.clone(),
                }],
            },
        ] {
            assert!(require_observational_compilation_acceptance(&emitted, &output).is_err());
        }
    }

    #[test]
    fn declaration_observation_binds_exact_subject_ready_candidate_and_transport() {
        let root = unique_directory(
            &std::env::temp_dir(),
            "sable-declaration-observation-binding-test",
        )
        .expect("create isolated observation binding tree");
        let _cleanup = TempProofTree(root.clone());
        std::fs::create_dir_all(modules_dir(&root)).expect("create generated-module directory");
        let candidate = unique_declaration_candidate_olean(&root, "Root_module")
            .expect("allocate candidate capability");
        let emitted = draft_with_source("import Sable\n\n").finish("Root_module");
        let subject = DeclarationAuditSubject::new(
            "proof-environment-exact",
            "proof-policy-exact",
            DeclarationModuleSubject::from_emitted("Root_module", &emitted),
            vec![declaration_module_fixture(
                "Dependency",
                "dependency-source-sha256",
            )],
        );
        let ready = b"sable-proof-ready-v3\nproof-environment:proof-environment-exact\n";
        let candidate_bytes = b"exact candidate olean bytes";
        let request = declaration_inventory_request(candidate.path())
            .expect("candidate has one exact inventory request");
        let result = empty_declaration_inventory_result();
        let observation = bind_declaration_observation(
            "proof-environment-exact",
            "proof-policy-exact",
            &subject,
            &emitted,
            &candidate,
            exact_observed_file(ready),
            exact_observed_file(ready),
            exact_observed_file(candidate_bytes),
            exact_observed_file(candidate_bytes),
            request.clone(),
            true,
            result.clone(),
            Vec::new(),
        )
        .expect("stable exact observational evidence binds");

        assert!(observation.observational);
        assert!(!observation.authoritative);
        assert_eq!(observation.expected_module_name, "Root_module");
        assert_eq!(observation.declaration_subject, subject);
        assert_eq!(
            observation.declaration_subject_sha256,
            crate::sha256::hex(&subject.canonical_json())
        );
        assert_eq!(observation.proof_ready_bytes, ready);
        assert_eq!(
            observation.proof_ready_sha256_before,
            observation.proof_ready_sha256_after
        );
        assert_eq!(
            observation.candidate_olean_sha256_before,
            observation.candidate_olean_sha256_after
        );
        assert_eq!(observation.inventory_request, request);
        assert_eq!(observation.inventory_result, result);
        assert!(observation.inventory.observational);
        assert!(!observation.inventory.is_module);

        let canonical = observation.canonical_json();
        let parsed: serde_json::Value =
            serde_json::from_slice(&canonical).expect("observation binding is exact JSON");
        assert_eq!(parsed["schema"], DECLARATION_OBSERVATION_SCHEMA);
        assert_eq!(parsed["observational"], true);
        assert_eq!(parsed["authoritative"], false);
        assert_eq!(parsed["expected_module_name"], "Root_module");
        assert_eq!(
            parsed["declaration_audit_subject"],
            serde_json::from_slice::<serde_json::Value>(&subject.canonical_json())
                .expect("subject is JSON")
        );
        assert_eq!(
            parsed["proof_ready_utf8"],
            std::str::from_utf8(ready).expect("fixture READY is UTF-8")
        );
        assert_eq!(
            parsed["inventory_request_utf8"],
            std::str::from_utf8(&request).expect("request is UTF-8")
        );
        assert_eq!(
            parsed["inventory_result_utf8"],
            std::str::from_utf8(&result).expect("result is UTF-8")
        );
        assert_eq!(observation.canonical_sha256().len(), 64);
        assert!(
            observation
                .canonical_sha256()
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        );
    }

    #[test]
    fn declaration_observation_rejects_every_changed_binding_input() {
        let root = unique_directory(
            &std::env::temp_dir(),
            "sable-declaration-observation-rejection-test",
        )
        .expect("create isolated observation rejection tree");
        let _cleanup = TempProofTree(root.clone());
        std::fs::create_dir_all(modules_dir(&root)).expect("create generated-module directory");
        let candidate = unique_declaration_candidate_olean(&root, "Root_module")
            .expect("allocate candidate capability");
        let emitted = draft_with_source("import Sable\n\n").finish("Root_module");
        let subject = DeclarationAuditSubject::new(
            "proof-environment",
            "proof-policy",
            DeclarationModuleSubject::from_emitted("Root_module", &emitted),
            Vec::new(),
        );
        let ready = b"exact READY bytes\n";
        let candidate_bytes = b"exact candidate bytes";
        let request = declaration_inventory_request(candidate.path()).expect("exact request");
        let result = empty_declaration_inventory_result();
        let bind = |subject: &DeclarationAuditSubject,
                    emitted: &Emitted,
                    ready_after: &[u8],
                    candidate_after: &[u8],
                    request: Vec<u8>,
                    status_success: bool,
                    result: Vec<u8>,
                    stderr: Vec<u8>| {
            bind_declaration_observation(
                "proof-environment",
                "proof-policy",
                subject,
                emitted,
                &candidate,
                exact_observed_file(ready),
                exact_observed_file(ready_after),
                exact_observed_file(candidate_bytes),
                exact_observed_file(candidate_after),
                request,
                status_success,
                result,
                stderr,
            )
        };

        let mut changed_envelope = subject.clone();
        changed_envelope.candidate.declaration_envelope.roots.pop();
        assert!(
            bind(
                &changed_envelope,
                &emitted,
                ready,
                candidate_bytes,
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        let relabeled_emitted = draft_with_source("import Sable\n\n").finish("Original_module");
        let relabeled_subject = DeclarationAuditSubject::new(
            "proof-environment",
            "proof-policy",
            DeclarationModuleSubject::from_emitted("Root_module", &relabeled_emitted),
            Vec::new(),
        );
        assert!(
            bind(
                &relabeled_subject,
                &relabeled_emitted,
                ready,
                candidate_bytes,
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err(),
            "an Emitted value finalized for another module cannot be relabeled"
        );
        let changed_emitted =
            draft_with_source("import Sable\n-- changed source\n\n").finish("Root_module");
        assert!(
            bind(
                &subject,
                &changed_emitted,
                ready,
                candidate_bytes,
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind_declaration_observation(
                "different-proof-environment",
                "proof-policy",
                &subject,
                &emitted,
                &candidate,
                exact_observed_file(ready),
                exact_observed_file(ready),
                exact_observed_file(candidate_bytes),
                exact_observed_file(candidate_bytes),
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind_declaration_observation(
                "proof-environment",
                "different-proof-policy",
                &subject,
                &emitted,
                &candidate,
                exact_observed_file(ready),
                exact_observed_file(ready),
                exact_observed_file(candidate_bytes),
                exact_observed_file(candidate_bytes),
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        let mut forged_digest = exact_observed_file(candidate_bytes);
        forged_digest.sha256 = crate::sha256::hex(b"different bytes");
        assert!(
            bind_declaration_observation(
                "proof-environment",
                "proof-policy",
                &subject,
                &emitted,
                &candidate,
                exact_observed_file(ready),
                exact_observed_file(ready),
                forged_digest.clone(),
                forged_digest,
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind(
                &subject,
                &emitted,
                b"changed READY bytes\n",
                candidate_bytes,
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind(
                &subject,
                &emitted,
                ready,
                b"changed candidate bytes",
                request.clone(),
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        let mut changed_request = request.clone();
        changed_request.push(b' ');
        assert!(
            bind(
                &subject,
                &emitted,
                ready,
                candidate_bytes,
                changed_request,
                true,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind(
                &subject,
                &emitted,
                ready,
                candidate_bytes,
                request.clone(),
                false,
                result.clone(),
                Vec::new(),
            )
            .is_err()
        );
        assert!(
            bind(
                &subject,
                &emitted,
                ready,
                candidate_bytes,
                request.clone(),
                true,
                result.clone(),
                b"warning\n".to_vec(),
            )
            .is_err()
        );
        assert!(
            bind(
                &subject,
                &emitted,
                ready,
                candidate_bytes,
                request,
                true,
                b"{}\n".to_vec(),
                Vec::new(),
            )
            .is_err()
        );
    }

    #[test]
    fn module_subject_reconstructs_identically_from_deterministic_emission() {
        let first = draft_with_source("import Sable\n\n").finish("Root_module");
        let repeated = draft_with_source("import Sable\n\n").finish("Root_module");
        let first_subject = DeclarationModuleSubject::from_emitted("Root_module", &first);
        let repeated_subject = DeclarationModuleSubject::from_emitted("Root_module", &repeated);
        assert_eq!(first_subject, repeated_subject);

        let changed = draft_with_source("import Sable\nopen Sable\n").finish("Root_module");
        assert_ne!(
            first_subject,
            DeclarationModuleSubject::from_emitted("Root_module", &changed)
        );
        assert_ne!(
            repeated_subject,
            DeclarationModuleSubject::from_emitted("Other_module", &repeated)
        );
    }

    #[test]
    fn ghost_ingress_binds_owned_modifiers_and_typed_roots() {
        let mut vc = empty_vc();
        vc.ghosts = vec![
            crate::ast::GhostItem {
                keyword: "def",
                unfold: false,
                fact: false,
                text: "successor (x : Int) : Int := x + 1".into(),
                span: Span::new(2, 20),
            },
            crate::ast::GhostItem {
                keyword: "def",
                unfold: false,
                fact: false,
                text: "countdown (n : Nat) : Nat := if n = 0 then 0 else countdown (n - 1)\ntermination_by n\ndecreasing_by omega".into(),
                span: Span::new(21, 90),
            },
            crate::ast::GhostItem {
                keyword: "theorem",
                unfold: true,
                fact: true,
                text: "useful' (x : Int) : x = x := rfl".into(),
                span: Span::new(91, 130),
            },
        ];

        let emitted = emit(
            &vc,
            &[],
            &std::collections::HashSet::new(),
            &[],
            &EmittedNames::default(),
        )
        .finish("SableGeneratedGhostTest");
        let commands = emitted
            .ingress
            .iter()
            .filter(|fragment| fragment.category == "command")
            .collect::<Vec<_>>();
        assert_eq!(commands.len(), 3);
        assert_eq!(
            commands[0].text,
            "@[simp] noncomputable def successor (x : Int) : Int := x + 1"
        );
        assert_eq!(commands[0].expected_modifiers, "@[simp] noncomputable ");
        assert!(commands[1].text.starts_with("noncomputable def countdown"));
        assert_eq!(commands[1].expected_modifiers, "noncomputable ");
        assert_eq!(
            commands[2].text,
            "@[simp] @[sable_fact] theorem useful' (x : Int) : x = x := rfl"
        );
        assert_eq!(commands[2].expected_modifiers, "@[simp] @[sable_fact] ");

        assert_eq!(
            &emitted.declaration_envelope.roots[..3],
            &[
                ExpectedDeclarationRoot {
                    name: "successor".into(),
                    kind: ExpectedDeclarationKind::Definition {
                        recursive: false,
                        noncomputable: true,
                        simp: true,
                    },
                },
                ExpectedDeclarationRoot {
                    name: "countdown".into(),
                    kind: ExpectedDeclarationKind::Definition {
                        recursive: true,
                        noncomputable: true,
                        simp: false,
                    },
                },
                ExpectedDeclarationRoot {
                    name: "useful'".into(),
                    kind: ExpectedDeclarationKind::Theorem {
                        simp: true,
                        sable_fact: true,
                    },
                },
            ]
        );

        let request: serde_json::Value = serde_json::from_slice(
            &ingress_audit_request(&emitted).expect("ingress request serializes"),
        )
        .expect("ingress request is JSON");
        assert_eq!(request["schema"], INGRESS_REQUEST_SCHEMA);
        assert_eq!(
            request["fragments"][0]["expected_modifiers"],
            "@[simp] noncomputable "
        );
        assert_eq!(request["fragments"][0]["expected_kind"], "definition");
        assert_eq!(request["fragments"][0]["expected_name"], "successor");
    }

    #[test]
    fn record_and_clause_helpers_are_explicitly_noncomputable_roots() {
        let mut vc = empty_vc();
        vc.records.push(crate::vcgen::RecordEmit {
            name: "Pair".into(),
            fields: vec![
                crate::vcgen::RecordFieldEmit {
                    name: "left".into(),
                    lean_ty: "Int".into(),
                    layout: "Sable.Layout.int".into(),
                    offset: 0,
                    wf: None,
                },
                crate::vcgen::RecordFieldEmit {
                    name: "right".into(),
                    lean_ty: "Int".into(),
                    layout: "Sable.Layout.int".into(),
                    offset: 8,
                    wf: None,
                },
            ],
            layout: crate::ast::StorageLayout { size: 16, align: 8 },
            span: Span::new(2, 40),
        });
        vc.clause_wfs.push(crate::vcgen::ClauseWf {
            def_name: "clause_wf".into(),
            binders: vec![("x".into(), "Int".into())],
            text: "0 ≤ x".into(),
            span: Span::new(41, 50),
            desc: "test clause".into(),
            result_ty: "Prop",
        });

        let emitted = emit(
            &vc,
            &[],
            &std::collections::HashSet::new(),
            &[],
            &EmittedNames::default(),
        )
        .finish("SableGeneratedRecordTest");
        for declaration in [
            "layout",
            "leftOffset",
            "rightOffset",
            "wf",
            "cellWf",
            "fromSpan",
            "toSpan",
            "clause_wf",
        ] {
            assert!(
                emitted
                    .lean_source
                    .contains(&format!("noncomputable def {declaration}")),
                "generated proof helper `{declaration}` must suppress code generation"
            );
        }
        assert_eq!(
            emitted.declaration_envelope.roots.first(),
            Some(&ExpectedDeclarationRoot {
                name: "SableR_Pair".into(),
                kind: ExpectedDeclarationKind::Structure {
                    fields: vec!["SableR_Pair.left".into(), "SableR_Pair.right".into()],
                },
            })
        );
        for root in &emitted.declaration_envelope.roots {
            if let ExpectedDeclarationKind::Definition { noncomputable, .. } = &root.kind {
                assert!(
                    *noncomputable,
                    "proof definition {} is noncomputable",
                    root.name
                );
            }
        }
        assert!(
            emitted
                .declaration_envelope
                .roots
                .iter()
                .any(|root| root.name == "clause_wf")
        );
    }

    #[test]
    fn ingress_auditor_transport_accepts_only_the_exact_result_schema() {
        let emitted = emitted_with_ingress();
        let accepted = b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":true}\n";
        parse_ingress_audit_output(&emitted, true, accepted, b"")
            .expect("the exact accepted result passes");

        for stdout in [
            b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":true}".as_slice(),
            b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":true}\r\n".as_slice(),
            b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":true,\"extra\":0}\n"
                .as_slice(),
            b"ok\n".as_slice(),
        ] {
            assert!(parse_ingress_audit_output(&emitted, true, stdout, b"").is_err());
        }
        assert!(parse_ingress_audit_output(&emitted, false, accepted, b"").is_err());
        assert!(parse_ingress_audit_output(&emitted, true, accepted, b"warning\n").is_err());
        let forged_kind = b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":false,\"failure_kind\":\"forged\",\"message\":\"accepted by loose parser\"}\n";
        assert!(parse_ingress_audit_output(&emitted, true, forged_kind, b"").is_err());
    }

    #[test]
    fn declaration_inventory_request_is_one_exact_observational_subject() {
        assert_eq!(
            declaration_inventory_request(Path::new("/tmp/Candidate.olean"))
                .expect("UTF-8 candidate path serializes"),
            br#"{"candidate_olean":"/tmp/Candidate.olean","schema":"sable-declaration-inventory-request-v1"}"#
        );
        assert!(declaration_inventory_request(Path::new("")).is_err());
    }

    #[test]
    fn declaration_inventory_transport_preserves_order_flags_and_structural_names() {
        let output = concat!(
            r#"{"constants":[{"const_name":{"some":{"str":[{"str":[null,"Sable"]},"fact"]}},"info_name":{"some":{"str":[{"str":[null,"Sable"]},"fact"]}},"kind":"theorem","safety":"safe"},{"const_name":{"some":{"str":[null,"unpaired"]}},"info_name":null,"kind":null,"safety":null},{"const_name":null,"info_name":{"some":{"num":[{"str":[null,"_hyg"]},7]}},"kind":"definition","safety":"partial"}],"extension_families":[{"count":2,"name":{"str":[null,"@family"]}}],"extra_const_names":[{"num":[null,42]}],"imports":[{"import_all":true,"is_exported":false,"is_meta":true,"module":{"str":[null,"Sable"]}}],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
            "\n"
        );
        let inventory = parse_declaration_inventory_output(true, output.as_bytes(), b"")
            .expect("the exact canonical observational inventory passes");
        assert!(inventory.observational);
        assert!(!inventory.is_module);
        assert_eq!(
            inventory.imports,
            vec![ObservedModuleImport {
                module: ObservedName::Str {
                    prefix: Box::new(ObservedName::Anonymous),
                    value: "Sable".into(),
                },
                import_all: true,
                is_exported: false,
                is_meta: true,
            }]
        );
        assert_eq!(inventory.constants.len(), 3);
        assert_eq!(
            inventory.constants[0].kind,
            Some(ObservedConstantKind::Theorem)
        );
        assert_eq!(
            inventory.constants[0].safety,
            Some(ObservedConstantSafety::Safe)
        );
        assert!(inventory.constants[1].const_name.is_some());
        assert!(inventory.constants[1].info_name.is_none());
        assert!(inventory.constants[2].const_name.is_none());
        assert_eq!(
            inventory.constants[2].info_name,
            Some(ObservedName::Num {
                prefix: Box::new(ObservedName::Str {
                    prefix: Box::new(ObservedName::Anonymous),
                    value: "_hyg".into(),
                }),
                value: 7,
            })
        );
        assert_eq!(
            inventory.extra_const_names,
            vec![ObservedName::Num {
                prefix: Box::new(ObservedName::Anonymous),
                value: 42,
            }]
        );
        assert_eq!(inventory.extension_families[0].count, 2);
    }

    #[test]
    fn declaration_preflight_maps_only_exact_ascii_dotted_names() {
        assert_eq!(
            observed_ascii_dotted_name("SableR_Node.proof'")
                .expect("the narrow dotted/apostrophe spelling maps exactly"),
            ObservedName::Str {
                prefix: Box::new(ObservedName::Str {
                    prefix: Box::new(ObservedName::Anonymous),
                    value: "SableR_Node".into(),
                }),
                value: "proof'".into(),
            }
        );
        for invalid in [
            "",
            ".Root",
            "Root.",
            "Root..field",
            "Root.7",
            "7Root",
            "_",
            "Root.«field»",
            "Root.field-name",
            "Røot.field",
        ] {
            assert!(
                observed_ascii_dotted_name(invalid).is_err(),
                "`{invalid}` is outside the pinned explicit-name spelling"
            );
        }
        let nested = observed_ascii_dotted_name("Root.field").expect("valid nested name");
        assert_ne!(
            nested,
            ObservedName::Str {
                prefix: Box::new(ObservedName::Anonymous),
                value: "Root.field".into(),
            },
            "a printable dotted component is not a structural dotted name"
        );
        assert_ne!(
            nested,
            ObservedName::Num {
                prefix: Box::new(preflight_name("Root")),
                value: 1,
            },
            "numeric hygienic components are never inferred from text"
        );
    }

    #[test]
    fn declaration_preflight_matches_explicit_names_and_retains_every_unknown() {
        let (envelope, inventory) = declaration_preflight_fixture();
        let preflight = preflight_declaration_inventory(&envelope, &inventory)
            .expect("the coarse denial-only fixture passes");

        assert!(preflight.observational);
        assert!(!preflight.authoritative);
        assert_eq!(preflight.explicit_matches.len(), 6);
        assert_eq!(
            preflight
                .explicit_matches
                .iter()
                .map(|matched| matched.slot_index)
                .collect::<Vec<_>>(),
            vec![3, 4, 2, 5, 6, 1],
            "lookup is by exact structural name while output retains envelope order"
        );
        assert!(matches!(
            &preflight.explicit_matches[0].role,
            DeclarationInventoryExplicitRole::StructureRoot { root_index: 0 }
        ));
        assert!(matches!(
            &preflight.explicit_matches[2].role,
            DeclarationInventoryExplicitRole::StructureField {
                root_index: 0,
                field_index: 1,
            }
        ));
        assert!(matches!(
            &preflight.explicit_matches[5].role,
            DeclarationInventoryExplicitRole::TerminalSentinel { root_index: 3 }
        ));
        assert_eq!(
            preflight
                .unclassified_constants
                .iter()
                .map(|constant| (constant.slot_index, constant.kind))
                .collect::<Vec<_>>(),
            vec![
                (0, ObservedConstantKind::Opaque),
                (7, ObservedConstantKind::Constructor),
                (8, ObservedConstantKind::Quotient),
            ],
            "safe-bit constants outside the explicit envelope remain policy-unclassified in slot order"
        );
        assert!(matches!(
            &preflight.unclassified_constants[0].name,
            ObservedName::Num { value: 7, .. }
        ));
        assert_eq!(inventory.imports.len(), 1);
        assert_eq!(inventory.extension_families.len(), 1);
        assert_eq!(inventory.extension_families[0].count, 2);
    }

    #[test]
    fn declaration_preflight_rejects_every_global_denial_condition() {
        let (envelope, base) = declaration_preflight_fixture();
        let mut cases = Vec::new();

        let mut inventory = base.clone();
        inventory.observational = false;
        cases.push(("non-observational input", inventory));

        let mut inventory = base.clone();
        inventory.is_module = true;
        cases.push(("module-system output", inventory));

        let mut inventory = base.clone();
        inventory
            .extra_const_names
            .push(preflight_name("Root.codegen_extra"));
        cases.push(("code-generation extras", inventory));

        let mut inventory = base.clone();
        inventory.constants[3].const_name = None;
        cases.push(("missing constNames side", inventory));

        let mut inventory = base.clone();
        inventory.constants[3].kind = None;
        cases.push(("missing kind", inventory));

        let mut inventory = base.clone();
        inventory.constants[3].info_name = Some(preflight_name("Root.Other"));
        cases.push(("mismatched parallel names", inventory));

        let mut inventory = base.clone();
        let duplicate = inventory.constants[3].clone();
        inventory.constants.push(duplicate);
        cases.push(("duplicate structural name", inventory));

        let mut inventory = base.clone();
        inventory.constants[0].kind = Some(ObservedConstantKind::Axiom);
        cases.push(("candidate axiom", inventory));

        let mut inventory = base.clone();
        inventory.constants[0].safety = Some(ObservedConstantSafety::Unsafe);
        cases.push(("unclassified unsafe constant", inventory));

        let mut inventory = base.clone();
        inventory.constants[0].safety = Some(ObservedConstantSafety::Partial);
        cases.push(("unclassified partial constant", inventory));

        let mut inventory = base.clone();
        inventory.constants[0].const_name = Some(ObservedName::Anonymous);
        inventory.constants[0].info_name = Some(ObservedName::Anonymous);
        cases.push(("anonymous constant", inventory));

        let mut inventory = base;
        inventory.constants.push(preflight_slot(
            preflight_name("SableGenerated.complete_unexpected"),
            ObservedConstantKind::Theorem,
        ));
        cases.push(("additional reserved sentinel", inventory));

        for (description, inventory) in cases {
            assert!(
                preflight_declaration_inventory(&envelope, &inventory).is_err(),
                "{description} must fail closed"
            );
        }
    }

    #[test]
    fn declaration_preflight_rejects_missing_wrong_or_ambiguous_explicit_declarations() {
        let (base_envelope, base_inventory) = declaration_preflight_fixture();
        let mut cases = Vec::new();

        let mut inventory = base_inventory.clone();
        inventory.constants.remove(3);
        cases.push(("missing structure root", base_envelope.clone(), inventory));

        let mut inventory = base_inventory.clone();
        inventory.constants.remove(4);
        cases.push(("missing structure field", base_envelope.clone(), inventory));

        for (description, slot, kind) in [
            ("wrong structure kind", 3, ObservedConstantKind::Definition),
            ("wrong field kind", 4, ObservedConstantKind::Constructor),
            ("wrong definition kind", 5, ObservedConstantKind::Theorem),
            ("wrong theorem kind", 6, ObservedConstantKind::Definition),
            ("wrong sentinel kind", 1, ObservedConstantKind::Definition),
        ] {
            let mut inventory = base_inventory.clone();
            inventory.constants[slot].kind = Some(kind);
            cases.push((description, base_envelope.clone(), inventory));
        }

        let mut envelope = base_envelope.clone();
        envelope.roots.pop();
        cases.push((
            "missing expected sentinel",
            envelope,
            base_inventory.clone(),
        ));

        let mut envelope = base_envelope.clone();
        envelope.roots[1].kind = ExpectedDeclarationKind::TerminalSentinel;
        cases.push((
            "non-final expected sentinel",
            envelope,
            base_inventory.clone(),
        ));

        let mut envelope = base_envelope.clone();
        let duplicate_name = envelope.roots[1].name.clone();
        envelope.roots[2].name = duplicate_name;
        cases.push(("duplicate expected name", envelope, base_inventory.clone()));

        let mut envelope = base_envelope.clone();
        envelope.roots[1].name = "Root.7invalid".into();
        cases.push((
            "invalid expected spelling",
            envelope,
            base_inventory.clone(),
        ));

        let mut envelope = base_envelope.clone();
        envelope.roots.last_mut().expect("sentinel root").name = "Root.complete_deadbeef".into();
        cases.push((
            "sentinel outside reserved prefix",
            envelope,
            base_inventory.clone(),
        ));

        for (description, envelope, inventory) in cases {
            assert!(
                preflight_declaration_inventory(&envelope, &inventory).is_err(),
                "{description} must fail closed"
            );
        }
    }

    #[test]
    #[ignore = "cross-language canary; requires explicit built inventory executable and candidate olean paths"]
    fn declaration_inventory_cross_language_canary() {
        use std::io::Write as _;

        let regular_env_path = |name: &str| {
            let path = PathBuf::from(
                std::env::var_os(name)
                    .unwrap_or_else(|| panic!("set {name} to one explicit regular file path")),
            );
            let metadata = std::fs::symlink_metadata(&path).unwrap_or_else(|error| {
                panic!("cannot inspect {name} {}: {error}", path.display())
            });
            assert!(
                !metadata.file_type().is_symlink() && metadata.is_file(),
                "{name} {} must be a regular non-symlink file",
                path.display()
            );
            path
        };
        let executable = regular_env_path("SABLE_DECLARATION_INVENTORY_EXE");
        let candidate = regular_env_path("SABLE_DECLARATION_INVENTORY_CANDIDATE");
        let request = declaration_inventory_request(&candidate)
            .expect("the explicit candidate path has an exact inventory request");

        let mut child = Command::new(&executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap_or_else(|error| {
                panic!(
                    "cannot spawn declaration inventory {}: {error}",
                    executable.display()
                )
            });
        {
            let mut stdin = child
                .stdin
                .take()
                .expect("declaration inventory stdin pipe is available");
            stdin
                .write_all(&request)
                .expect("write the exact declaration inventory request");
        }
        let output = child
            .wait_with_output()
            .expect("wait for the declaration inventory process");
        let inventory = parse_declaration_inventory_output(
            output.status.success(),
            &output.stdout,
            &output.stderr,
        )
        .expect("cross-language output satisfies the exact canonical transport");
        assert!(inventory.observational);
        let nonanonymous = |name: &ObservedName| !matches!(name, ObservedName::Anonymous);
        let has_structural_name = inventory
            .imports
            .iter()
            .any(|import| nonanonymous(&import.module))
            || inventory.constants.iter().any(|constant| {
                constant.const_name.as_ref().is_some_and(&nonanonymous)
                    || constant.info_name.as_ref().is_some_and(&nonanonymous)
            })
            || inventory.extra_const_names.iter().any(&nonanonymous)
            || inventory
                .extension_families
                .iter()
                .any(|family| nonanonymous(&family.name));
        assert!(
            has_structural_name,
            "candidate inventory must expose at least one nonanonymous structural Lean name"
        );
    }

    #[test]
    #[ignore = "end-to-end canary; explicitly runs the pinned proof build, ingress auditor, Lean compiler, and declaration inventory"]
    fn declaration_compile_and_observe_cross_language_canary() {
        assert_eq!(
            std::env::var("SABLE_RUN_DECLARATION_COMPILE_OBSERVATION_CANARY").as_deref(),
            Ok("1"),
            "set SABLE_RUN_DECLARATION_COMPILE_OBSERVATION_CANARY=1 to authorize this ignored Lean canary"
        );
        let repo_root = PathBuf::from(
            std::env::var_os("SABLE_DECLARATION_COMPILE_OBSERVATION_REPO")
                .expect("set SABLE_DECLARATION_COMPILE_OBSERVATION_REPO to the explicit repo root"),
        );
        assert!(repo_root.is_absolute());
        let environment =
            ProofEnvironment::capture(&repo_root).expect("capture exact proof environment");
        let module_name = "SableGeneratedDeclarationObservationCanary";
        let emitted = draft_with_source("import Sable\n\n").finish(module_name);
        let subject = DeclarationAuditSubject::new(
            environment.id(),
            environment.policy(),
            DeclarationModuleSubject::from_emitted(module_name, &emitted),
            Vec::new(),
        );
        let temporary_entries = |root: &Path| -> std::collections::BTreeSet<String> {
            let modules = modules_dir(root);
            let Ok(entries) = std::fs::read_dir(modules) else {
                return std::collections::BTreeSet::new();
            };
            entries
                .filter_map(Result::ok)
                .filter_map(|entry| entry.file_name().into_string().ok())
                .filter(|name| {
                    name.contains(".declaration-source.") || name.contains(".declaration-output.")
                })
                .collect()
        };
        let before = temporary_entries(&repo_root);
        let observation =
            compile_and_observe_declaration_module(&repo_root, &environment, &emitted, &subject)
                .expect("strict ephemeral compilation and inventory observation pass");
        let after = temporary_entries(&repo_root);

        assert_eq!(before, after, "all owned temporary paths are cleaned");
        assert!(
            std::fs::symlink_metadata(&observation.ephemeral_source_path).is_err(),
            "the exact ephemeral source file is removed before return"
        );
        assert!(
            std::fs::symlink_metadata(&observation.ephemeral_source_root).is_err(),
            "the exact ephemeral source directory is removed before return"
        );
        assert!(
            std::fs::symlink_metadata(&observation.ephemeral_candidate_path).is_err(),
            "the exact ephemeral candidate file is removed before return"
        );
        assert!(
            std::fs::symlink_metadata(&observation.ephemeral_candidate_root).is_err(),
            "the exact ephemeral candidate directory is removed before return"
        );
        assert!(observation.observational);
        assert!(!observation.authoritative);
        assert_eq!(
            observation.source_sha256_before,
            crate::sha256::hex(emitted.lean_source.as_bytes())
        );
        assert_eq!(
            observation.source_sha256_before,
            observation.source_sha256_after_compile
        );
        assert_eq!(
            observation.source_sha256_before,
            observation.source_sha256_after_inventory
        );
        assert_eq!(
            observation.lean_stdout_sha256,
            crate::sha256::hex(&observation.lean_stdout)
        );
        assert!(
            observation
                .lean_messages
                .iter()
                .all(|message| message.severity != "error")
        );
        assert!(observation.declaration.observational);
        assert!(!observation.declaration.authoritative);
        assert_eq!(observation.declaration.expected_module_name, module_name);
        assert!(observation.declaration.inventory.observational);
        assert!(!observation.declaration.inventory.is_module);
        assert!(observation.inventory_preflight.observational);
        assert!(!observation.inventory_preflight.authoritative);
        assert_eq!(observation.inventory_preflight.explicit_matches.len(), 1);
        assert!(matches!(
            &observation.inventory_preflight.explicit_matches[0].role,
            DeclarationInventoryExplicitRole::TerminalSentinel { root_index: 0 }
        ));
    }

    #[test]
    fn declaration_inventory_transport_rejects_noncanonical_or_loose_evidence() {
        let exact = concat!(
            r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
            "\n"
        );
        parse_declaration_inventory_output(true, exact.as_bytes(), b"")
            .expect("the empty exact inventory passes");
        let without_newline = exact.strip_suffix('\n').expect("fixture has newline");
        let cases = vec![
            without_newline.as_bytes().to_vec(),
            format!("{without_newline}\r\n").into_bytes(),
            format!("{exact}{{}}\n").into_bytes(),
            concat!(
                r#"{"schema":"sable-declaration-inventory-result-v1","observational":true,"is_module":false,"imports":[],"extra_const_names":[],"extension_families":[],"constants":[]}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1","schema":"sable-declaration-inventory-result-v1"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":false,"schema":"sable-declaration-inventory-result-v1"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v0"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1","unknown":0}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[{"const_name":{"some":{"display":"not-structural"}},"info_name":null,"kind":null,"safety":null}],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[{"const_name":null,"info_name":null,"kind":null,"safety":null}],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
            concat!(
                r#"{"constants":[{"const_name":null,"info_name":{"some":{"str":[null,"x"]}},"kind":"forged","safety":"safe"}],"extension_families":[],"extra_const_names":[],"imports":[],"is_module":false,"observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
                "\n"
            )
            .as_bytes()
            .to_vec(),
        ];
        for output in cases {
            assert!(parse_declaration_inventory_output(true, &output, b"").is_err());
        }
        assert!(parse_declaration_inventory_output(false, exact.as_bytes(), b"").is_err());
        assert!(parse_declaration_inventory_output(true, exact.as_bytes(), b"warning\n").is_err());

        let rejected = concat!(
            r#"{"error_kind":"request","message":"bad request","observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
            "\n"
        );
        assert!(
            parse_declaration_inventory_output(true, rejected.as_bytes(), b"")
                .expect_err("an exact rejection remains a failure")
                .contains("request boundary")
        );
        let forged = concat!(
            r#"{"error_kind":"accepted","message":"forged","observational":true,"schema":"sable-declaration-inventory-result-v1"}"#,
            "\n"
        );
        assert!(parse_declaration_inventory_output(true, forged.as_bytes(), b"").is_err());
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
        let declaration_inventory = declaration_inventory_path(&built);
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
        std::fs::write(
            olean_root.join("SableDeclarationAudit.olean"),
            b"declaration inventory library olean",
        )
        .expect("write declaration inventory library olean");
        std::fs::write(olean_root.join("Sable/Fixture.olean"), b"fixture olean")
            .expect("write nested olean");
        std::fs::write(&auditor, b"native auditor").expect("write native auditor");
        std::fs::write(&declaration_inventory, b"native declaration inventory")
            .expect("write native declaration inventory");

        let files = BTreeMap::from([
            ("lean/Sable.lean".into(), b"import Sable.Fixture".to_vec()),
            ("lean/SableProofAudit.lean".into(), b"import Sable".to_vec()),
            (
                "lean/SableDeclarationAudit.lean".into(),
                b"import Lean".to_vec(),
            ),
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
                "SableDeclarationAudit.olean",
                "SableProofAudit.olean"
            ]
        );

        std::fs::remove_file(&declaration_inventory)
            .expect("remove observational declaration inventory executable");
        assert!(
            proof_build_output_digests(&built, &files)
                .expect_err("a missing declaration inventory executable fails closed")
                .contains("observational declaration inventory")
        );
        std::fs::write(&declaration_inventory, b"native declaration inventory")
            .expect("restore native declaration inventory");

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
        let rejection = b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":false,\"failure_kind\":\"fragment\",\"message\":\"escaped parser boundary\",\"index\":1}\n";
        let failure = parse_ingress_audit_output(&emitted, true, rejection, b"")
            .expect_err("fragment rejection fails closed");
        assert_eq!(failure.span, Span::new(7, 11));
        assert_eq!(failure.description, "second fragment");
        assert_eq!(failure.message, "escaped parser boundary");

        let out_of_range = b"{\"schema\":\"sable-proof-ingress-result-v2\",\"accepted\":false,\"failure_kind\":\"fragment\",\"message\":\"forged\",\"index\":2}\n";
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
            [
                "--quiet",
                "build",
                "Sable",
                "sable-proof-audit",
                "sable-declaration-audit",
            ]
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

        let declaration_inventory_path =
            Path::new("proof-environment/lean/.lake/build/bin/sable-declaration-audit");
        let declaration_inventory =
            serial_declaration_inventory_command(lean_dir, declaration_inventory_path);
        assert_serial_lake_command_base(&declaration_inventory, lean_dir);
        assert_eq!(
            declaration_inventory.get_args().collect::<Vec<_>>(),
            [OsStr::new("env"), declaration_inventory_path.as_os_str()]
        );
    }

    #[test]
    fn declaration_compilation_command_pins_ephemeral_root_output_source_and_dependencies() {
        let lean_dir = Path::new("proof-environment/lean");
        let modules = Path::new("/repo/.sable-out/modules");
        let source_root = modules.join(".Root_module.declaration-source.42.7");
        let source = source_root.join("Root_module.lean");
        let candidate = modules
            .join(".Root_module.declaration-output.42.8")
            .join("Root_module.olean");
        let command =
            generated_lean_command(lean_dir, modules, &source, Some((&source_root, &candidate)));
        assert_eq!(command.get_program(), OsStr::new("lake"));
        assert_eq!(command.get_current_dir(), Some(lean_dir));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            [
                OsStr::new("env"),
                OsStr::new("lean"),
                OsStr::new("--json"),
                OsStr::new("--root"),
                source_root.as_os_str(),
                OsStr::new("-o"),
                candidate.as_os_str(),
                source.as_os_str(),
            ]
        );
        let envs = command.get_envs().collect::<Vec<_>>();
        assert!(envs.contains(&(OsStr::new("LEAN_PATH"), Some(modules.as_os_str()))));
        for name in PROOF_TOOL_OVERRIDES {
            if name != "LEAN_PATH" {
                assert!(
                    envs.contains(&(OsStr::new(name), None)),
                    "declaration compilation removes ambient override {name}"
                );
            }
        }
        assert_eq!(
            source.file_name().and_then(|name| name.to_str()),
            Some("Root_module.lean"),
            "the explicit root yields the exact expected module name"
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
                (
                    "SableDeclarationAudit.olean".into(),
                    crate::sha256::hex(b"exact declaration inventory olean"),
                ),
            ]),
            proof_auditor_sha256: crate::sha256::hex(b"exact proof auditor"),
            declaration_inventory_sha256: crate::sha256::hex(b"exact declaration inventory"),
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
            local_olean_sha256: output_digests.local_olean_sha256.clone(),
            proof_auditor_sha256: output_digests.declaration_inventory_sha256.clone(),
            declaration_inventory_sha256: output_digests.proof_auditor_sha256.clone(),
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
                    .replace("sable-proof-ready-v3", "sable-proof-ready-v2")
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

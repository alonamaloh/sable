//! The two-language split (design §1): any line whose first non-whitespace
//! characters are `///` is a proof line; consecutive proof lines form a
//! proof block. Proof blocks attach positionally — a block whose last line
//! immediately precedes an item (no blank line) attaches to it.
//!
//! This pass produces (a) the program text with proof lines blanked out
//! (byte-for-byte, so all spans and line numbers coincide with the original
//! file) and (b) the list of proof blocks with their clauses.

use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseKind {
    Pre,
    Post,
    Invariant,
    Variant,
    Assert,
    Defer,
    Assume,
    GhostDef,
    Theorem,
    /// `/// spec name : sig` — a trait's spec-level function (ADR 0007).
    Spec,
    Discharge,
    /// Continuation or unrecognized — reported by the parser when reached.
    Other,
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub kind: ClauseKind,
    /// `#[label(name)]` — a short stable name for the obligation and
    /// its hypothesis, replacing the content slug in generated names
    /// (`fn.post.frame`, `h_inv_frame`). Stripped from `text`.
    pub label: Option<String>,
    /// Proof-language text after the keyword, verbatim except that a
    /// trailing `-- comment` is stripped (clauses get spliced inside
    /// parentheses in generated Lean, where a line comment would swallow
    /// the closing paren).
    pub text: String,
    /// Span of `text` within the original source.
    pub span: Span,
    /// Span of the whole `/// ...` line.
    pub line_span: Span,
}

#[derive(Debug, Clone)]
pub struct ProofBlock {
    pub clauses: Vec<Clause>,
    /// 1-based line numbers of the first and last `///` line.
    pub first_line: usize,
    pub last_line: usize,
    pub span: Span,
}

pub struct ScanResult {
    /// Original source with every proof line's content replaced by spaces.
    pub program_text: String,
    pub blocks: Vec<ProofBlock>,
}

pub fn scan(source: &str) -> ScanResult {
    let mut program = String::with_capacity(source.len());
    let mut blocks: Vec<ProofBlock> = Vec::new();
    let mut current: Option<ProofBlock> = None;

    let mut offset = 0;
    for (idx, line) in source.split_inclusive('\n').enumerate() {
        let line_no = idx + 1;
        let content = line.strip_suffix('\n').unwrap_or(line);
        let trimmed_start = content.len() - content.trim_start().len();
        let trimmed = content.trim_start();

        // `///` starts a proof line; `////` does not (matches doc-comment lore).
        if trimmed.starts_with("///") && !trimmed.starts_with("////") {
            let clause = parse_clause(content, trimmed_start, offset);
            match current.as_mut() {
                Some(block) if block.last_line + 1 == line_no => {
                    block.last_line = line_no;
                    block.span = block.span.join(clause.line_span);
                    block.clauses.push(clause);
                }
                _ => {
                    if let Some(done) = current.take() {
                        blocks.push(done);
                    }
                    current = Some(ProofBlock {
                        first_line: line_no,
                        last_line: line_no,
                        span: clause.line_span,
                        clauses: vec![clause],
                    });
                }
            }
            // Blank the proof line in the program text.
            for _ in 0..content.len() {
                program.push(' ');
            }
            if line.ends_with('\n') {
                program.push('\n');
            }
        } else {
            if let Some(done) = current.take() {
                blocks.push(done);
            }
            program.push_str(line);
        }
        offset += line.len();
    }
    if let Some(done) = current.take() {
        blocks.push(done);
    }

    // Merge continuation lines (no leading clause keyword) into the
    // preceding clause: multi-line `post match result with | ...` and
    // multi-line discharge scripts depend on this. A continuation line
    // with no preceding clause stays `Other`; the parser reports it.
    for block in &mut blocks {
        let mut merged: Vec<Clause> = Vec::new();
        for clause in block.clauses.drain(..) {
            match (clause.kind, merged.last_mut()) {
                (ClauseKind::Other, Some(prev)) => {
                    prev.text.push('\n');
                    prev.text.push_str(&clause.text);
                    prev.span = prev.span.join(clause.span);
                    prev.line_span = prev.line_span.join(clause.line_span);
                }
                _ => merged.push(clause),
            }
        }
        block.clauses = merged;
    }

    ScanResult {
        program_text: program,
        blocks,
    }
}

fn parse_clause(line: &str, indent: usize, line_offset: usize) -> Clause {
    let line_span = Span::new(line_offset, line_offset + line.len());
    let after_marker_idx = indent + 3; // past "///"
    let after_marker = &line[after_marker_idx..];
    let kw_start_rel = after_marker.len() - after_marker.trim_start().len();
    let rest = after_marker.trim_start();

    let (kind, kw_len) = keyword(rest);
    let text_rel = kw_start_rel + kw_len;
    // Continuation lines (no keyword) keep their leading indentation —
    // multi-line tactic scripts need relative indent for nested bullets.
    let mut text = if kind == ClauseKind::Other {
        after_marker
            .strip_prefix(' ')
            .unwrap_or(after_marker)
            .trim_end()
            .to_string()
    } else {
        after_marker[text_rel..].trim_start().to_string()
    };
    let text_lead_ws = if kind == ClauseKind::Other {
        after_marker.len() - after_marker.trim_start().len()
    } else {
        after_marker[text_rel..].len() - after_marker[text_rel..].trim_start().len()
    };

    // Strip a trailing Lean line comment (see field doc on `text`).
    if let Some(pos) = text.find("--") {
        text.truncate(pos);
    }
    let mut text = text.trim_end().to_string();

    // `#[label(name)]` on contract clauses: strip a well-formed label;
    // a malformed `#[...]` stays in `text` for the parser to reject.
    let mut label = None;
    let mut label_len = 0;
    if matches!(
        kind,
        ClauseKind::Pre
            | ClauseKind::Post
            | ClauseKind::Invariant
            | ClauseKind::Variant
            | ClauseKind::Assert
    ) {
        if let Some(rest) = text.strip_prefix("#[label(") {
            if let Some(close) = rest.find(")]") {
                let name = &rest[..close];
                if !name.is_empty()
                    && name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    label = Some(name.to_string());
                    let stripped = rest[close + 2..].trim_start();
                    label_len = text.len() - stripped.len();
                    text = stripped.to_string();
                }
            }
        }
    }

    let text_start = line_offset + after_marker_idx + text_rel + text_lead_ws + label_len;
    Clause {
        kind,
        label,
        span: Span::new(text_start, text_start + text.len()),
        text,
        line_span,
    }
}

fn keyword(rest: &str) -> (ClauseKind, usize) {
    let word: String = rest
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    let kind = match word.as_str() {
        "pre" => ClauseKind::Pre,
        "post" => ClauseKind::Post,
        "invariant" => ClauseKind::Invariant,
        "variant" => ClauseKind::Variant,
        "assert" => ClauseKind::Assert,
        "defer" => ClauseKind::Defer,
        "assume" => ClauseKind::Assume,
        "def" => ClauseKind::GhostDef,
        "spec" => ClauseKind::Spec,
        "theorem" => ClauseKind::Theorem,
        "discharge" => ClauseKind::Discharge,
        _ => return (ClauseKind::Other, 0),
    };
    (kind, word.len())
}

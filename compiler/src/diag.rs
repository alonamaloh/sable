//! Diagnostic rendering: every user-facing error carries a source span and,
//! for verification failures, the obligation name, goal, and context.
//! Errors about clause text must point at the .sable file, never at
//! generated Lean (see CLAUDE.md invariants).

use crate::span::{LineMap, Span};

#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Short machine-matchable name: obligation name for verification
    /// failures (`div_round_up.overflow.a_add_b`), or an error code for
    /// front-end errors (`parse.expected_token`, `type.mismatch`, ...).
    pub name: String,
    /// One-line human title.
    pub title: String,
    pub span: Span,
    /// Label printed under the caret.
    pub label: String,
    /// `= key: value` footnotes, in order.
    pub notes: Vec<(String, String)>,
}

impl Diagnostic {
    pub fn render(&self, path: &str, source: &str, lines: &LineMap) -> String {
        self.render_level("error", path, source, lines)
    }

    pub fn render_level(&self, level: &str, path: &str, source: &str, lines: &LineMap) -> String {
        let (line, col) = lines.line_col(self.span.start);
        let mut out = String::new();
        out.push_str(&format!("{level}: {}\n", self.title));
        out.push_str(&format!("  --> {path}:{line}:{col}\n"));

        let line_span = lines.line_span(line, source);
        let text = &source[line_span.start..line_span.end];
        let gutter = format!("{line}");
        let pad = " ".repeat(gutter.len());
        out.push_str(&format!("{pad} |\n"));
        out.push_str(&format!("{gutter} | {text}\n"));

        // Caret underline, clipped to this line.
        let start_in_line = self.span.start.saturating_sub(line_span.start);
        let end_in_line = (self.span.end.min(line_span.end)).saturating_sub(line_span.start);
        let width = (end_in_line.saturating_sub(start_in_line)).max(1);
        out.push_str(&format!(
            "{pad} | {}{} {}\n",
            " ".repeat(start_in_line),
            "^".repeat(width),
            self.label
        ));

        for (key, value) in &self.notes {
            if value.contains('\n') {
                out.push_str(&format!("{pad} = {key}:\n"));
                for l in value.lines() {
                    out.push_str(&format!("{pad}     {l}\n"));
                }
            } else {
                out.push_str(&format!("{pad} = {key}: {value}\n"));
            }
        }
        out
    }
}

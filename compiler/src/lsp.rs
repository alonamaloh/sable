//! The Sable language server (`sable lsp`, stdio transport).
//!
//! Scope — the design's reader-contract UX (design §1, Appendix A)
//! made visible:
//!   - diagnostics: fast front-end pass on every edit; the full Lean
//!     verification on open and save
//!   - hover on a function name: its contract (pre/post/variant), i.e.
//!     "no reader may be shown a function without its contract"
//!   - folding ranges for every proof block
//!   - semantic tokens: evidence lines are `comment`-typed (dimmed in
//!     every theme); interface lines (pre/post) are `property`-typed
//!     (highlighted) — "a reader may ignore proofs"

use crate::ast::Program;
use crate::diag::Diagnostic as SableDiag;
use crate::scan::ClauseKind;
use crate::span::LineMap;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{
    FoldingRangeRequest, HoverRequest, Request as _, SemanticTokensFullRequest,
};
use lsp_types::*;
use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;

/// Append a breadcrumb to /tmp/sable-lsp.log — the black box for
/// debugging editor-spawned instances whose stderr is hard to reach.
fn logf(msg: &str) {
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open("/tmp/sable-lsp.log")
    {
        let _ = writeln!(f, "[pid {}] {msg}", std::process::id());
    }
    eprintln!("sable lsp: {msg}");
}

pub fn run() -> Result<(), Box<dyn Error + Sync + Send>> {
    std::panic::set_hook(Box::new(|info| {
        logf(&format!("PANIC: {info}"));
    }));
    logf(&format!(
        "starting; exe={:?} cwd={:?} args={:?}",
        std::env::current_exe().ok(),
        std::env::current_dir().ok(),
        std::env::args().collect::<Vec<_>>(),
    ));
    let (connection, io_threads) = Connection::stdio();

    let capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::FULL),
                save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                    include_text: Some(false),
                })),
                ..Default::default()
            },
        )),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
        semantic_tokens_provider: Some(
            SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
                legend: SemanticTokensLegend {
                    token_types: vec![
                        SemanticTokenType::COMMENT,  // 0: evidence (dimmed)
                        SemanticTokenType::PROPERTY, // 1: interface (bright)
                    ],
                    token_modifiers: vec![],
                },
                full: Some(SemanticTokensFullOptions::Bool(true)),
                ..Default::default()
            }),
        ),
        ..Default::default()
    };

    if let Err(e) = connection.initialize(serde_json::to_value(capabilities)?) {
        logf(&format!("initialize failed: {e}"));
        return Err(e.into());
    }
    logf("initialized");
    if let Err(e) = main_loop(connection) {
        logf(&format!("main loop error: {e}"));
        return Err(e);
    }
    io_threads.join()?;
    logf("clean exit");
    Ok(())
}

struct State {
    docs: HashMap<Uri, String>,
}

fn main_loop(connection: Connection) -> Result<(), Box<dyn Error + Sync + Send>> {
    let mut state = State {
        docs: HashMap::new(),
    };
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                let resp = handle_request(&state, req);
                connection.sender.send(Message::Response(resp))?;
            }
            Message::Notification(note) => {
                handle_notification(&connection, &mut state, note)?;
            }
            Message::Response(_) => {}
        }
    }
    Ok(())
}

fn handle_notification(
    connection: &Connection,
    state: &mut State,
    note: Notification,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    match note.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: DidOpenTextDocumentParams = serde_json::from_value(note.params)?;
            let uri = params.text_document.uri;
            state
                .docs
                .insert(uri.clone(), params.text_document.text.clone());
            publish(connection, state, &uri, true)?;
        }
        DidChangeTextDocument::METHOD => {
            let params: DidChangeTextDocumentParams = serde_json::from_value(note.params)?;
            let uri = params.text_document.uri;
            if let Some(change) = params.content_changes.into_iter().next_back() {
                state.docs.insert(uri.clone(), change.text);
            }
            publish(connection, state, &uri, false)?;
        }
        DidSaveTextDocument::METHOD => {
            let params: DidSaveTextDocumentParams = serde_json::from_value(note.params)?;
            publish(connection, state, &params.text_document.uri, true)?;
        }
        _ => {}
    }
    Ok(())
}

/// Front-end diagnostics on every edit; the full (Lean) verification only
/// when `full` — i.e. on open and save, when the on-disk file is current.
fn publish(
    connection: &Connection,
    state: &State,
    uri: &Uri,
    full: bool,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let Some(text) = state.docs.get(uri) else {
        return Ok(());
    };
    let lines = LineMap::new(text);
    let mut diags = crate::front_diagnostics(text);
    let mut warnings = Vec::new();
    if full && diags.is_empty() {
        if let Some(path) = uri_path(uri) {
            let (mods, result) = crate::check_file_structured(&path, &crate::Options::default());
            // Only diagnostics in the root module belong to this uri
            // (imports carry combined-source spans past the root's end).
            let root_len = mods.modules.first().map(|m| m.len).unwrap_or(usize::MAX);
            match result {
                Err(more) => {
                    diags.extend(more.into_iter().filter(|d| d.span.start < root_len));
                }
                // Automation-budget warnings surface at WARNING severity.
                Ok(info) => {
                    warnings = info
                        .warnings
                        .into_iter()
                        .filter(|d| d.span.start < root_len)
                        .collect();
                }
            }
        }
    }
    let lsp_diags: Vec<lsp_types::Diagnostic> = diags
        .iter()
        .map(|d| to_lsp_diag(d, text, &lines))
        .chain(
            warnings
                .iter()
                .map(|d| to_lsp_diag_sev(d, text, &lines, DiagnosticSeverity::WARNING)),
        )
        .collect();
    connection.sender.send(Message::Notification(Notification::new(
        PublishDiagnostics::METHOD.to_string(),
        PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: lsp_diags,
            version: None,
        },
    )))?;
    Ok(())
}

fn handle_request(state: &State, req: Request) -> Response {
    let id = req.id.clone();
    match req.method.as_str() {
        HoverRequest::METHOD => match serde_json::from_value::<HoverParams>(req.params) {
            Ok(p) => hover(state, id, p),
            Err(e) => error_resp(id, e),
        },
        FoldingRangeRequest::METHOD => {
            match serde_json::from_value::<FoldingRangeParams>(req.params) {
                Ok(p) => folding(state, id, p),
                Err(e) => error_resp(id, e),
            }
        }
        SemanticTokensFullRequest::METHOD => {
            match serde_json::from_value::<SemanticTokensParams>(req.params) {
                Ok(p) => semantic_tokens(state, id, p),
                Err(e) => error_resp(id, e),
            }
        }
        _ => Response::new_ok(id, serde_json::Value::Null),
    }
}

fn error_resp(id: RequestId, e: impl std::fmt::Display) -> Response {
    Response::new_err(id, -32602, e.to_string())
}

// ------------------------------------------------------------------ hover

fn hover(state: &State, id: RequestId, params: HoverParams) -> Response {
    let uri = &params.text_document_position_params.text_document.uri;
    let pos = params.text_document_position_params.position;
    let Some(text) = state.docs.get(uri) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let lines = LineMap::new(text);
    let Some(offset) = position_to_offset(text, &lines, pos) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let Some(word) = word_at(text, offset) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let Some(program) = parse_program(text) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let Some(f) = program.fns.iter().find(|f| f.name == word) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };

    // The interface block, exactly as the design's rendering contract
    // requires: signature plus pre/post (and variant/partiality when
    // they exist) — never the body, never the evidence.
    let params_str = f
        .params
        .iter()
        .map(|p| format!("{} {}", p.ty.name(), p.name))
        .collect::<Vec<_>>()
        .join(", ");
    let ret = match f.ret {
        crate::ast::Ty::Unit => String::new(),
        other => format!(" -> {}", other.name()),
    };
    let mut md = format!("```sable\nfn {}({params_str}){ret}\n```\n", f.name);
    if f.pres.is_empty() && f.posts.is_empty() {
        md.push_str("\n*(no contract)*\n");
    } else {
        md.push_str("\n---\n");
        for pre in &f.pres {
            md.push_str(&format!("- **pre** `{}`\n", pre.text.replace('\n', " ")));
        }
        for post in &f.posts {
            md.push_str(&format!("- **post** `{}`\n", post.text.replace('\n', " ")));
        }
        if let Some(v) = &f.variant {
            md.push_str(&format!("- **variant** `{}`\n", v.text.replace('\n', " ")));
        }
    }
    let hover = Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: md,
        }),
        range: None,
    };
    Response::new_ok(id, serde_json::to_value(hover).unwrap())
}

// ---------------------------------------------------------------- folding

fn folding(state: &State, id: RequestId, params: FoldingRangeParams) -> Response {
    let Some(text) = state.docs.get(&params.text_document.uri) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let scanned = crate::scan::scan(text);
    let ranges: Vec<FoldingRange> = scanned
        .blocks
        .iter()
        .filter(|b| b.last_line > b.first_line)
        .map(|b| FoldingRange {
            start_line: (b.first_line - 1) as u32,
            end_line: (b.last_line - 1) as u32,
            kind: Some(FoldingRangeKind::Comment),
            ..Default::default()
        })
        .collect();
    Response::new_ok(id, serde_json::to_value(ranges).unwrap())
}

// -------------------------------------------------------- semantic tokens

fn semantic_tokens(state: &State, id: RequestId, params: SemanticTokensParams) -> Response {
    let Some(text) = state.docs.get(&params.text_document.uri) else {
        return Response::new_ok(id, serde_json::Value::Null);
    };
    let lines = LineMap::new(text);
    let scanned = crate::scan::scan(text);

    // (line0, utf16_len, token_type): 0 = evidence/dimmed, 1 = interface.
    let mut line_tokens: Vec<(u32, u32, u32)> = Vec::new();
    for block in &scanned.blocks {
        for clause in &block.clauses {
            let ttype = match clause.kind {
                ClauseKind::Pre | ClauseKind::Post => 1,
                _ => 0,
            };
            let first = lines.line_col(clause.line_span.start).0;
            let last = lines.line_col(clause.line_span.end).0;
            for line in first..=last {
                let span = lines.line_span(line, text);
                let len = text[span.start..span.end].encode_utf16().count() as u32;
                line_tokens.push(((line - 1) as u32, len, ttype));
            }
        }
    }
    line_tokens.sort();
    line_tokens.dedup_by_key(|t| t.0);

    let mut data = Vec::new();
    let mut prev_line = 0u32;
    for (line, len, ttype) in line_tokens {
        data.push(SemanticToken {
            delta_line: line - prev_line,
            delta_start: 0,
            length: len,
            token_type: ttype,
            token_modifiers_bitset: 0,
        });
        prev_line = line;
    }
    let tokens = SemanticTokens {
        result_id: None,
        data,
    };
    Response::new_ok(id, serde_json::to_value(tokens).unwrap())
}

// ------------------------------------------------------------------ utils

fn parse_program(text: &str) -> Option<Program> {
    let lines = LineMap::new(text);
    let scanned = crate::scan::scan(text);
    let tokens = crate::lexer::lex(&scanned.program_text).ok()?;
    crate::parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text).ok()
}

fn uri_path(uri: &Uri) -> Option<PathBuf> {
    let s = uri.as_str();
    let stripped = s.strip_prefix("file://")?;
    // Percent-decode the minimal cases (spaces).
    Some(PathBuf::from(stripped.replace("%20", " ")))
}

fn to_lsp_diag(d: &SableDiag, text: &str, lines: &LineMap) -> lsp_types::Diagnostic {
    to_lsp_diag_sev(d, text, lines, DiagnosticSeverity::ERROR)
}

fn to_lsp_diag_sev(
    d: &SableDiag,
    text: &str,
    lines: &LineMap,
    severity: DiagnosticSeverity,
) -> lsp_types::Diagnostic {
    let mut message = d.title.clone();
    if !d.label.is_empty() {
        message.push_str(&format!("\n{}", d.label));
    }
    for (key, value) in &d.notes {
        message.push_str(&format!("\n{key}: {value}"));
    }
    lsp_types::Diagnostic {
        range: Range {
            start: offset_to_position(text, lines, d.span.start),
            end: offset_to_position(text, lines, d.span.end),
        },
        severity: Some(severity),
        code: Some(NumberOrString::String(d.name.clone())),
        source: Some("sable".into()),
        message,
        ..Default::default()
    }
}

fn offset_to_position(text: &str, lines: &LineMap, offset: usize) -> Position {
    let offset = offset.min(text.len());
    let (line, _) = lines.line_col(offset);
    let line_span = lines.line_span(line, text);
    let col16 = text[line_span.start..offset.max(line_span.start)]
        .encode_utf16()
        .count() as u32;
    Position {
        line: (line - 1) as u32,
        character: col16,
    }
}

fn position_to_offset(text: &str, lines: &LineMap, pos: Position) -> Option<usize> {
    let line = (pos.line as usize) + 1;
    if line > lines.num_lines() {
        return None;
    }
    let span = lines.line_span(line, text);
    let line_text = &text[span.start..span.end];
    let mut units = 0u32;
    for (byte_idx, ch) in line_text.char_indices() {
        if units >= pos.character {
            return Some(span.start + byte_idx);
        }
        units += ch.len_utf16() as u32;
    }
    Some(span.end)
}

fn word_at(text: &str, offset: usize) -> Option<String> {
    let bytes = text.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    if offset >= bytes.len() {
        return None;
    }
    let mut start = offset;
    while start > 0 && is_word(bytes[start - 1]) {
        start -= 1;
    }
    let mut end = offset;
    while end < bytes.len() && is_word(bytes[end]) {
        end += 1;
    }
    if start == end {
        return None;
    }
    Some(text[start..end].to_string())
}

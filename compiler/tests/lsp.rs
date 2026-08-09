//! Drives `sable lsp` over stdio with a real LSP handshake: initialize,
//! didOpen a file with a type error, and assert the published diagnostics
//! carry the Sable diagnostic code and the right position.

use std::io::{BufRead, BufReader, Read, Write};

use std::process::{Command, Stdio};

fn frame(payload: &str) -> Vec<u8> {
    format!("Content-Length: {}\r\n\r\n{payload}", payload.len()).into_bytes()
}

fn read_message(reader: &mut impl BufRead) -> serde_json::Value {
    let mut content_length = 0usize;
    loop {
        let mut line = String::new();
        reader.read_line(&mut line).expect("header read");
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(rest) = line.strip_prefix("Content-Length:") {
            content_length = rest.trim().parse().expect("content length");
        }
    }
    let mut buf = vec![0u8; content_length];
    reader.read_exact(&mut buf).expect("body read");
    serde_json::from_slice(&buf).expect("json body")
}

#[test]
fn lsp_diagnostics_hover_and_tokens() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sable"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn sable lsp");
    let mut stdin = child.stdin.take().unwrap();
    let mut stdout = BufReader::new(child.stdout.take().unwrap());

    let send = |stdin: &mut std::process::ChildStdin, v: serde_json::Value| {
        stdin.write_all(&frame(&v.to_string())).unwrap();
        stdin.flush().unwrap();
    };

    send(
        &mut stdin,
        serde_json::json!({
            "jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": { "capabilities": {} }
        }),
    );
    let init = read_message(&mut stdout);
    assert!(
        init["result"]["capabilities"]["hoverProvider"].as_bool() == Some(true),
        "hover capability missing: {init}"
    );
    send(
        &mut stdin,
        serde_json::json!({ "jsonrpc": "2.0", "method": "initialized", "params": {} }),
    );

    // A file with a definite-initialization error plus a contracted
    // function to hover over. Lines are 0-based in LSP.
    let text = "\
/// pre  b > 0\n\
/// post result = a / b\n\
fn div(u32 a, u32 b) -> u32 {\n\
    return a / b;\n\
}\n\
\n\
/// post result >= 0\n\
fn broken(bool c) -> i32 {\n\
    i32 x;\n\
    if (c) { x = 1; }\n\
    return x;\n\
}\n";
    send(
        &mut stdin,
        serde_json::json!({
            "jsonrpc": "2.0", "method": "textDocument/didOpen",
            "params": { "textDocument": {
                "uri": "file:///nonexistent/probe.sable",
                "languageId": "sable", "version": 1, "text": text
            }}
        }),
    );
    let diag_note = read_message(&mut stdout);
    assert_eq!(diag_note["method"], "textDocument/publishDiagnostics");
    let diags = diag_note["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diags.len(), 1, "expected one diagnostic: {diag_note}");
    assert_eq!(diags[0]["code"], "type.uninitialized");
    assert_eq!(diags[0]["range"]["start"]["line"], 10); // `return x;`

    // Hover over `div` in its call... over the definition name (line 2).
    send(
        &mut stdin,
        serde_json::json!({
            "jsonrpc": "2.0", "id": 2, "method": "textDocument/hover",
            "params": {
                "textDocument": { "uri": "file:///nonexistent/probe.sable" },
                "position": { "line": 2, "character": 4 }
            }
        }),
    );
    let hover = read_message(&mut stdout);
    let value = hover["result"]["contents"]["value"].as_str().unwrap();
    assert!(value.contains("**pre** `b > 0`"), "hover was: {value}");
    assert!(value.contains("**post** `result = a / b`"), "hover: {value}");

    // Semantic tokens: 4 proof lines → 4 line tokens, all interface (=1).
    send(
        &mut stdin,
        serde_json::json!({
            "jsonrpc": "2.0", "id": 3, "method": "textDocument/semanticTokens/full",
            "params": { "textDocument": { "uri": "file:///nonexistent/probe.sable" } }
        }),
    );
    let toks = read_message(&mut stdout);
    let data = toks["result"]["data"].as_array().unwrap();
    assert_eq!(data.len() % 5, 0);
    assert_eq!(data.len() / 5, 3, "three contract lines: {toks}");

    send(
        &mut stdin,
        serde_json::json!({ "jsonrpc": "2.0", "id": 9, "method": "shutdown", "params": null }),
    );
    let _ = read_message(&mut stdout);
    send(
        &mut stdin,
        serde_json::json!({ "jsonrpc": "2.0", "method": "exit", "params": null }),
    );
    let status = child.wait().expect("wait");
    assert!(status.success());
}

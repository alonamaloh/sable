//! Warm-check daemon: keeps a Lean language server (`lake env lean --server`)
//! alive so repeated `sable check` runs skip the ~1.5–2s Lean cold start.
//!
//! Protocol (deliberately trivial — newline-delimited JSON over a unix socket
//! at `.sable-out/daemon.sock`):
//!   client → daemon: `{"file": "/abs/path/to/generated.lean"}\n`
//!   daemon → client: `{"ok": true, "messages": [{"severity", "line", "data"}…]}\n`
//!                or  `{"ok": false, "error": "…"}\n`
//! `messages` uses the same shape as `lean::LeanMessage` from the batch
//! `lake env lean --json` path (1-based lines), so the diagnostic mapping
//! downstream is identical.
//!
//! Per check the daemon drives Lean's own LSP server: `textDocument/didOpen`
//! the first time a path is checked, `textDocument/didChange` (full-text
//! replacement) on re-checks, `textDocument/waitForDiagnostics` (a Lean
//! extension that responds only once the file is fully elaborated) as the
//! quiescence signal, and collect `textDocument/publishDiagnostics`.
//! If `waitForDiagnostics` fails we fall back to watching
//! `$/lean/fileProgress` for an empty `processing` array.
//!
//! Documents stay open between checks on purpose: Lean's server runs one
//! worker process per open document, and that worker re-imports the prelude
//! only when the file *header* changes. Generated files always start with
//! `import Sable`, so a re-check of an open document skips import loading —
//! that is where the cold-start time goes. Each open document costs a
//! resident worker process, so we cap them with a small LRU.
//!
//! The client side (`try_check`) treats *any* problem — no socket, stale
//! socket, daemon error — as "no daemon": the caller falls back to the batch
//! path, so `sable check` never gets worse because a daemon misbehaved.
//!
//! Cancel-on-disconnect: while a check is in flight the daemon watches the
//! client socket; if the client dies (killed `sable check`), the daemon
//! `didClose`s the document, which makes Lean's server terminate that
//! file's worker — no orphaned `lean --worker` grinding on dead work. The
//! canceled document leaves the warm set (the next check of that file pays
//! one cold didOpen), a fair trade against minutes of wasted CPU.

use crate::lean::LeanMessage;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::mpsc::{Receiver, RecvTimeoutError, channel};
use std::time::{Duration, Instant};

pub fn socket_path(repo_root: &Path) -> PathBuf {
    repo_root.join(".sable-out").join("daemon.sock")
}

// ---------------------------------------------------------------------------
// Client side (used by `sable check`)
// ---------------------------------------------------------------------------

/// Ask a running daemon to check `lean_file`. Returns `None` when there is no
/// usable daemon (socket missing, connection refused, daemon reported an
/// error, malformed reply) — the caller then uses the batch path.
pub fn try_check(repo_root: &Path, lean_file: &Path) -> Option<Vec<LeanMessage>> {
    let mut stream = UnixStream::connect(socket_path(repo_root)).ok()?;
    // A generous ceiling so a wedged daemon cannot hang `sable check`
    // forever; real checks finish in well under this.
    let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(300)));
    let request = serde_json::json!({ "file": lean_file.to_string_lossy() });
    writeln!(stream, "{request}").ok()?;
    stream.flush().ok()?;

    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    reader.read_line(&mut line).ok()?;
    let reply: serde_json::Value = serde_json::from_str(line.trim()).ok()?;
    if reply["ok"].as_bool() != Some(true) {
        return None;
    }
    let messages = reply["messages"]
        .as_array()?
        .iter()
        .map(|m| LeanMessage {
            severity: m["severity"].as_str().unwrap_or("error").to_string(),
            line: m["line"].as_u64().unwrap_or(0) as usize,
            data: m["data"].as_str().unwrap_or("").to_string(),
        })
        .collect();
    Some(messages)
}

// ---------------------------------------------------------------------------
// Daemon side (`sable daemon`)
// ---------------------------------------------------------------------------

/// Run the daemon until killed. Builds the prelude once, spawns the Lean
/// server, then services check requests sequentially over the unix socket.
pub fn run(repo_root: &Path) -> Result<(), String> {
    let lean_dir = repo_root.join("lean");

    // Same staleness guard as the batch path, paid once at daemon startup.
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

    let mut server = LeanServer::spawn(&lean_dir)?;
    eprintln!("sable daemon: lean server ready ({})", lean_dir.display());

    let sock = socket_path(repo_root);
    if let Some(dir) = sock.parent() {
        std::fs::create_dir_all(dir)
            .map_err(|err| format!("cannot create {}: {err}", dir.display()))?;
    }
    // Remove a stale socket from a previous daemon; if another daemon is
    // live on it, that one loses — last starter wins, which is the least
    // surprising behavior for a manually-run daemon.
    let _ = std::fs::remove_file(&sock);
    let listener = UnixListener::bind(&sock)
        .map_err(|err| format!("cannot bind {}: {err}", sock.display()))?;
    eprintln!("sable daemon: listening on {}", sock.display());

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(err) => {
                eprintln!("sable daemon: accept failed: {err}");
                continue;
            }
        };
        let reply = handle_request(&mut server, &mut stream, &lean_dir);
        let _ = writeln!(stream, "{reply}");
        let _ = stream.flush();
    }
    Ok(())
}

fn handle_request(
    server: &mut LeanServer,
    stream: &mut UnixStream,
    lean_dir: &Path,
) -> serde_json::Value {
    let mut line = String::new();
    if BufReader::new(&mut *stream).read_line(&mut line).is_err() {
        return error_reply("cannot read request");
    }
    let Ok(request) = serde_json::from_str::<serde_json::Value>(line.trim()) else {
        return error_reply("malformed request (expected one JSON line)");
    };
    let Some(file) = request["file"].as_str() else {
        return error_reply("request missing \"file\"");
    };

    // If the Lean server died since the last request, respawn it once.
    if !server.alive() {
        eprintln!("sable daemon: lean server exited; respawning");
        match LeanServer::spawn(lean_dir) {
            Ok(fresh) => *server = fresh,
            Err(err) => return error_reply(&format!("lean server respawn failed: {err}")),
        }
    }

    match server.check(Path::new(file), stream) {
        Ok(messages) => {
            let messages: Vec<serde_json::Value> = messages
                .iter()
                .map(|m| {
                    serde_json::json!({
                        "severity": m.severity,
                        "line": m.line,
                        "data": m.data,
                    })
                })
                .collect();
            serde_json::json!({ "ok": true, "messages": messages })
        }
        Err(err) => {
            eprintln!("sable daemon: check failed: {err}");
            error_reply(&err)
        }
    }
}

fn error_reply(message: &str) -> serde_json::Value {
    serde_json::json!({ "ok": false, "error": message })
}

// ---------------------------------------------------------------------------
// A minimal LSP client for Lean's `lean --server`
// ---------------------------------------------------------------------------

/// Most-recently-used cap on simultaneously open documents (each one is a
/// resident Lean worker process holding the imported prelude).
const MAX_OPEN_DOCS: usize = 4;

struct LeanServer {
    child: Child,
    stdin: ChildStdin,
    /// Messages parsed off the server's stdout by a dedicated reader
    /// thread — the check loop must poll with a timeout so it can watch
    /// the client socket at the same time. The thread exits when the
    /// pipe closes (server death or daemon drop-kill).
    incoming: Receiver<Result<serde_json::Value, String>>,
    next_id: i64,
    /// Monotonic didOpen/didChange version, shared across documents.
    next_version: i64,
    /// Currently-open document uris, most recently used last.
    open_docs: Vec<String>,
    /// Last published diagnostics per open uri. Lean may elide re-publishing
    /// when a re-check reuses cached snapshots (identical content), so a
    /// round with no publishDiagnostics falls back to these.
    last_diags: std::collections::HashMap<String, serde_json::Value>,
}

impl LeanServer {
    fn spawn(lean_dir: &Path) -> Result<LeanServer, String> {
        let mut child = Command::new("lake")
            .arg("env")
            .arg("lean")
            .arg("--server")
            .current_dir(lean_dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|err| format!("failed to spawn `lake env lean --server`: {err}"))?;
        let stdin = child.stdin.take().expect("piped stdin");
        let mut stdout = BufReader::new(child.stdout.take().expect("piped stdout"));
        let (tx, incoming) = channel();
        std::thread::spawn(move || {
            loop {
                match read_framed(&mut stdout) {
                    Ok(msg) => {
                        if tx.send(Ok(msg)).is_err() {
                            break;
                        }
                    }
                    Err(err) => {
                        let _ = tx.send(Err(err));
                        break;
                    }
                }
            }
        });
        let mut server = LeanServer {
            child,
            stdin,
            incoming,
            next_id: 0,
            next_version: 0,
            open_docs: Vec::new(),
            last_diags: std::collections::HashMap::new(),
        };

        let root_uri = file_uri(lean_dir);
        server.request(
            "initialize",
            serde_json::json!({
                "processId": std::process::id(),
                "rootUri": root_uri,
                "capabilities": {},
            }),
        )?;
        server.notify("initialized", serde_json::json!({}))?;
        Ok(server)
    }

    fn alive(&mut self) -> bool {
        matches!(self.child.try_wait(), Ok(None))
    }

    /// Check one generated .lean file; returns messages in batch-path shape.
    /// Watches `client` while waiting: a disconnect cancels the check by
    /// closing the document (terminating its worker).
    fn check(
        &mut self,
        lean_file: &Path,
        client: &mut UnixStream,
    ) -> Result<Vec<LeanMessage>, String> {
        let text = std::fs::read_to_string(lean_file)
            .map_err(|err| format!("cannot read {}: {err}", lean_file.display()))?;
        let uri = file_uri(lean_file);
        self.next_version += 1;
        let version = self.next_version;

        if let Some(pos) = self.open_docs.iter().position(|u| *u == uri) {
            // Already open: full-text didChange. The header (`import Sable`)
            // is unchanged, so the worker keeps its loaded imports — this is
            // the warm path that makes the daemon worthwhile.
            self.open_docs.remove(pos);
            self.open_docs.push(uri.clone());
            self.notify(
                "textDocument/didChange",
                serde_json::json!({
                    "textDocument": { "uri": uri, "version": version },
                    "contentChanges": [ { "text": text } ],
                }),
            )?;
        } else {
            if self.open_docs.len() >= MAX_OPEN_DOCS {
                let evicted = self.open_docs.remove(0);
                self.last_diags.remove(&evicted);
                self.notify(
                    "textDocument/didClose",
                    serde_json::json!({ "textDocument": { "uri": evicted } }),
                )?;
            }
            self.open_docs.push(uri.clone());
            self.notify(
                "textDocument/didOpen",
                serde_json::json!({
                    "textDocument": {
                        "uri": uri,
                        "languageId": "lean",
                        "version": version,
                        "text": text,
                    }
                }),
            )?;
        }

        // Quiescence: Lean's own extension request answers once diagnostics
        // for this version are complete; final publishDiagnostics precedes
        // the response on the same ordered pipe. On failure, fall back to
        // watching $/lean/fileProgress for an empty processing array.
        let wait_id = self.send_request(
            "textDocument/waitForDiagnostics",
            serde_json::json!({ "uri": uri, "version": version }),
        )?;

        let mut diagnostics: Option<serde_json::Value> = None;
        let mut wait_failed = false;
        let mut progress_done = false;
        let mut canceled = false;
        // After a cancel didClose, keep draining briefly so the server's
        // in-flight replies for this uri are consumed rather than left to
        // confuse the next request.
        let mut cancel_deadline: Option<Instant> = None;
        let result = loop {
            if !canceled && wait_failed && progress_done {
                break Ok(());
            }
            if let Some(deadline) = cancel_deadline {
                if Instant::now() >= deadline {
                    break Err("canceled: client disconnected".into());
                }
            }
            let msg = match self.receive_timeout(Duration::from_millis(100)) {
                None => {
                    if !canceled && client_disconnected(client) {
                        canceled = true;
                        eprintln!(
                            "sable daemon: client disconnected — closing {} to stop its worker",
                            lean_file.display()
                        );
                        let _ = self.notify(
                            "textDocument/didClose",
                            serde_json::json!({ "textDocument": { "uri": uri } }),
                        );
                        cancel_deadline = Some(Instant::now() + Duration::from_secs(10));
                    }
                    continue;
                }
                Some(Ok(m)) => m,
                Some(Err(err)) => break Err(err),
            };
            if msg["method"] == "textDocument/publishDiagnostics"
                && msg["params"]["uri"] == serde_json::Value::String(uri.clone())
            {
                diagnostics = Some(msg["params"]["diagnostics"].clone());
                continue;
            }
            if msg["method"] == "$/lean/fileProgress"
                && msg["params"]["textDocument"]["uri"] == serde_json::Value::String(uri.clone())
            {
                progress_done = msg["params"]["processing"]
                    .as_array()
                    .is_some_and(Vec::is_empty);
                continue;
            }
            if msg["id"] == serde_json::Value::from(wait_id) && msg.get("method").is_none() {
                if canceled {
                    // The worker is gone (didClose); this is the pending
                    // waitForDiagnostics resolving, however it resolved.
                    break Err("canceled: client disconnected".into());
                }
                if msg.get("error").is_none() {
                    break Ok(());
                }
                // waitForDiagnostics unavailable/failed: fall back to
                // $/lean/fileProgress reporting the file done.
                wait_failed = true;
                continue;
            }
            // Server-to-client request we don't implement: decline politely
            // so the server does not wait on us.
            if msg.get("id").is_some() && msg.get("method").is_some() {
                self.send(&serde_json::json!({
                    "jsonrpc": "2.0",
                    "id": msg["id"],
                    "error": { "code": -32601, "message": "method not found" },
                }))?;
            }
        };

        if let Err(err) = result {
            // Leave the document out of the warm set; a fresh didOpen next
            // time is the safest way back to a known state. (On cancel the
            // didClose already happened.)
            self.open_docs.retain(|u| *u != uri);
            self.last_diags.remove(&uri);
            if !canceled {
                let _ = self.notify(
                    "textDocument/didClose",
                    serde_json::json!({ "textDocument": { "uri": uri } }),
                );
            }
            return Err(err);
        }
        match diagnostics {
            Some(ref d) => {
                self.last_diags.insert(uri.clone(), d.clone());
            }
            None => diagnostics = self.last_diags.get(&uri).cloned(),
        }

        let mut messages = Vec::new();
        if let Some(diags) = diagnostics.as_ref().and_then(|d| d.as_array()) {
            for d in diags {
                let severity = match d["severity"].as_u64() {
                    Some(1) | None => "error",
                    Some(2) => "warning",
                    Some(3) => "information",
                    _ => "hint",
                };
                messages.push(LeanMessage {
                    severity: severity.to_string(),
                    // LSP lines are 0-based; `lean --json` (and our source
                    // map) are 1-based.
                    line: d["range"]["start"]["line"].as_u64().unwrap_or(0) as usize + 1,
                    data: d["message"].as_str().unwrap_or("").to_string(),
                });
            }
        }
        Ok(messages)
    }

    // -- JSON-RPC plumbing --------------------------------------------------

    fn send(&mut self, msg: &serde_json::Value) -> Result<(), String> {
        let body = msg.to_string();
        write!(self.stdin, "Content-Length: {}\r\n\r\n{}", body.len(), body)
            .and_then(|()| self.stdin.flush())
            .map_err(|err| format!("write to lean server failed: {err}"))
    }

    fn send_request(&mut self, method: &str, params: serde_json::Value) -> Result<i64, String> {
        self.next_id += 1;
        let id = self.next_id;
        self.send(&serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params,
        }))?;
        Ok(id)
    }

    /// Send a request and block until its response, answering unrelated
    /// server-to-client requests and discarding notifications meanwhile.
    fn request(
        &mut self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<serde_json::Value, String> {
        let id = self.send_request(method, params)?;
        loop {
            let msg = self.receive()?;
            if msg["id"] == serde_json::Value::from(id) && msg.get("method").is_none() {
                if let Some(err) = msg.get("error") {
                    return Err(format!("lean server error for {method}: {err}"));
                }
                return Ok(msg["result"].clone());
            }
            if msg.get("id").is_some() && msg.get("method").is_some() {
                self.send(&serde_json::json!({
                    "jsonrpc": "2.0",
                    "id": msg["id"],
                    "error": { "code": -32601, "message": "method not found" },
                }))?;
            }
        }
    }

    fn notify(&mut self, method: &str, params: serde_json::Value) -> Result<(), String> {
        self.send(&serde_json::json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
        }))
    }

    /// Next server message, blocking (startup handshake path).
    fn receive(&mut self) -> Result<serde_json::Value, String> {
        match self.incoming.recv() {
            Ok(msg) => msg,
            Err(_) => Err("lean server reader thread exited".into()),
        }
    }

    /// Next server message, or None on timeout (the check loop's poll —
    /// timeouts are when the client socket gets watched).
    fn receive_timeout(&mut self, timeout: Duration) -> Option<Result<serde_json::Value, String>> {
        match self.incoming.recv_timeout(timeout) {
            Ok(msg) => Some(msg),
            Err(RecvTimeoutError::Timeout) => None,
            Err(RecvTimeoutError::Disconnected) => {
                Some(Err("lean server reader thread exited".into()))
            }
        }
    }
}

/// Read one Content-Length-framed JSON-RPC message (reader thread).
fn read_framed(stdout: &mut BufReader<ChildStdout>) -> Result<serde_json::Value, String> {
    let mut content_length: Option<usize> = None;
    loop {
        let mut line = String::new();
        let n = stdout
            .read_line(&mut line)
            .map_err(|err| format!("read from lean server failed: {err}"))?;
        if n == 0 {
            return Err("lean server closed its stdout".into());
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(value) = line
            .strip_prefix("Content-Length:")
            .or_else(|| line.strip_prefix("content-length:"))
        {
            content_length = value.trim().parse().ok();
        }
    }
    let len = content_length.ok_or("lean server message missing Content-Length")?;
    let mut body = vec![0u8; len];
    stdout
        .read_exact(&mut body)
        .map_err(|err| format!("read from lean server failed: {err}"))?;
    serde_json::from_slice(&body).map_err(|err| format!("lean server sent invalid JSON: {err}"))
}

/// Has the check client gone away? A read on the request socket after the
/// request line: EOF means disconnected; the client never sends more, so a
/// zero-ish timeout probe consumes nothing meaningful.
fn client_disconnected(stream: &mut UnixStream) -> bool {
    let _ = stream.set_read_timeout(Some(Duration::from_millis(1)));
    let mut buf = [0u8; 1];
    match stream.read(&mut buf) {
        Ok(0) => true,
        Ok(_) => false,
        Err(err) => !matches!(
            err.kind(),
            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
        ),
    }
}

impl Drop for LeanServer {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn file_uri(path: &Path) -> String {
    // Paths here are repo paths: absolute, no characters needing escapes
    // beyond what Lean itself tolerates. Percent-encode the few that would
    // break URI parsing.
    let mut out = String::from("file://");
    for b in path.to_string_lossy().bytes() {
        match b {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => out.push(b as char),
            b'/' | b'-' | b'.' | b'_' | b'~' => out.push(b as char),
            _ => out.push_str(&format!("%{b:02X}")),
        }
    }
    out
}

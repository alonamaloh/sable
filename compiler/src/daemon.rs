//! Warm-check daemon: keeps a Lean language server (`lake env lean --server`)
//! alive so repeated `sable check` runs skip the ~1.5–2s Lean cold start.
//!
//! Protocol (deliberately trivial — newline-delimited JSON over a unix socket
//! at `.sable-out/daemon.sock`):
//!   client → daemon: `{"file": "/abs/path/to/generated.lean",
//!                       "fingerprint": "fnv64:...", "text": "..."}\n`
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
//! Documents stay open only within one exact immutable proof build. A request
//! for another captured environment replaces the whole server; a generated
//! import-header edit triggers didClose/didOpen. We never didChange a document
//! whose worker may hold stale imports. Each open document costs a resident
//! worker process, so we cap them with an LRU.
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

/// Check a generated document against the exact proof environment captured
/// while it was prepared. The caller must not substitute a fresh fingerprint:
/// doing so could pair old generated text with newly edited profile/prelude
/// semantics. Returns `None` when no usable daemon answers, so the caller can
/// use the batch path with the same expected fingerprint.
pub fn try_check(
    repo_root: &Path,
    lean_file: &Path,
    proof_environment: &crate::lean::ProofEnvironment,
    expected_source: &str,
) -> Option<Vec<LeanMessage>> {
    // Ensure the daemon can recover these exact bytes even if the live
    // checkout changes before it reads the request.
    proof_environment.materialize_source(repo_root).ok()?;
    let mut stream = UnixStream::connect(socket_path(repo_root)).ok()?;
    // A generous ceiling so a wedged daemon cannot hang `sable check`
    // forever; real checks finish in well under this.
    let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(300)));
    let request = serde_json::json!({
        "file": lean_file.to_string_lossy(),
        "fingerprint": proof_environment.id(),
        "text": expected_source,
    });
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

/// Run the daemon until killed. Proof builds are request-selected immutable
/// snapshots, so startup never guesses which mutable checkout state to build.
pub fn run(repo_root: &Path) -> Result<(), String> {
    let mut server: Option<LeanServer> = None;

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
        let reply = handle_request(&mut server, &mut stream, repo_root);
        let _ = writeln!(stream, "{reply}");
        let _ = stream.flush();
    }
    Ok(())
}

fn handle_request(
    server: &mut Option<LeanServer>,
    stream: &mut UnixStream,
    repo_root: &Path,
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
    let Some(request_fingerprint) = request["fingerprint"].as_str() else {
        return error_reply("request missing \"fingerprint\"");
    };
    let Some(expected_source) = request["text"].as_str() else {
        return error_reply("request missing \"text\"");
    };

    let proof_environment =
        match crate::lean::ProofEnvironment::load_published(repo_root, request_fingerprint) {
            Ok(environment) => environment,
            Err(error) => return error_reply(&error),
        };
    let built = match proof_environment.ensure_built(repo_root) {
        Ok(built) => built,
        Err(error) => return error_reply(&error),
    };
    let replace = server.as_ref().is_none_or(|server| {
        server.environment_fingerprint != proof_environment.id() || server.built_root != built
    });
    if replace {
        eprintln!(
            "sable daemon: selecting proof environment {}",
            proof_environment.id()
        );
        match LeanServer::spawn(repo_root, &proof_environment, &built) {
            Ok(fresh) => *server = Some(fresh),
            Err(error) => return error_reply(&format!("lean server spawn failed: {error}")),
        }
    }
    if server.as_mut().is_none_or(|server| !server.alive()) {
        eprintln!("sable daemon: lean server exited; respawning");
        match LeanServer::spawn(repo_root, &proof_environment, &built) {
            Ok(fresh) => *server = Some(fresh),
            Err(error) => return error_reply(&format!("lean server respawn failed: {error}")),
        }
    }

    match server.as_mut().expect("server was spawned above").check(
        Path::new(file),
        expected_source,
        stream,
    ) {
        Ok(messages) => {
            if let Err(error) = proof_environment.validate_built(&built) {
                return error_reply(&error);
            }
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
            // A failed notify/request can leave our open-document bookkeeping
            // out of sync with Lean. Replace the whole server before another
            // client can use it; the next request will still perform the
            // normal environment-fingerprint comparison first.
            if let Some(mut failed) = server.take() {
                failed.stop();
            }
            match LeanServer::spawn(repo_root, &proof_environment, &built) {
                Ok(fresh) => *server = Some(fresh),
                Err(respawn_error) => {
                    eprintln!(
                        "sable daemon: cleanup respawn after failed check also failed: {respawn_error}"
                    );
                }
            }
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

struct OpenDocument {
    uri: String,
    /// Exact leading `import ...` lines. Lean workers retain imported oleans,
    /// so changing this requires didClose/didOpen, never didChange.
    import_header: String,
    /// Exact last text, so cached diagnostics are reused only for an
    /// identical document, never merely for one with the same imports.
    text: String,
}

fn import_header(text: &str) -> String {
    // Generated files put their complete import list first. Preserve exact
    // lines and their order: changing even one dependency identity is enough
    // to require a fresh worker.
    text.lines()
        .take_while(|line| line.trim_start().starts_with("import "))
        .collect::<Vec<_>>()
        .join("\n")
}

struct LeanServer {
    /// Snapshot this process was spawned against. Any change replaces the
    /// entire server, clearing workers, open documents, and cached oleans.
    environment_fingerprint: String,
    /// Final stable repo-shaped build path whose oleans this process imports.
    built_root: PathBuf,
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
    /// Currently-open documents, most recently used last.
    open_docs: Vec<OpenDocument>,
    /// Last published diagnostics per open uri. Lean may elide re-publishing
    /// when a re-check reuses cached snapshots (identical content), so a
    /// round with no publishDiagnostics falls back to these.
    last_diags: std::collections::HashMap<String, serde_json::Value>,
}

impl LeanServer {
    fn spawn(
        repo_root: &Path,
        proof_environment: &crate::lean::ProofEnvironment,
        built_root: &Path,
    ) -> Result<LeanServer, String> {
        // Direct `lean` with the explicit search path (workspace +
        // generated-artifact dir): generated files import per-module
        // artifacts (ADR 0013 slice 2), and their content-addressed
        // names change with content, so a header re-import always sees
        // the current artifact.
        proof_environment.validate_built(built_root)?;
        let lean_dir = built_root.join("lean");
        let mut child = Command::new("lean")
            .arg("--server")
            .env(
                "LEAN_PATH",
                crate::lean::lean_search_path(repo_root, proof_environment)?,
            )
            .current_dir(&lean_dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|err| format!("failed to spawn `lean --server`: {err}"))?;
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
            environment_fingerprint: proof_environment.id().to_string(),
            built_root: built_root.to_path_buf(),
            child,
            stdin,
            incoming,
            next_id: 0,
            next_version: 0,
            open_docs: Vec::new(),
            last_diags: std::collections::HashMap::new(),
        };

        let root_uri = file_uri(&lean_dir);
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

    fn stop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }

    /// Check one generated .lean file; returns messages in batch-path shape.
    /// Watches `client` while waiting: a disconnect cancels the check by
    /// closing the document (terminating its worker).
    fn check(
        &mut self,
        lean_file: &Path,
        expected_source: &str,
        client: &mut UnixStream,
    ) -> Result<Vec<LeanMessage>, String> {
        // The exact prepared text travels with the request. The file path is
        // only the stable LSP identity; re-reading it here would reintroduce a
        // race with another checker materializing a different root version.
        let text = expected_source.to_string();
        let uri = file_uri(lean_file);
        let import_header = import_header(&text);
        self.next_version += 1;
        let version = self.next_version;

        if let Some(pos) = self.open_docs.iter().position(|doc| doc.uri == uri) {
            let previous = &self.open_docs[pos];
            if previous.import_header != import_header {
                // A worker does not necessarily reload imported oleans on a
                // full-text change. Close it before opening the replacement,
                // so the new import graph is elaborated from a clean state.
                self.notify(
                    "textDocument/didClose",
                    serde_json::json!({ "textDocument": { "uri": uri } }),
                )?;
                self.open_docs.remove(pos);
                self.last_diags.remove(&uri);
                self.open_document(uri.clone(), import_header, version, text)?;
            } else {
                // Import environment is unchanged: full-text didChange is the
                // safe warm path.
                let identical_text = previous.text == text;
                self.notify(
                    "textDocument/didChange",
                    serde_json::json!({
                        "textDocument": { "uri": uri, "version": version },
                        "contentChanges": [ { "text": text } ],
                    }),
                )?;
                self.open_docs.remove(pos);
                if !identical_text {
                    self.last_diags.remove(&uri);
                }
                self.open_docs.push(OpenDocument {
                    uri: uri.clone(),
                    import_header,
                    text,
                });
            }
        } else {
            if self.open_docs.len() >= MAX_OPEN_DOCS {
                let evicted_uri = self.open_docs[0].uri.clone();
                self.notify(
                    "textDocument/didClose",
                    serde_json::json!({ "textDocument": { "uri": evicted_uri } }),
                )?;
                self.open_docs.remove(0);
                self.last_diags.remove(&evicted_uri);
            }
            self.open_document(uri.clone(), import_header, version, text)?;
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
            self.open_docs.retain(|doc| doc.uri != uri);
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

    fn open_document(
        &mut self,
        uri: String,
        import_header: String,
        version: i64,
        text: String,
    ) -> Result<(), String> {
        self.notify(
            "textDocument/didOpen",
            serde_json::json!({
                "textDocument": {
                    "uri": uri.clone(),
                    "languageId": "lean",
                    "version": version,
                    "text": text.clone(),
                }
            }),
        )?;
        self.open_docs.push(OpenDocument {
            uri,
            import_header,
            text,
        });
        Ok(())
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
        self.stop();
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

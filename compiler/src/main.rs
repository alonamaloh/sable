use sable::{Options, Outcome, check_file};
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "\
Usage:
  sable check <file.sable>           verify a Sable source file
  sable check --emit-lean <file>     print the generated Lean instead of checking
  sable test  <file.sable>           run test_* functions with dynamic contract checks
  sable ... -M <dir>                 add a directory to the `use` module search path
  sable lsp                          run the language server on stdio
  sable daemon                       keep a warm Lean server for fast checks
                                     (socket: .sable-out/daemon.sock)
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut opts = Options::default();
    let mut command = None;
    let mut file = None;

    let mut expect_module_path = false;
    for arg in &args {
        if expect_module_path {
            opts.module_paths.push(PathBuf::from(arg));
            expect_module_path = false;
            continue;
        }
        match arg.as_str() {
            "check" if command.is_none() => command = Some("check"),
            "test" if command.is_none() => command = Some("test"),
            "lsp" if command.is_none() => command = Some("lsp"),
            "daemon" if command.is_none() => command = Some("daemon"),
            // LSP clients conventionally append --stdio (vscode-languageclient
            // does, among others); stdio is our only transport, so accept it.
            "--stdio" if command == Some("lsp") => {}
            "--emit-lean" => opts.emit_lean_only = true,
            "-M" | "--module-path" => expect_module_path = true,
            "-h" | "--help" => {
                print!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            other if !other.starts_with('-') && command.is_some() && file.is_none() => {
                file = Some(PathBuf::from(other));
            }
            other => {
                eprintln!("error: unexpected argument `{other}`\n{USAGE}");
                return ExitCode::from(2);
            }
        }
    }

    if command == Some("daemon") {
        let cwd = match std::env::current_dir() {
            Ok(d) => d,
            Err(e) => {
                eprintln!("daemon error: cannot determine current directory: {e}");
                return ExitCode::FAILURE;
            }
        };
        let Some(repo_root) = sable::lean::find_repo_root(&cwd) else {
            eprintln!(
                "daemon error: cannot locate the Sable repo (no ancestor of {} \
                 contains lean/lean-toolchain)",
                cwd.display()
            );
            return ExitCode::FAILURE;
        };
        return match sable::daemon::run(&repo_root) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("daemon error: {e}");
                ExitCode::FAILURE
            }
        };
    }
    if command == Some("lsp") {
        return match sable::lsp::run() {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("lsp error: {e}");
                ExitCode::FAILURE
            }
        };
    }
    let (Some(command), Some(file)) = (command, file) else {
        eprint!("{USAGE}");
        return ExitCode::from(2);
    };

    if command == "test" {
        return match sable::test_file(&file, &opts) {
            Err(failures) => {
                for f in &failures {
                    eprintln!("{}", f.rendered);
                }
                ExitCode::FAILURE
            }
            Ok(reports) => {
                if reports.is_empty() {
                    println!("no test_* functions in {}", file.display());
                    return ExitCode::SUCCESS;
                }
                let mut failed = 0;
                for r in &reports {
                    match &r.outcome {
                        Ok(()) => println!("test {} ... ok", r.name),
                        Err(msg) => {
                            failed += 1;
                            println!("test {} ... FAILED", r.name);
                            println!("    {msg}");
                        }
                    }
                    for (clause, why) in &r.skipped {
                        println!("    skipped (unmonitorable): {clause} — {why}");
                    }
                }
                println!(
                    "test result: {} passed, {failed} failed",
                    reports.len() - failed
                );
                if failed == 0 {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::FAILURE
                }
            }
        };
    }

    match check_file(&file, &opts) {
        Outcome::Verified {
            functions,
            obligations,
            unsafe_regions,
            externs,
            deferred,
            assumed,
            warnings,
        } => {
            if !opts.emit_lean_only {
                for w in &warnings {
                    eprintln!("{w}");
                }
                let proved = obligations - deferred.len() - assumed.len();
                println!(
                    "verified: {} — {obligations} obligation(s) across {functions} function(s): \
                     {proved} proved, {} deferred, {} assumed",
                    file.display(),
                    deferred.len(),
                    assumed.len(),
                );
                for d in &deferred {
                    println!("  deferred (sound runtime trap): {d}");
                }
                for (a, reason) in &assumed {
                    println!("  assumed (UNSOUND, audited):    {a} — {reason}");
                }
                // The audit surface, when there is one: a reader needs
                // to know how many places rest on a proof rather than on
                // the type system (ADR 0026).
                if unsafe_regions > 0 {
                    println!("  unsafe regions: {unsafe_regions}");
                }
                // An audited extern contract is an axiom nobody proved.
                // Saying "fully verified" while trusting one would be a
                // lie, so the status names the boundary and lists it
                // (ADR 0027).
                if !externs.is_empty() {
                    println!("  extern assumptions: {}", externs.len());
                    for (id, reason, name) in &externs {
                        println!("    - {id} ({name}): {reason}");
                    }
                }
                if !deferred.is_empty() || !assumed.is_empty() {
                    println!(
                        "status: verified with escapes (defers: {}, assumes: {})",
                        deferred.len(),
                        assumed.len()
                    );
                } else if !externs.is_empty() {
                    println!("status: verified relative to audited boundary");
                } else {
                    println!("status: fully verified");
                }
            }
            ExitCode::SUCCESS
        }
        Outcome::Failed(failures) => {
            for f in &failures {
                eprintln!("{}", f.rendered);
            }
            eprintln!(
                "verification failed: {} error(s) in {}",
                failures.len(),
                file.display()
            );
            ExitCode::FAILURE
        }
    }
}

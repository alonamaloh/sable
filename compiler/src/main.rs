use sable::{check_file, Options, Outcome};
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "\
Usage:
  sable check <file.sable>           verify a Sable source file
  sable check --emit-lean <file>     print the generated Lean instead of checking
  sable test  <file.sable>           run test_* functions with dynamic contract checks
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut opts = Options::default();
    let mut command = None;
    let mut file = None;

    for arg in &args {
        match arg.as_str() {
            "check" if command.is_none() => command = Some("check"),
            "test" if command.is_none() => command = Some("test"),
            "--emit-lean" => opts.emit_lean_only = true,
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

    let (Some(command), Some(file)) = (command, file) else {
        eprint!("{USAGE}");
        return ExitCode::from(2);
    };

    if command == "test" {
        return match sable::test_file(&file) {
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
            deferred,
            assumed,
        } => {
            if !opts.emit_lean_only {
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
                if deferred.is_empty() && assumed.is_empty() {
                    println!("status: fully verified");
                } else {
                    println!(
                        "status: verified with escapes (defers: {}, assumes: {})",
                        deferred.len(),
                        assumed.len()
                    );
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

use sable::{check_file, Options, Outcome};
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "\
Usage:
  sable check <file.sable>           verify a Sable source file
  sable check --emit-lean <file>     print the generated Lean instead of checking
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut opts = Options::default();
    let mut command = None;
    let mut file = None;

    for arg in &args {
        match arg.as_str() {
            "check" if command.is_none() => command = Some("check"),
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

    let (Some("check"), Some(file)) = (command, file) else {
        eprint!("{USAGE}");
        return ExitCode::from(2);
    };

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

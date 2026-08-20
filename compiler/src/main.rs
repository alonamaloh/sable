use sable::{Options, Outcome, VerifiedInfo, check_file};
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "\
Usage:
  sable check <file.sable>           verify a Sable source file
  sable check --emit-lean <file>     print the generated Lean instead of checking
  sable build --emit-llvm <file>     verify, then emit textual LLVM IR
             [--entry <name>]        also emit a C-compatible main for <name>
             [-o <file>|-]           write atomically to <file> (default: stdout)
  sable test  <file.sable>           run test_* functions with dynamic contract checks
  sable explain-type '<type>'        show parser positions and stage-gate coverage
  sable ... -M <dir>                 add a directory to the `use` module search path
  sable lsp                          run the language server on stdio
  sable daemon                       keep a warm Lean server for fast checks
                                     (socket: .sable-out/daemon.sock)
  sable doctor                       check the local Sable toolchain and checkout
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut opts = Options::default();
    let mut command = None;
    let mut file = None;
    let mut emit_llvm = false;
    let mut entry = None;
    let mut output = None;

    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "check" if command.is_none() => command = Some("check"),
            "build" if command.is_none() => command = Some("build"),
            "test" if command.is_none() => command = Some("test"),
            "explain-type" if command.is_none() => command = Some("explain-type"),
            "lsp" if command.is_none() => command = Some("lsp"),
            "daemon" if command.is_none() => command = Some("daemon"),
            "doctor" if command.is_none() => command = Some("doctor"),
            // LSP clients conventionally append --stdio (vscode-languageclient
            // does, among others); stdio is our only transport, so accept it.
            "--stdio" if command == Some("lsp") => {}
            "--emit-lean" => opts.emit_lean_only = true,
            "--emit-llvm" => emit_llvm = true,
            "--entry" => {
                if entry.is_some() {
                    eprintln!("error: `--entry` may only be supplied once\n{USAGE}");
                    return ExitCode::from(2);
                }
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: `--entry` requires a function name\n{USAGE}");
                    return ExitCode::from(2);
                };
                entry = Some(value.clone());
            }
            "-o" | "--output" => {
                if output.is_some() {
                    eprintln!("error: `-o` may only be supplied once\n{USAGE}");
                    return ExitCode::from(2);
                }
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: `-o` requires a path or `-`\n{USAGE}");
                    return ExitCode::from(2);
                };
                output = Some(PathBuf::from(value));
            }
            "-M" | "--module-path" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: `-M` requires a directory\n{USAGE}");
                    return ExitCode::from(2);
                };
                opts.module_paths.push(PathBuf::from(value));
            }
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
        i += 1;
    }

    if opts.emit_lean_only && command != Some("check") {
        eprintln!("error: `--emit-lean` is only valid with `sable check`\n{USAGE}");
        return ExitCode::from(2);
    }
    if emit_llvm && command != Some("build") {
        eprintln!("error: `--emit-llvm` is only valid with `sable build`\n{USAGE}");
        return ExitCode::from(2);
    }
    if (entry.is_some() || output.is_some()) && command != Some("build") {
        eprintln!("error: `--entry` and `-o` are only valid with `sable build`\n{USAGE}");
        return ExitCode::from(2);
    }
    if command == Some("build") && !emit_llvm {
        eprintln!("error: `sable build` currently requires `--emit-llvm`\n{USAGE}");
        return ExitCode::from(2);
    }

    if command == Some("explain-type") {
        if !opts.module_paths.is_empty() {
            eprintln!(
                "error: `-M` is not valid with `sable explain-type`; the command explains \
                 closed built-in and resource type spellings\n{USAGE}"
            );
            return ExitCode::from(2);
        }
        let Some(spelling) = file.as_ref().and_then(|argument| argument.to_str()) else {
            eprintln!("error: `sable explain-type` requires one type spelling\n{USAGE}");
            return ExitCode::from(2);
        };
        return match sable::explain_type(spelling) {
            Ok(report) => {
                print!("{report}");
                ExitCode::SUCCESS
            }
            Err(diagnostic) => {
                let lines = sable::span::LineMap::new(spelling);
                eprint!("{}", diagnostic.render("<type>", spelling, &lines));
                eprintln!("  = diagnostic: {}", diagnostic.name);
                ExitCode::from(2)
            }
        };
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
    if command == Some("doctor") {
        if !opts.module_paths.is_empty() {
            eprintln!("error: `-M` is not valid with `sable doctor`\n{USAGE}");
            return ExitCode::from(2);
        }
        if file.is_some() {
            eprintln!("error: `sable doctor` takes no file\n{USAGE}");
            return ExitCode::from(2);
        }
        let cwd = match std::env::current_dir() {
            Ok(cwd) => cwd,
            Err(error) => {
                eprintln!("doctor error: cannot determine current directory: {error}");
                return ExitCode::FAILURE;
            }
        };
        let report = sable::doctor::inspect(&cwd);
        println!("Sable doctor");
        for check in &report.checks {
            let status = match check.status {
                sable::doctor::CheckStatus::Ok => "ok",
                sable::doctor::CheckStatus::Warning => "warning",
                sable::doctor::CheckStatus::Error => "error",
            };
            println!("  {status:7} {:14} {}", check.name, check.detail);
        }
        if !report.ready() {
            println!("not ready: fix the required checks above");
            return ExitCode::FAILURE;
        }
        if report.native_ready() {
            println!("ready: verification and native execution prerequisites found");
        } else {
            println!("ready: verification prerequisites found; native execution unavailable");
        }
        return ExitCode::SUCCESS;
    }
    let (Some(command), Some(file)) = (command, file) else {
        eprint!("{USAGE}");
        return ExitCode::from(2);
    };

    if command == "build" {
        return build_llvm(&file, &opts, entry, output.as_deref());
    }

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
            machine_profiles,
            machine_intrinsics,
            deferred,
            assumed,
            warnings,
            proof_assurance,
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
                for (id, hash) in &machine_profiles {
                    println!("  machine profile: {id} ({hash})");
                }
                if !machine_intrinsics.is_empty() {
                    println!("  machine intrinsics: {}", machine_intrinsics.join(", "));
                }
                println!(
                    "{}",
                    proof_assurance.status_line(
                        !deferred.is_empty() || !assumed.is_empty(),
                        !externs.is_empty(),
                    )
                );
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

fn build_llvm(
    file: &Path,
    opts: &Options,
    entry: Option<String>,
    output: Option<&Path>,
) -> ExitCode {
    let (mods, verified) = sable::verify_file_structured(file, opts);
    let verified = match verified {
        Ok(verified) => verified,
        Err(diags) => {
            for diag in &diags {
                eprintln!("{}", mods.render(diag));
            }
            eprintln!(
                "verification failed: {} error(s) in {}",
                diags.len(),
                file.display()
            );
            return ExitCode::FAILURE;
        }
    };

    let emit_opts = sable::llvm::EmitOptions { entry };
    let ir = match sable::llvm::emit_verified(&verified, &emit_opts) {
        Ok(ir) => ir,
        Err(diags) => {
            for diag in &diags {
                eprintln!("{}", mods.render(diag));
            }
            eprintln!(
                "LLVM lowering failed: {} error(s) in {}",
                diags.len(),
                file.display()
            );
            return ExitCode::FAILURE;
        }
    };

    let write_result = match output {
        Some(path) if path != Path::new("-") => write_atomic(path, ir.as_bytes()),
        _ => write_stdout(ir.as_bytes()),
    };
    if let Err(error) = write_result {
        let destination = output
            .filter(|path| *path != Path::new("-"))
            .map_or_else(|| "stdout".to_owned(), |path| path.display().to_string());
        eprintln!("error: could not write LLVM IR to {destination}: {error}");
        return ExitCode::FAILURE;
    }

    report_verified(file, verified.info(), &mods);
    ExitCode::SUCCESS
}

fn write_stdout(bytes: &[u8]) -> io::Result<()> {
    let stdout = io::stdout();
    let mut stdout = stdout.lock();
    stdout.write_all(bytes)?;
    stdout.flush()
}

fn report_verified(file: &Path, info: &VerifiedInfo, mods: &sable::modules::ModuleSet) {
    for warning in &info.warnings {
        eprintln!("{}", mods.render_level("warning", warning));
    }
    let proved = info.obligations - info.deferred.len() - info.assumed.len();
    eprintln!(
        "verified: {} — {} obligation(s) across {} function(s): \
         {proved} proved, {} deferred, {} assumed",
        file.display(),
        info.obligations,
        info.functions,
        info.deferred.len(),
        info.assumed.len(),
    );
    for deferred in &info.deferred {
        eprintln!("  deferred (sound runtime trap): {deferred}");
    }
    for (assumed, reason) in &info.assumed {
        eprintln!("  assumed (UNSOUND, audited):    {assumed} — {reason}");
    }
    if info.unsafe_regions > 0 {
        eprintln!("  unsafe regions: {}", info.unsafe_regions);
    }
    if !info.externs.is_empty() {
        eprintln!("  extern assumptions: {}", info.externs.len());
        for (id, reason, name) in &info.externs {
            eprintln!("    - {id} ({name}): {reason}");
        }
    }
    for (id, hash) in &info.machine_profiles {
        eprintln!("  machine profile: {id} ({hash})");
    }
    if !info.machine_intrinsics.is_empty() {
        eprintln!(
            "  machine intrinsics: {}",
            info.machine_intrinsics.join(", ")
        );
    }
    eprintln!(
        "{}",
        info.proof_assurance.status_line(
            !info.deferred.is_empty() || !info.assumed.is_empty(),
            !info.externs.is_empty(),
        )
    );
}

fn write_atomic(destination: &Path, bytes: &[u8]) -> io::Result<()> {
    let file_name = destination.file_name().ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidInput, "output path must name a file")
    })?;
    let parent = destination
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));

    let mut attempt = 0_u32;
    let (temp_path, mut temp) = loop {
        let temp_name = format!(
            ".{}.sable-tmp-{}-{attempt}",
            file_name.to_string_lossy(),
            std::process::id()
        );
        let temp_path = parent.join(temp_name);
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp_path)
        {
            Ok(temp) => break (temp_path, temp),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                attempt = attempt.checked_add(1).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        "no temporary filename available",
                    )
                })?;
            }
            Err(error) => return Err(error),
        }
    };

    if let Err(error) = temp.write_all(bytes).and_then(|()| temp.sync_all()) {
        drop(temp);
        let _ = fs::remove_file(&temp_path);
        return Err(error);
    }
    drop(temp);
    if let Err(error) = fs::rename(&temp_path, destination) {
        let _ = fs::remove_file(&temp_path);
        return Err(error);
    }
    Ok(())
}

#[cfg(test)]
mod status_tests {
    use sable::ProofAssurance;

    #[test]
    fn unaudited_dependencies_never_render_a_fully_verified_status() {
        assert_eq!(
            ProofAssurance::GeneratedOnly.status_line(false, false),
            "status: Lean generated only; proof not checked"
        );

        let cases = [
            (
                false,
                false,
                "status: Lean accepted; proof dependencies unaudited",
            ),
            (
                true,
                false,
                "status: Lean accepted with declared escapes; proof dependencies unaudited",
            ),
            (
                false,
                true,
                "status: Lean accepted relative to an audited extern boundary; proof dependencies unaudited",
            ),
            (
                true,
                true,
                "status: Lean accepted with declared escapes and an audited extern boundary; proof dependencies unaudited",
            ),
        ];

        for (has_declared_escapes, has_externs, expected) in cases {
            let actual = ProofAssurance::LeanAcceptedDependenciesUnaudited
                .status_line(has_declared_escapes, has_externs);
            assert_eq!(actual, expected);
            assert!(!actual.contains("fully verified"));
        }
    }
}

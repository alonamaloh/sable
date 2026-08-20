#!/usr/bin/env python3
"""Run Sable's curated trusted-base mutation experiments.

The runner always mutates an archived Git revision in a temporary directory.
It never copies or edits the caller's working tree.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from typing import Any


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
DEFAULT_MANIFEST = HERE / "mutations.json"
CLASSIFICATIONS = (
    "semantic-kill",
    "conservative-kill",
    "structural-kill",
    "compile-invalid",
    "crash",
    "timeout",
    "equivalent-or-survivor",
)
LOG_LIMIT = 32_000
PRINT_LOCK = threading.Lock()


class HarnessError(RuntimeError):
    pass


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def bounded_workers(raw: str) -> int:
    try:
        workers = int(raw)
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "must be an integer from 1 through 2"
        ) from error
    if not 1 <= workers <= 2:
        raise argparse.ArgumentTypeError("must be from 1 through 2")
    return workers


def progress(message: str) -> None:
    with PRINT_LOCK:
        print(message, file=sys.stderr, flush=True)


def clipped(value: str) -> str:
    if len(value) <= LOG_LIMIT:
        return value
    half = LOG_LIMIT // 2
    return value[:half] + "\n... output truncated ...\n" + value[-half:]


def run_process(
    argv: list[str], cwd: Path, env: dict[str, str], timeout: float
) -> dict[str, Any]:
    started = time.monotonic()
    try:
        proc = subprocess.Popen(
            argv,
            cwd=cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
            start_new_session=True,
        )
    except OSError as error:
        return {
            "argv": argv,
            "returncode": None,
            "timed_out": False,
            "spawn_error": str(error),
            "duration_seconds": round(time.monotonic() - started, 3),
            "stdout": "",
            "stderr": "",
        }
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=3)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = proc.communicate()
    return {
        "argv": argv,
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "duration_seconds": round(time.monotonic() - started, 3),
        "stdout": clipped(stdout),
        "stderr": clipped(stderr),
    }


def git_bytes(*args: str) -> bytes:
    try:
        completed = subprocess.run(
            ["git", "-C", str(REPO), *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as error:
        raise HarnessError(f"cannot execute git: {error}") from error
    if completed.returncode:
        raise HarnessError(completed.stderr.decode(errors="replace").strip())
    return completed.stdout


def resolve_revision(revision: str) -> str:
    return git_bytes("rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()


def safe_relative_path(raw: str) -> PurePosixPath:
    if not isinstance(raw, str):
        raise HarnessError(f"repository-relative path must be text, got {type(raw).__name__}")
    path = PurePosixPath(raw)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise HarnessError(f"unsafe repository-relative path: {raw!r}")
    return path


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise HarnessError(f"cannot read manifest {path}: {error}") from error
    if not isinstance(data, dict):
        raise HarnessError("manifest root must be a JSON object")
    schema_version = data.get("schema_version")
    if (
        type(schema_version) is not int
        or schema_version != 1
        or not isinstance(data.get("mutants"), list)
    ):
        raise HarnessError("manifest must have schema_version 1 and a mutants array")
    return data


def revision_text(revision: str, path: str, cache: dict[str, str]) -> str:
    if path not in cache:
        cache[path] = git_bytes("show", f"{revision}:{path}").decode("utf-8")
    return cache[path]


def validate_manifest(data: dict[str, Any], revision: str) -> dict[str, Any]:
    errors: list[str] = []
    ids: set[str] = set()
    source_cache: dict[str, str] = {}
    allowed_families = {"certificate", "checker", "control", "vc"}
    certificate_paths = {
        "compiler/src/argument_schedule.rs",
        "lean/Sable/Transition.lean",
    }
    for index, mutant in enumerate(data["mutants"]):
        where = f"mutants[{index}]"
        if not isinstance(mutant, dict):
            errors.append(f"{where}: mutant must be an object")
            continue
        mutant_sources: dict[str, str] = {}
        mid = mutant.get("id")
        if not isinstance(mid, str) or not re.fullmatch(r"[a-z0-9_.-]+", mid):
            errors.append(f"{where}: invalid id")
        elif mid in ids:
            errors.append(f"{where}: duplicate id {mid}")
        else:
            ids.add(mid)
        family = mutant.get("family")
        if not isinstance(family, str) or family not in allowed_families:
            errors.append(
                f"{where}: family must be certificate, checker, control, or vc"
            )
        if not isinstance(mutant.get("description"), str) or not mutant["description"]:
            errors.append(f"{where}: description is required")
        edits = mutant.get("edits")
        if not isinstance(edits, list) or not edits:
            errors.append(f"{where}: at least one edit is required")
            edits = []
        for edit_index, edit in enumerate(edits):
            edit_where = f"{where}.edits[{edit_index}]"
            if not isinstance(edit, dict):
                errors.append(f"{edit_where}: edit must be an object")
                continue
            path = edit.get("file")
            before = edit.get("before")
            after = edit.get("after")
            try:
                safe_relative_path(path)
            except (HarnessError, TypeError) as error:
                errors.append(f"{edit_where}: {error}")
                continue
            if family == "certificate" and path not in certificate_paths:
                errors.append(
                    f"{edit_where}: certificate mutations are limited to "
                    "compiler/src/argument_schedule.rs or lean/Sable/Transition.lean"
                )
            elif family != "certificate" and not path.startswith("compiler/src/"):
                errors.append(
                    f"{edit_where}: non-certificate mutations are limited to compiler/src"
                )
            if not isinstance(before, str) or not before:
                errors.append(f"{edit_where}: before must be non-empty text")
                continue
            if not isinstance(after, str) or before == after:
                errors.append(f"{edit_where}: after must differ from before")
                continue
            try:
                source = mutant_sources.get(path)
                if source is None:
                    source = revision_text(revision, path, source_cache)
                count = source.count(before)
            except (HarnessError, UnicodeDecodeError) as error:
                errors.append(f"{edit_where}: cannot read {path}: {error}")
                continue
            if count != 1:
                errors.append(
                    f"{edit_where}: before text occurs {count} times at {revision[:12]}, expected 1"
                )
                continue
            old_after_count = source.count(after)
            patched = source.replace(before, after, 1)
            if patched.count(after) != old_after_count + 1:
                errors.append(f"{edit_where}: after text was not inserted exactly once")
                continue
            if before not in after and patched.count(before) != 0:
                errors.append(f"{edit_where}: before text remains after the patch")
                continue
            mutant_sources[path] = patched
        oracles = mutant.get("oracles")
        if not isinstance(oracles, list) or not oracles:
            errors.append(f"{where}: at least one oracle is required")
            oracles = []
        for oracle_index, oracle in enumerate(oracles):
            oracle_where = f"{where}.oracles[{oracle_index}]"
            if not isinstance(oracle, dict):
                errors.append(f"{oracle_where}: oracle must be an object")
                continue
            kind = oracle.get("kind")
            if kind == "source":
                source = oracle.get("path")
                try:
                    safe_relative_path(source)
                    git_bytes("cat-file", "-e", f"{revision}:{source}")
                except (HarnessError, TypeError) as error:
                    errors.append(f"{oracle_where}: missing/unsafe source: {error}")
                expectation = oracle.get("expect")
                if not isinstance(expectation, str) or expectation not in {
                    "failed",
                    "verified",
                }:
                    errors.append(f"{oracle_where}: source expect must be failed or verified")
                marker = oracle.get("baseline_contains")
                if expectation == "failed" and (
                    not isinstance(marker, str) or not marker
                ):
                    errors.append(
                        f"{oracle_where}: failed source requires a non-empty baseline_contains"
                    )
                elif marker is not None and not isinstance(marker, str):
                    errors.append(f"{oracle_where}: baseline_contains must be text")
                if "diagnostic" in oracle:
                    errors.append(
                        f"{oracle_where}: use a rendered baseline_contains marker, not diagnostic"
                    )
                module_paths = oracle.get("module_paths", [])
                if not isinstance(module_paths, list):
                    errors.append(f"{oracle_where}: module_paths must be an array")
                    module_paths = []
                for module_path in module_paths:
                    try:
                        safe_relative_path(module_path)
                        git_bytes("cat-file", "-e", f"{revision}:{module_path}")
                    except (HarnessError, TypeError) as error:
                        errors.append(f"{oracle_where}: bad module path: {error}")
            elif kind == "cargo-test":
                if not isinstance(oracle.get("test"), str) or not oracle["test"]:
                    errors.append(f"{oracle_where}: cargo-test requires test")
            else:
                errors.append(f"{oracle_where}: unknown oracle kind {kind!r}")
    return {
        "valid": not errors,
        "revision": revision,
        "mutant_count": len(data["mutants"]),
        "families": {
            family: sum(
                1
                for m in data["mutants"]
                if isinstance(m, dict) and m.get("family") == family
            )
            for family in sorted(allowed_families)
        },
        "errors": errors,
    }


def extract_revision(revision: str, destination: Path) -> None:
    archive = git_bytes("archive", "--format=tar", revision)
    destination.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as tar:
        root = destination.resolve()
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if root != target and root not in target.parents:
                raise HarnessError(f"archive contains unsafe path {member.name!r}")
            if not (member.isdir() or member.isfile()):
                raise HarnessError(f"archive contains unsupported link/device {member.name!r}")
        tar.extractall(destination)


def worker_env(target: Path) -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        {
            "CARGO_TARGET_DIR": str(target),
            "CARGO_BUILD_JOBS": "1",
            "CARGO_INCREMENTAL": "1",
            "CARGO_TERM_COLOR": "never",
            "LEAN_IMPORT_WORKERS": "1",
            "LEAN_NUM_THREADS": "0",
            "SABLE_TEST_JOBS": "1",
        }
    )
    return env


def reset_sable_out(checkout: Path) -> None:
    output = checkout / ".sable-out"
    if not output.exists():
        return
    for child in output.iterdir():
        if child.name == "proof-envs":
            continue
        if child.is_dir() and not child.is_symlink():
            shutil.rmtree(child)
        else:
            child.unlink()


def build(checkout: Path, env: dict[str, str], timeout: float) -> dict[str, Any]:
    return run_process(
        [
            "cargo",
            "build",
            "--locked",
            "--manifest-path",
            str(checkout / "compiler/Cargo.toml"),
        ],
        checkout,
        env,
        timeout,
    )


def oracle_key(oracle: dict[str, Any]) -> str:
    return json.dumps(oracle, sort_keys=True, separators=(",", ":"))


def run_oracle(
    oracle: dict[str, Any], checkout: Path, target: Path, env: dict[str, str], timeout: float
) -> dict[str, Any]:
    reset_sable_out(checkout)
    if oracle["kind"] == "source":
        argv = [str(target / "debug/sable"), "check", str(checkout / oracle["path"])]
        for module_path in oracle.get("module_paths", []):
            argv.extend(["-M", str(checkout / module_path)])
    else:
        argv = [
            "cargo",
            "test",
            "--locked",
            "--manifest-path",
            str(checkout / "compiler/Cargo.toml"),
            "--lib",
            oracle["test"],
            "--",
            "--exact",
            "--nocapture",
        ]
    return run_process(argv, checkout, env, timeout)


def baseline_matches(oracle: dict[str, Any], result: dict[str, Any]) -> tuple[bool, str]:
    if "spawn_error" in result:
        return False, f"baseline oracle could not start: {result['spawn_error']}"
    if result["timed_out"]:
        return False, "baseline oracle timed out"
    if oracle["kind"] == "cargo-test":
        if result["returncode"] != 0:
            return False, "baseline cargo test failed"
        return cargo_test_ran_once(oracle, result, "ok")
    if process_crashed(result):
        return False, "baseline source oracle crashed"
    expected_success = oracle["expect"] == "verified"
    actual_success = result["returncode"] == 0
    if expected_success != actual_success:
        return False, f"baseline expected {oracle['expect']}, got return code {result['returncode']}"
    marker = oracle.get("baseline_contains")
    combined = result["stdout"] + result["stderr"]
    if marker and marker not in combined:
        return False, f"baseline output lacks rendered marker {marker!r}"
    return True, ""


def cargo_test_ran_once(
    oracle: dict[str, Any], result: dict[str, Any], expected_status: str
) -> tuple[bool, str]:
    """Authenticate Cargo's filter instead of treating a zero-test run as success."""
    combined = result["stdout"] + "\n" + result["stderr"]
    running = re.findall(r"(?m)^running (\d+) tests?\s*$", combined)
    if running != ["1"]:
        return False, f"cargo reported test counts {running!r}, expected exactly one run"
    test = re.escape(oracle["test"])
    statuses = re.findall(rf"(?m)^test {test} \.\.\. (ok|FAILED|ignored)\s*$", combined)
    if statuses != [expected_status]:
        return False, (
            f"cargo did not report exactly one `{oracle['test']}` result "
            f"with status {expected_status!r}: {statuses!r}"
        )
    return True, ""


def process_crashed(result: dict[str, Any]) -> bool:
    returncode = result.get("returncode")
    combined = result.get("stdout", "") + result.get("stderr", "")
    return bool(
        (isinstance(returncode, int) and returncode < 0)
        or "thread 'main' panicked at" in combined
        or "fatal runtime error:" in combined
    )


def looks_compile_invalid(result: dict[str, Any]) -> bool:
    combined = result["stdout"] + result["stderr"]
    return bool(
        "could not compile `sable`" in combined
        or "error: could not compile" in combined
        or re.search(r"error\[E\d{4}\]", combined)
    )


def classify_oracle(
    oracle: dict[str, Any], baseline: dict[str, Any], mutated: dict[str, Any]
) -> dict[str, Any]:
    detail: dict[str, Any] = {
        "kind": oracle["kind"],
        "oracle": oracle,
        "baseline": baseline,
        "mutated": mutated,
    }
    if mutated["timed_out"]:
        detail["classification"] = "timeout"
        return detail
    if "spawn_error" in mutated:
        detail["harness_error"] = f"oracle could not start: {mutated['spawn_error']}"
        return detail
    if oracle["kind"] == "cargo-test":
        if mutated["returncode"] == 0:
            observed, reason = cargo_test_ran_once(oracle, mutated, "ok")
            if not observed:
                detail["harness_error"] = reason
            else:
                detail["classification"] = "equivalent-or-survivor"
        elif looks_compile_invalid(mutated):
            detail["classification"] = "compile-invalid"
        else:
            observed, reason = cargo_test_ran_once(oracle, mutated, "FAILED")
            if observed:
                detail["classification"] = "structural-kill"
            elif process_crashed(mutated):
                detail["classification"] = "crash"
                detail["note"] = reason
            else:
                detail["harness_error"] = reason
        return detail
    if process_crashed(mutated):
        detail["classification"] = "crash"
        return detail
    baseline_success = baseline["returncode"] == 0
    mutated_success = mutated["returncode"] == 0
    if not baseline_success and mutated_success:
        detail["classification"] = "semantic-kill"
    elif baseline_success and not mutated_success:
        detail["classification"] = "conservative-kill"
    else:
        detail["classification"] = "equivalent-or-survivor"
        marker = oracle.get("baseline_contains")
        if marker and marker not in mutated["stdout"] + mutated["stderr"]:
            detail["diagnostic_only_change"] = True
            detail["note"] = (
                "the mutant still rejects the source; diagnostic drift is not a soundness kill"
            )
    return detail


def apply_edits(
    mutant: dict[str, Any], checkout: Path, originals: dict[Path, bytes]
) -> None:
    """Apply one mutant, restoring partial writes before propagating any error."""
    try:
        for edit in mutant["edits"]:
            path = checkout.joinpath(*safe_relative_path(edit["file"]).parts)
            if path not in originals:
                originals[path] = path.read_bytes()
            source = path.read_text(encoding="utf-8")
            count = source.count(edit["before"])
            if count != 1:
                raise HarnessError(
                    f"{mutant['id']}: {edit['file']} anchor occurs {count} times, expected 1"
                )
            old_after_count = source.count(edit["after"])
            patched = source.replace(edit["before"], edit["after"], 1)
            if patched.count(edit["after"]) != old_after_count + 1:
                raise HarnessError(f"{mutant['id']}: after text was not inserted exactly once")
            if edit["before"] not in edit["after"] and patched.count(edit["before"]) != 0:
                raise HarnessError(f"{mutant['id']}: before text remains after the patch")
            path.write_text(patched, encoding="utf-8")
    except Exception:
        restore_edits(originals)
        raise


def restore_edits(originals: dict[Path, bytes]) -> None:
    for path, contents in originals.items():
        path.write_bytes(contents)


def strongest(details: list[dict[str, Any]]) -> str:
    classes = {detail["classification"] for detail in details}
    for classification in (
        "semantic-kill",
        "conservative-kill",
        "structural-kill",
        "compile-invalid",
        "crash",
        "timeout",
        "equivalent-or-survivor",
    ):
        if classification in classes:
            return classification
    raise AssertionError("no oracle classifications")


def _run_chunk(
    worker: int,
    mutants: list[dict[str, Any]],
    revision: str,
    compile_timeout: float,
    oracle_timeout: float,
) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix=f"sable-mutations-{worker}-") as temporary:
        root = Path(temporary)
        checkout = root / "checkout"
        target = root / "cargo-target"
        progress(f"worker {worker}: extracting {revision[:12]}")
        extract_revision(revision, checkout)
        env = worker_env(target)
        progress(f"worker {worker}: compiling pristine baseline")
        baseline_build = build(checkout, env, compile_timeout)
        if baseline_build["timed_out"] or baseline_build["returncode"] != 0:
            if "spawn_error" in baseline_build:
                message = f"baseline build could not start: {baseline_build['spawn_error']}"
            elif baseline_build["timed_out"]:
                message = "baseline build timed out"
            else:
                message = "baseline build failed"
            return [
                {
                    "id": mutant["id"],
                    "family": mutant["family"],
                    "status": "harness-error",
                    "error": message,
                    "baseline_build": baseline_build,
                }
                for mutant in mutants
            ]
        baseline_oracles: dict[str, dict[str, Any]] = {}
        for mutant in mutants:
            for oracle in mutant["oracles"]:
                key = oracle_key(oracle)
                if key in baseline_oracles:
                    continue
                progress(f"worker {worker}: baseline oracle for {mutant['id']}")
                baseline = run_oracle(oracle, checkout, target, env, oracle_timeout)
                okay, reason = baseline_matches(oracle, baseline)
                if not okay:
                    baseline["harness_error"] = reason
                baseline_oracles[key] = baseline
        for mutant in mutants:
            started = time.monotonic()
            invalid_baselines = [
                baseline_oracles[oracle_key(oracle)]
                for oracle in mutant["oracles"]
                if "harness_error" in baseline_oracles[oracle_key(oracle)]
            ]
            if invalid_baselines:
                results.append(
                    {
                        "id": mutant["id"],
                        "family": mutant["family"],
                        "status": "harness-error",
                        "error": invalid_baselines[0]["harness_error"],
                        "baseline": invalid_baselines[0],
                    }
                )
                continue
            originals: dict[Path, bytes] = {}
            try:
                reset_sable_out(checkout)
                apply_edits(mutant, checkout, originals)
                progress(f"worker {worker}: compiling {mutant['id']}")
                mutated_build = build(checkout, env, compile_timeout)
                result: dict[str, Any] = {
                    "id": mutant["id"],
                    "family": mutant["family"],
                    "description": mutant["description"],
                    "status": "completed",
                    "build": mutated_build,
                }
                if "spawn_error" in mutated_build:
                    raise HarnessError(
                        f"mutant build could not start: {mutated_build['spawn_error']}"
                    )
                if mutated_build["timed_out"]:
                    result["classification"] = "timeout"
                    result["oracles"] = []
                elif mutated_build["returncode"] != 0:
                    result["classification"] = "compile-invalid"
                    result["oracles"] = []
                else:
                    details = []
                    for oracle in mutant["oracles"]:
                        progress(f"worker {worker}: oracle {mutant['id']}")
                        mutated = run_oracle(oracle, checkout, target, env, oracle_timeout)
                        details.append(
                            classify_oracle(
                                oracle, baseline_oracles[oracle_key(oracle)], mutated
                            )
                        )
                    result["oracles"] = details
                    invalid = next(
                        (detail for detail in details if "harness_error" in detail), None
                    )
                    if invalid is not None:
                        result["status"] = "harness-error"
                        result["error"] = invalid["harness_error"]
                    else:
                        result["classification"] = strongest(details)
                result["duration_seconds"] = round(time.monotonic() - started, 3)
                results.append(result)
            except Exception as error:
                results.append(
                    {
                        "id": mutant["id"],
                        "family": mutant["family"],
                        "status": "harness-error",
                        "error": str(error),
                    }
                )
            finally:
                restore_edits(originals)
                reset_sable_out(checkout)
    return results


def run_chunk(
    worker: int,
    mutants: list[dict[str, Any]],
    revision: str,
    compile_timeout: float,
    oracle_timeout: float,
) -> list[dict[str, Any]]:
    try:
        return _run_chunk(worker, mutants, revision, compile_timeout, oracle_timeout)
    except Exception as error:
        return [
            {
                "id": mutant.get("id", f"worker-{worker}-unknown"),
                "family": mutant.get("family", "unknown"),
                "status": "harness-error",
                "error": f"worker setup failed ({type(error).__name__}): {error}",
            }
            for mutant in mutants
        ]


def select_mutants(
    data: dict[str, Any], requested: list[str], limit: int | None
) -> list[dict[str, Any]]:
    all_mutants = data["mutants"]
    if requested:
        by_id = {mutant["id"]: mutant for mutant in all_mutants}
        missing = [mid for mid in requested if mid not in by_id]
        if missing:
            raise HarnessError(f"unknown mutant(s): {', '.join(missing)}")
        selected = [by_id[mid] for mid in requested]
    else:
        selected = list(all_mutants)
    if limit is not None:
        selected = selected[:limit]
    if not selected:
        raise HarnessError("no mutants selected")
    return selected


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    result.add_argument("--revision", default="HEAD", help="committed revision to archive")
    result.add_argument("--list", action="store_true", help="list curated mutants and exit")
    result.add_argument("--dry-run", action="store_true", help="validate anchors/oracles and exit")
    result.add_argument("--mutant", action="append", default=[], help="run one id; repeatable")
    result.add_argument("--limit", type=int, help="run the first N selected mutants")
    result.add_argument(
        "--workers",
        type=bounded_workers,
        default=2,
        metavar="{1,2}",
        help="bounded mutation workers (default: 2)",
    )
    result.add_argument("--compile-timeout", type=float, default=300.0)
    result.add_argument("--timeout", type=float, default=180.0, help="per-oracle timeout")
    result.add_argument("--report", type=Path, help="write JSON here instead of stdout")
    return result


def emit_report(report: dict[str, Any], path: Path | None) -> None:
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if path is None:
        sys.stdout.write(rendered)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered, encoding="utf-8")
        progress(f"wrote {path}")


def main() -> int:
    args = parser().parse_args()
    try:
        data = load_manifest(args.manifest.resolve())
        revision = resolve_revision(args.revision)
        validation = validate_manifest(data, revision)
        if args.list:
            if not validation["valid"]:
                raise HarnessError(
                    "manifest validation failed:\n  " + "\n  ".join(validation["errors"])
                )
            for mutant in data["mutants"]:
                print(f"{mutant['id']:<52} {mutant['family']:<7} {mutant['description']}")
            return 0
        if args.dry_run:
            emit_report({"mode": "dry-run", **validation}, args.report)
            return 0 if validation["valid"] else 2
        if not validation["valid"]:
            raise HarnessError("manifest validation failed:\n  " + "\n  ".join(validation["errors"]))
        selected = select_mutants(data, args.mutant, args.limit)
        if args.compile_timeout <= 0 or args.timeout <= 0:
            raise HarnessError("timeouts must be positive")
        worker_count = min(args.workers, len(selected))
        chunks = [selected[index::worker_count] for index in range(worker_count)]
        started_at = utc_now()
        started = time.monotonic()
        collected: list[dict[str, Any]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as executor:
            futures = {
                executor.submit(
                    run_chunk,
                    index + 1,
                    chunk,
                    revision,
                    args.compile_timeout,
                    args.timeout,
                ): chunk
                for index, chunk in enumerate(chunks)
            }
            for future in concurrent.futures.as_completed(futures):
                chunk = futures[future]
                try:
                    collected.extend(future.result())
                except Exception as error:
                    collected.extend(
                        {
                            "id": mutant["id"],
                            "family": mutant["family"],
                            "status": "harness-error",
                            "error": (
                                f"worker future failed ({type(error).__name__}): {error}"
                            ),
                        }
                        for mutant in chunk
                    )
        order = {mutant["id"]: index for index, mutant in enumerate(selected)}
        collected.sort(key=lambda result: order[result["id"]])
        counts = {classification: 0 for classification in CLASSIFICATIONS}
        harness_errors = 0
        for result in collected:
            classification = result.get("classification")
            if classification in counts:
                counts[classification] += 1
            else:
                harness_errors += 1
        report = {
            "schema_version": 1,
            "mode": "run",
            "revision": revision,
            "started_at": started_at,
            "finished_at": utc_now(),
            "duration_seconds": round(time.monotonic() - started, 3),
            "workers": worker_count,
            "selected": [mutant["id"] for mutant in selected],
            "summary": {"classifications": counts, "harness_errors": harness_errors},
            "results": collected,
        }
        emit_report(report, args.report)
        return 2 if harness_errors else 0
    except HarnessError as error:
        print(f"soundness mutation harness: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

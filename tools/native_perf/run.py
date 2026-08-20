#!/usr/bin/env python3
"""Fail-closed native-vs-C benchmark runner for the bounded Sable workloads."""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import math
import os
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = Path(__file__).with_name("workloads.json")
DEFAULT_CLOSURE = Path(__file__).with_name("closure.json")
SCHEMA_VERSION = 2
OPTIMIZATION = "-O2"
SAFE_WORKLOAD_ID = re.compile(r"[a-z0-9_]+\Z")
SAFE_ENTRY = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
SHA256_TEXT = re.compile(r"[0-9a-f]{64}\Z")
COMMIT_TEXT = re.compile(r"[0-9a-f]{40}\Z")
VERIFICATION_SUMMARY = re.compile(
    r"^verified: .+ — (\d+) obligation\(s\) across (\d+) function\(s\): "
    r"(\d+) proved, (\d+) deferred, (\d+) assumed$",
    re.MULTILINE,
)


class HarnessError(RuntimeError):
    pass


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit native admission and compare authenticated Sable/C -O2 workload pairs."
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--closure", type=Path, default=DEFAULT_CLOSURE)
    parser.add_argument(
        "--compiler",
        type=Path,
        help="explicit compiler binary (default: build current checkout in release mode)",
    )
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--machine-label", required=True)
    parser.add_argument("--warmups", type=nonnegative_int, default=3)
    parser.add_argument("--samples", type=positive_int, default=15)
    parser.add_argument("--timeout-seconds", type=positive_int, default=900)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allow-dirty", action="store_true")
    parser.add_argument(
        "--only",
        action="append",
        default=[],
        metavar="WORKLOAD",
        help="run one workload id (repeatable)",
    )
    return parser.parse_args()


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return parsed


def load_object(path: Path) -> dict[str, Any]:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise HarnessError(f"cannot load {path}: {error}") from error
    if not isinstance(loaded, dict):
        raise HarnessError(f"{path} must contain a JSON object")
    return loaded


def command(
    arguments: list[str], timeout: int, *, check: bool = False
) -> subprocess.CompletedProcess[str]:
    try:
        result = subprocess.run(
            arguments,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise HarnessError(f"command failed to start or finish: {arguments!r}: {error}") from error
    if check and result.returncode != 0:
        raise HarnessError(
            f"command failed ({result.returncode}): {arguments!r}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def first_line(arguments: list[str], timeout: int) -> str:
    result = command(arguments, timeout, check=True)
    combined = result.stdout.strip() or result.stderr.strip()
    return combined.splitlines()[0] if combined else ""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise HarnessError(f"cannot hash {path}: {error}") from error
    return digest.hexdigest()


def percentile_nearest_rank(values: list[int], percentile: float) -> int:
    ordered = sorted(values)
    rank = max(1, math.ceil(percentile * len(ordered)))
    return ordered[rank - 1]


def timing_summary(values: list[int], work_units: int) -> dict[str, Any]:
    median = int(statistics.median(values))
    return {
        "samples_ns": values,
        "min_ns": min(values),
        "median_ns": median,
        "p95_ns": percentile_nearest_rank(values, 0.95),
        "median_ns_per_work_unit": median / work_units,
    }


def timed_run(executable: Path, expected_exit: int, timeout: int) -> int:
    start = time.perf_counter_ns()
    result = command([str(executable)], timeout)
    elapsed = time.perf_counter_ns() - start
    if result.returncode != expected_exit:
        raise HarnessError(
            f"semantic probe for {executable} exited {result.returncode}, expected "
            f"{expected_exit}; stdout={result.stdout!r}, stderr={result.stderr!r}"
        )
    return elapsed


def validate_manifest(
    manifest: dict[str, Any], closure: dict[str, Any], only: list[str]
) -> list[dict[str, Any]]:
    manifest_keys = {"schema_version", "module_paths", "hosted_runtime", "workloads"}
    closure_keys = {
        "schema_version",
        "audited_base_revision",
        "audited_date",
        "native_optimization",
        "hosted_runtime_sha256",
        "workloads",
    }
    if set(manifest) != manifest_keys:
        raise HarnessError(
            f"manifest fields must be exactly {', '.join(sorted(manifest_keys))}"
        )
    if set(closure) != closure_keys:
        raise HarnessError(
            f"closure fields must be exactly {', '.join(sorted(closure_keys))}"
        )
    if (
        type(manifest.get("schema_version")) is not int
        or manifest.get("schema_version") != SCHEMA_VERSION
        or type(closure.get("schema_version")) is not int
        or closure.get("schema_version") != SCHEMA_VERSION
    ):
        raise HarnessError(
            f"manifest and closure schema_version must both be {SCHEMA_VERSION}"
        )
    module_paths = manifest.get("module_paths")
    if (
        not isinstance(module_paths, list)
        or not module_paths
        or any(type(path) is not str or not path for path in module_paths)
    ):
        raise HarnessError("manifest module_paths must be a nonempty list of strings")
    if type(manifest.get("hosted_runtime")) is not str or not manifest["hosted_runtime"]:
        raise HarnessError("manifest hosted_runtime must be a nonempty string")
    audited_revision = closure.get("audited_base_revision")
    if type(audited_revision) is not str or not COMMIT_TEXT.fullmatch(audited_revision):
        raise HarnessError("closure audited_base_revision must be a lowercase 40-hex commit")
    audited_date = closure.get("audited_date")
    if type(audited_date) is not str:
        raise HarnessError("closure audited_date must be an ISO date string")
    try:
        parsed_date = datetime.date.fromisoformat(audited_date)
    except ValueError as error:
        raise HarnessError("closure audited_date must be a valid ISO date") from error
    if parsed_date.isoformat() != audited_date:
        raise HarnessError("closure audited_date must use canonical YYYY-MM-DD form")
    if closure.get("native_optimization") != OPTIMIZATION:
        raise HarnessError(f"closure native_optimization must be {OPTIMIZATION!r}")
    runtime_hash = closure.get("hosted_runtime_sha256")
    if type(runtime_hash) is not str or not SHA256_TEXT.fullmatch(runtime_hash):
        raise HarnessError("closure hosted_runtime_sha256 must be lowercase SHA-256")
    workloads = manifest.get("workloads")
    closures = closure.get("workloads")
    if not isinstance(workloads, list) or not isinstance(closures, dict):
        raise HarnessError("manifest workloads must be a list and closure workloads an object")
    seen: set[str] = set()
    selected: list[dict[str, Any]] = []
    required = {
        "id": str,
        "verified_subject": str,
        "sable_source": str,
        "entry": str,
        "c_source": str,
        "work_units": int,
        "expected_exit": int,
        "semantic_profile": str,
    }
    optional = {"scope_nonclaim": str}
    requested = set(only)
    for workload in workloads:
        if not isinstance(workload, dict):
            raise HarnessError("every manifest workload must be an object")
        allowed_fields = set(required) | set(optional)
        if set(workload) - allowed_fields or set(required) - set(workload):
            raise HarnessError(
                "each workload must contain exactly the required fields plus optional "
                "scope_nonclaim"
            )
        for field, field_type in required.items():
            if type(workload.get(field)) is not field_type:
                raise HarnessError(f"workload field {field!r} must be {field_type.__name__}")
            if field_type is str and not workload[field]:
                raise HarnessError(f"workload field {field!r} must not be empty")
        for field, field_type in optional.items():
            if field in workload and (
                type(workload[field]) is not field_type or not workload[field]
            ):
                raise HarnessError(f"workload field {field!r} must be a nonempty string")
        workload_id = workload["id"]
        if not SAFE_WORKLOAD_ID.fullmatch(workload_id):
            raise HarnessError(
                f"workload id {workload_id!r} must match lowercase [a-z0-9_]+"
            )
        if not SAFE_ENTRY.fullmatch(workload["entry"]):
            raise HarnessError(f"workload {workload_id!r} has an invalid entry name")
        if workload_id in seen:
            raise HarnessError(f"duplicate workload id {workload_id!r}")
        seen.add(workload_id)
        if workload_id not in closures:
            raise HarnessError(f"workload {workload_id!r} has no closure record")
        if workload["work_units"] <= 0:
            raise HarnessError(f"workload {workload_id!r} has nonpositive work_units")
        if not 0 <= workload["expected_exit"] <= 255:
            raise HarnessError(f"workload {workload_id!r} has an invalid process exit oracle")
        record = closures[workload_id]
        if not isinstance(record, dict):
            raise HarnessError(f"closure record {workload_id!r} must be an object")
        status = record.get("expected_status")
        source_hashes = record.get("source_sha256")
        if status not in {"admitted", "blocked"} or not isinstance(source_hashes, dict):
            raise HarnessError(f"closure record {workload_id!r} has invalid common fields")
        if set(source_hashes) != {"verified_subject", "sable", "c"}:
            raise HarnessError(
                f"closure record {workload_id!r} must authenticate exactly three sources"
            )
        for source_role, digest in source_hashes.items():
            if type(digest) is not str or not SHA256_TEXT.fullmatch(digest):
                raise HarnessError(
                    f"closure record {workload_id!r} has invalid {source_role} SHA-256"
                )
        if status == "blocked":
            expected_fields = {
                "expected_status",
                "title_fragment",
                "detail_fragment",
                "closure",
                "source_sha256",
            }
            if set(record) != expected_fields:
                raise HarnessError(
                    f"blocked closure record {workload_id!r} has unexpected fields"
                )
            for field in ("title_fragment", "detail_fragment", "closure"):
                if type(record.get(field)) is not str or not record[field]:
                    raise HarnessError(
                        f"blocked closure {workload_id!r} needs nonempty {field}"
                    )
        else:
            common_fields = {
                "expected_status",
                "scope",
                "comparison_eligibility",
                "optimized_ir_shape_profile",
                "source_sha256",
            }
            eligibility = record.get("comparison_eligibility")
            expected_fields = set(common_fields)
            if eligibility == "optimization_trivialized":
                expected_fields.add("noncomparable_reason")
            if set(record) != expected_fields:
                raise HarnessError(
                    f"admitted closure record {workload_id!r} has unexpected fields"
                )
            if eligibility not in {"comparable", "optimization_trivialized"}:
                raise HarnessError(
                    f"admitted closure {workload_id!r} has invalid comparison eligibility"
                )
            for field in ("scope", "optimized_ir_shape_profile"):
                if type(record.get(field)) is not str or not record[field]:
                    raise HarnessError(
                        f"admitted closure {workload_id!r} needs nonempty {field}"
                    )
            if record["optimized_ir_shape_profile"] != workload_id:
                raise HarnessError(
                    f"admitted closure {workload_id!r} must use its identically named "
                    "hardcoded shape profile"
                )
            if eligibility == "optimization_trivialized" and (
                type(record.get("noncomparable_reason")) is not str
                or not record["noncomparable_reason"]
            ):
                raise HarnessError(
                    f"non-comparable closure {workload_id!r} needs a reason"
                )
        if not requested or workload_id in requested:
            selected.append(workload)
    unknown = requested - seen
    if unknown:
        raise HarnessError(f"unknown --only workload(s): {', '.join(sorted(unknown))}")
    if set(closures) != seen:
        extra = set(closures) - seen
        raise HarnessError(f"closure has unknown workload(s): {', '.join(sorted(extra))}")
    return selected


def parse_verification_summary(build_text: str) -> dict[str, Any]:
    matches = list(VERIFICATION_SUMMARY.finditer(build_text))
    status_lines = re.findall(r"^status: (.+)$", build_text, re.MULTILINE)
    unsafe_lines = re.findall(r"^\s*unsafe regions: (\d+)$", build_text, re.MULTILINE)
    extern_lines = re.findall(r"^\s*extern assumptions: (\d+)$", build_text, re.MULTILINE)
    reasons: list[str] = []
    summary: dict[str, Any] = {
        "summary_count": len(matches),
        "status_lines": status_lines,
        "unsafe_regions": sum(int(value) for value in unsafe_lines),
        "extern_assumptions": sum(int(value) for value in extern_lines),
    }
    if len(matches) != 1:
        reasons.append("expected_exactly_one_verification_summary")
    else:
        obligations, functions, proved, deferred, assumed = (
            int(value) for value in matches[0].groups()
        )
        summary.update(
            {
                "obligations": obligations,
                "functions": functions,
                "proved": proved,
                "deferred": deferred,
                "assumed": assumed,
            }
        )
        if obligations != proved + deferred + assumed:
            reasons.append("verification_counts_do_not_sum")
        if deferred != 0:
            reasons.append("deferred_obligations_present")
        if assumed != 0:
            reasons.append("assumed_obligations_present")
    if status_lines != ["fully verified"]:
        reasons.append("status_is_not_uniquely_fully_verified")
    if unsafe_lines:
        reasons.append("unsafe_regions_present")
    if extern_lines:
        reasons.append("extern_assumptions_present")
    summary["accepted_for_comparison"] = not reasons
    summary["rejection_reasons"] = reasons
    return summary


def authenticate_blocked_refusal(
    build: subprocess.CompletedProcess[str],
    build_text: str,
    expected: dict[str, Any],
    sable_source: Path,
) -> dict[str, Any]:
    lines = [line for line in build_text.splitlines() if line]
    title = expected["title_fragment"]
    detail = expected["detail_fragment"]
    terminal = f"LLVM lowering failed: 1 error(s) in {sable_source}"
    checks = {
        "returncode_is_one": build.returncode == 1,
        "exactly_one_error_heading": sum(
            line.startswith("error: ") for line in lines
        )
        == 1,
        "title_occurs_once": build_text.count(title) == 1,
        "detail_occurs_once": build_text.count(detail) == 1,
        "terminal_summary_exact": bool(lines) and lines[-1] == terminal,
        "no_verification_failure": "verification failed" not in build_text.lower(),
    }
    return {"passed": all(checks.values()), "checks": checks, "terminal": terminal}


def optimized_ir_shape(profile: str, ir_text: str) -> dict[str, Any]:
    ssa = r"%[-A-Za-z$._0-9]+"

    def count(pattern: str) -> int:
        return len(re.findall(pattern, ir_text, re.MULTILINE))

    dynamic_loads = count(rf"^\s*{ssa}\s*=\s*load i32,")
    dynamic_stores = count(rf"^\s*store i32 {ssa},")
    unsigned_load_ordering = count(
        rf"^\s*{ssa}\s*=\s*icmp (?:samesign )?u(?:gt|ge|lt|le) i32 {ssa}, {ssa}"
    )
    ordering_comparisons = count(
        rf"^\s*{ssa}\s*=\s*icmp (?:samesign )?[us](?:gt|ge|lt|le) i32 "
    )
    dynamic_gep_names = set(
        re.findall(
            rf"^\s*({ssa})\s*=\s*getelementptr[^\n]*\bi64 {ssa}(?:,|$)",
            ir_text,
            re.MULTILINE,
        )
    )
    stores_through_dynamic_gep = sum(
        count(rf"^\s*store i32 [^,\n]+, ptr {re.escape(name)}(?:,|$)")
        for name in dynamic_gep_names
    )
    common_counts = {
        "dynamic_i32_loads": dynamic_loads,
        "dynamic_i32_stores": dynamic_stores,
        "dynamic_load_to_load_unsigned_ordering_compares": unsigned_load_ordering,
        "i32_ordering_compares": ordering_comparisons,
        "stores_through_dynamic_index_gep": stores_through_dynamic_gep,
    }
    if profile == "lomuto_partition_u32":
        requirements = {
            "i32_ordering_compares": {"minimum": 1},
            "dynamic_i32_stores": {"minimum": 1},
        }
    elif profile == "merge_u32":
        requirements = {
            "dynamic_load_to_load_unsigned_ordering_compares": {"minimum": 1},
            "dynamic_i32_stores": {"minimum": 1},
        }
    elif profile == "linear_probe_u32":
        common_counts.update(
            {
                "occupancy_eq_zero_compares": count(
                    rf"^\s*{ssa}\s*=\s*icmp eq i32 (?:{ssa}, 0|0, {ssa})"
                ),
                "key_eq_9_compares": count(
                    rf"^\s*{ssa}\s*=\s*icmp eq i32 (?:{ssa}, 9|9, {ssa})"
                ),
                "key_eq_17_compares": count(
                    rf"^\s*{ssa}\s*=\s*icmp eq i32 (?:{ssa}, 17|17, {ssa})"
                ),
                "key_eq_25_compares": count(
                    rf"^\s*{ssa}\s*=\s*icmp eq i32 (?:{ssa}, 25|25, {ssa})"
                ),
            }
        )
        requirements = {
            "dynamic_i32_loads": {"minimum": 8},
            "occupancy_eq_zero_compares": {"minimum": 4},
            "key_eq_9_compares": {"minimum": 1},
            "key_eq_17_compares": {"minimum": 1},
            "key_eq_25_compares": {"minimum": 1},
            "stores_through_dynamic_index_gep": {"minimum": 1},
        }
    else:
        raise HarnessError(f"unknown optimized-IR shape profile {profile!r}")
    checks = {
        name: common_counts[name] >= requirement["minimum"]
        for name, requirement in requirements.items()
    }
    return {
        "profile": profile,
        "purpose": "anti_trivialization_only_not_semantic_equivalence",
        "counts": common_counts,
        "requirements": requirements,
        "checks": checks,
        "passed": all(checks.values()),
    }


def absolute_repo_path(relative: str, *, require_file: bool = True) -> Path:
    candidate = (ROOT / relative).resolve()
    try:
        candidate.relative_to(ROOT)
    except ValueError as error:
        raise HarnessError(f"path escapes repository: {relative!r}") from error
    if require_file and not candidate.is_file():
        raise HarnessError(f"required file does not exist: {relative}")
    if not require_file and not candidate.is_dir():
        raise HarnessError(f"required directory does not exist: {relative}")
    return candidate


def main() -> int:
    args = parse_args()
    try:
        if not args.machine_label.strip():
            raise HarnessError("--machine-label must not be empty")
        manifest_path = args.manifest.resolve()
        closure_path = args.closure.resolve()
        manifest = load_object(manifest_path)
        closure = load_object(closure_path)
        workloads = validate_manifest(manifest, closure, args.only)
        clang = shutil.which(args.clang)
        if clang is None:
            raise HarnessError(f"cannot find clang executable {args.clang!r}")
        start_git_status = command(
            ["git", "status", "--porcelain=v1"], args.timeout_seconds, check=True
        )
        start_dirty = bool(start_git_status.stdout.strip())
        if start_dirty and not args.allow_dirty:
            raise HarnessError(
                "worktree is dirty; commit changes or pass --allow-dirty for a "
                "non-baseline smoke run"
            )
        start_revision = first_line(["git", "rev-parse", "HEAD"], args.timeout_seconds)
        audited_base = closure["audited_base_revision"]
        audited_commit = command(
            ["git", "cat-file", "-e", f"{audited_base}^{{commit}}"],
            args.timeout_seconds,
        )
        if audited_commit.returncode != 0:
            raise HarnessError(
                f"closure audited_base_revision is not a local commit: {audited_base}"
            )
        audited_ancestor = command(
            ["git", "merge-base", "--is-ancestor", audited_base, start_revision],
            args.timeout_seconds,
        )
        if audited_ancestor.returncode != 0:
            if audited_ancestor.returncode == 1:
                raise HarnessError(
                    "closure audited_base_revision is not an ancestor of the run revision"
                )
            raise HarnessError("git could not compare the audited base and run revisions")

        runtime = absolute_repo_path(manifest["hosted_runtime"])
        runtime_hash = sha256(runtime)
        if runtime_hash != closure["hosted_runtime_sha256"]:
            raise HarnessError(
                "hosted runtime hash differs from closure.json; audit the runtime boundary "
                "before refreshing the closure"
            )
        default_manifest = manifest_path == DEFAULT_MANIFEST.resolve()
        default_closure = closure_path == DEFAULT_CLOSURE.resolve()
        evidence_reasons: list[str] = []
        if not default_manifest:
            evidence_reasons.append("custom_manifest")
        if not default_closure:
            evidence_reasons.append("custom_closure")
        if start_dirty:
            evidence_reasons.append("dirty_start")
        if args.compiler is not None:
            evidence_reasons.append("explicit_compiler")
        if args.warmups != 3 or args.samples != 15:
            evidence_reasons.append("nondefault_timing_protocol")
        if args.only:
            evidence_reasons.append("workload_subset")
        if args.output is not None:
            try:
                args.output.resolve().relative_to(ROOT)
            except ValueError:
                pass
            else:
                evidence_reasons.append("output_path_inside_worktree")

        compiler_build_elapsed_ns: int | None = None
        if args.compiler is None:
            compiler = ROOT / "compiler" / "target" / "release" / "sable"
            compiler_build_start = time.perf_counter_ns()
            command(
                [
                    "cargo",
                    "build",
                    "--release",
                    "--locked",
                    "--manifest-path",
                    str(ROOT / "compiler" / "Cargo.toml"),
                ],
                args.timeout_seconds,
                check=True,
            )
            compiler_build_elapsed_ns = time.perf_counter_ns() - compiler_build_start
            compiler_origin = (
                "release build from recorded dirty checkout (smoke only)"
                if start_dirty
                else "release build from recorded clean checkout"
            )
        else:
            compiler = args.compiler.resolve()
            compiler_origin = "explicit --compiler (smoke/custom; binary hash recorded)"
        if not compiler.is_file() or not os.access(compiler, os.X_OK):
            raise HarnessError(f"compiler is not executable after preparation: {compiler}")
        compiler_hash = sha256(compiler)
        module_paths = manifest["module_paths"]
        closure_records = closure["workloads"]
        manifest_hash = sha256(manifest_path)
        closure_hash = sha256(closure_path)

        authenticated_inputs: dict[str, tuple[Path, str]] = {
            "manifest": (manifest_path, manifest_hash),
            "closure": (closure_path, closure_hash),
            "hosted_runtime": (runtime, runtime_hash),
            "compiler_binary": (compiler, compiler_hash),
        }

        report: dict[str, Any] = {
            "schema_version": SCHEMA_VERSION,
            "status": "ok",
            "generated_unix_ns": time.time_ns(),
            "evidence_tier": None,
            "evidence_reasons": evidence_reasons,
            "provenance": {
                "manifest": {
                    "path": str(manifest_path),
                    "sha256": manifest_hash,
                    "default": default_manifest,
                },
                "closure": {
                    "path": str(closure_path),
                    "sha256": closure_hash,
                    "default": default_closure,
                },
                "hosted_runtime": {
                    "path": str(runtime),
                    "sha256": runtime_hash,
                    "default": manifest["hosted_runtime"]
                    == "runtime/hosted/sable_rt_v1.c",
                },
                "start_revision": start_revision,
                "start_dirty": start_dirty,
                "end_revision": None,
                "end_dirty": None,
                "audited_closure": {
                    "audited_base_revision": audited_base,
                    "audited_base_is_ancestor": True,
                    "audited_date": closure["audited_date"],
                    "native_optimization": closure["native_optimization"],
                    "hosted_runtime_sha256": closure["hosted_runtime_sha256"],
                },
            },
            "machine": {
                "label": args.machine_label,
                "hostname": socket.gethostname(),
                "platform": platform.platform(),
                "machine": platform.machine(),
                "processor": platform.processor(),
                "python": platform.python_version(),
            },
            "toolchain": {
                "compiler_path": str(compiler),
                "compiler_sha256": compiler_hash,
                "compiler_origin": compiler_origin,
                "compiler_build_elapsed_ns": compiler_build_elapsed_ns,
                "rustc": first_line(["rustc", "--version"], args.timeout_seconds),
                "clang_path": clang,
                "clang": first_line([clang, "--version"], args.timeout_seconds),
                "optimization": OPTIMIZATION,
            },
            "protocol": {
                "warmups": args.warmups,
                "samples": args.samples,
                "clock": "time.perf_counter_ns",
                "process_model": "one process per sample; each process performs manifest work_units",
                "order": "alternating C/Sable first for admitted pairs",
                "anti_trivialization_gate": (
                    "named optimized-LLVM structural profiles; rejects known constant "
                    "collapse but does not prove semantic equivalence"
                ),
            },
            "workloads": [],
            "errors": [],
        }

        with tempfile.TemporaryDirectory(prefix="sable-native-perf-") as temporary:
            temp = Path(temporary)
            for index, workload in enumerate(workloads):
                workload_id = workload["id"]
                expected = closure_records[workload_id]
                if not isinstance(expected, dict) or expected.get("expected_status") not in {
                    "admitted",
                    "blocked",
                }:
                    raise HarnessError(f"invalid closure status for {workload_id}")
                sable_source = absolute_repo_path(workload["sable_source"])
                verified_subject = absolute_repo_path(workload["verified_subject"])
                c_source = absolute_repo_path(workload["c_source"])
                for role, path in (
                    ("verified_subject", verified_subject),
                    ("sable", sable_source),
                    ("c", c_source),
                ):
                    authenticated_inputs[f"{workload_id}:{role}"] = (path, sha256(path))
                sable_text = sable_source.read_text(encoding="utf-8")
                c_text = c_source.read_text(encoding="utf-8")
                work_units_marker = f"while (iteration < {workload['work_units']})"
                if sable_text.count(work_units_marker) != 1:
                    raise HarnessError(
                        f"{workload_id}: Sable source must contain exactly one authenticated "
                        f"work-unit marker {work_units_marker!r}"
                    )
                if c_text.count("#ifndef WORK_UNITS") != 1:
                    raise HarnessError(
                        f"{workload_id}: C source must require runner-injected WORK_UNITS"
                    )
                actual_hashes = {
                    "verified_subject": sha256(verified_subject),
                    "sable": sha256(sable_source),
                    "c": sha256(c_source),
                }
                if expected.get("source_sha256") != actual_hashes:
                    raise HarnessError(
                        f"{workload_id}: source hashes differ from closure.json; audit the "
                        "semantic pair and refresh its authenticated hashes"
                    )
                item: dict[str, Any] = {
                    "id": workload_id,
                    "verified_subject": workload["verified_subject"],
                    "sable_source": workload["sable_source"],
                    "c_source": workload["c_source"],
                    "entry": workload["entry"],
                    "work_units": workload["work_units"],
                    "expected_exit": workload["expected_exit"],
                    "semantic_profile": workload["semantic_profile"],
                    "scope_nonclaim": workload.get("scope_nonclaim"),
                    "source_sha256": actual_hashes,
                }
                if expected["expected_status"] == "admitted":
                    item.update(
                        {
                            "closure_scope": expected["scope"],
                            "comparison_eligibility": expected[
                                "comparison_eligibility"
                            ],
                            "optimized_ir_shape_profile": expected[
                                "optimized_ir_shape_profile"
                            ],
                        }
                    )
                llvm_path = temp / f"{workload_id}.ll"
                build_args = [str(compiler), "build", "--emit-llvm", "--entry", workload["entry"]]
                for module_path in module_paths:
                    build_args.extend(
                        ["-M", str(absolute_repo_path(module_path, require_file=False))]
                    )
                build_args.extend(["-o", str(llvm_path), str(sable_source)])
                build_start = time.perf_counter_ns()
                build = command(build_args, args.timeout_seconds)
                item["native_gate_elapsed_ns"] = time.perf_counter_ns() - build_start
                build_text = (build.stdout + "\n" + build.stderr).strip()

                expected_status = expected["expected_status"]
                emitted = build.returncode == 0
                native_ready = False
                if emitted:
                    item["verification"] = parse_verification_summary(build_text)
                if emitted and expected_status == "blocked":
                    item["native_admission"] = "unexpected_admission"
                    item["comparison_status"] = "admission_mismatch"
                    report["errors"].append(
                        f"{workload_id}: native gate now admits a closure recorded as blocked; "
                        "audit and update closure.json"
                    )
                elif not emitted and expected_status == "admitted":
                    item["native_admission"] = "unexpected_refusal"
                    item["comparison_status"] = "admission_mismatch"
                    item["refusal"] = build_text[-6000:]
                    report["errors"].append(
                        f"{workload_id}: native gate refused a workload recorded as admitted"
                    )
                elif not emitted:
                    refusal_auth = authenticate_blocked_refusal(
                        build, build_text, expected, sable_source
                    )
                    if not refusal_auth["passed"]:
                        item["native_admission"] = "refusal_mismatch"
                        item["comparison_status"] = "admission_mismatch"
                        report["errors"].append(
                            f"{workload_id}: native refusal does not match authenticated closure"
                        )
                    else:
                        item["native_admission"] = "blocked_expected"
                        item["comparison_status"] = "c_reference_only_native_blocked"
                    item["refusal"] = {
                        "title_fragment": expected["title_fragment"],
                        "detail_fragment": expected["detail_fragment"],
                        "closure": expected.get("closure"),
                        "authentication": refusal_auth,
                    }
                else:
                    verification = item["verification"]
                    if verification["accepted_for_comparison"]:
                        item["native_admission"] = "admitted_expected"
                        native_ready = True
                    else:
                        item["native_admission"] = "verification_incomplete"
                        item["comparison_status"] = "verification_incomplete"
                        report["errors"].append(
                            f"{workload_id}: emitted LLVM lacks an authenticated zero-escape "
                            "fully-verified summary"
                        )

                c_executable = temp / f"{workload_id}-c"
                c_compile = command(
                    [
                        clang,
                        OPTIMIZATION,
                        "-std=c11",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        f"-DWORK_UNITS={workload['work_units']}",
                        str(c_source),
                        str(runtime),
                        "-o",
                        str(c_executable),
                    ],
                    args.timeout_seconds,
                )
                if c_compile.returncode != 0:
                    item["c_compile_error"] = (c_compile.stdout + c_compile.stderr)[-6000:]
                    item["comparison_status"] = "c_compile_failed"
                    report["errors"].append(f"{workload_id}: C -O2 compilation failed")
                    report["workloads"].append(item)
                    continue

                expected_exit = workload["expected_exit"]
                if not native_ready:
                    if item.get("comparison_status") == "c_reference_only_native_blocked":
                        try:
                            timed_run(c_executable, expected_exit, args.timeout_seconds)
                        except HarnessError as error:
                            item["semantic_probe_error"] = str(error)
                            item["comparison_status"] = "semantic_probe_failed"
                            report["errors"].append(
                                f"{workload_id}: C reference semantic probe failed"
                            )
                    report["workloads"].append(item)
                    continue

                sable_opt_ir = temp / f"{workload_id}-sable-o2.ll"
                c_opt_ir = temp / f"{workload_id}-c-o2.ll"
                sable_opt_compile = command(
                    [
                        clang,
                        OPTIMIZATION,
                        "-S",
                        "-emit-llvm",
                        "-x",
                        "ir",
                        str(llvm_path),
                        "-o",
                        str(sable_opt_ir),
                    ],
                    args.timeout_seconds,
                )
                c_opt_compile = command(
                    [
                        clang,
                        OPTIMIZATION,
                        "-std=c11",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        "-S",
                        "-emit-llvm",
                        f"-DWORK_UNITS={workload['work_units']}",
                        str(c_source),
                        "-o",
                        str(c_opt_ir),
                    ],
                    args.timeout_seconds,
                )
                if sable_opt_compile.returncode != 0 or c_opt_compile.returncode != 0:
                    item["optimized_ir_compile_error"] = {
                        "sable": (sable_opt_compile.stdout + sable_opt_compile.stderr)[-6000:],
                        "c": (c_opt_compile.stdout + c_opt_compile.stderr)[-6000:],
                    }
                    item["comparison_status"] = "anti_trivialization_ir_compile_failed"
                    report["errors"].append(
                        f"{workload_id}: could not produce both optimized LLVM shape artifacts"
                    )
                    report["workloads"].append(item)
                    continue
                shape_profile = expected["optimized_ir_shape_profile"]
                sable_shape = optimized_ir_shape(
                    shape_profile, sable_opt_ir.read_text(encoding="utf-8")
                )
                c_shape = optimized_ir_shape(
                    shape_profile, c_opt_ir.read_text(encoding="utf-8")
                )
                item["optimized_ir_authentication"] = {
                    "sable": {
                        **sable_shape,
                        "sha256": sha256(sable_opt_ir),
                    },
                    "c": {**c_shape, "sha256": sha256(c_opt_ir)},
                }
                eligibility = expected["comparison_eligibility"]
                if eligibility == "comparable" and not (
                    sable_shape["passed"] and c_shape["passed"]
                ):
                    item["comparison_status"] = "anti_trivialization_failed"
                    report["errors"].append(
                        f"{workload_id}: optimized LLVM failed its named "
                        "anti-trivialization profile"
                    )
                    report["workloads"].append(item)
                    continue
                if eligibility == "optimization_trivialized" and (
                    sable_shape["passed"] or c_shape["passed"]
                ):
                    item["comparison_status"] = (
                        "anti_trivialization_classification_mismatch"
                    )
                    report["errors"].append(
                        f"{workload_id}: optimized shape no longer matches the recorded "
                        "both-sides trivialization closure; re-audit eligibility"
                    )
                    report["workloads"].append(item)
                    continue

                sable_executable = temp / f"{workload_id}-sable"
                native_compile = command(
                    [
                        clang,
                        OPTIMIZATION,
                        "-x",
                        "ir",
                        str(llvm_path),
                        "-x",
                        "c",
                        str(runtime),
                        "-o",
                        str(sable_executable),
                    ],
                    args.timeout_seconds,
                )
                if native_compile.returncode != 0:
                    item["sable_native_compile_error"] = (
                        native_compile.stdout + native_compile.stderr
                    )[-6000:]
                    item["comparison_status"] = "native_link_failed"
                    report["errors"].append(
                        f"{workload_id}: clang -O2 rejected emitted LLVM/runtime"
                    )
                    report["workloads"].append(item)
                    continue

                try:
                    timed_run(c_executable, expected_exit, args.timeout_seconds)
                    timed_run(sable_executable, expected_exit, args.timeout_seconds)
                except HarnessError as error:
                    item["semantic_probe_error"] = str(error)
                    item["comparison_status"] = "semantic_probe_failed"
                    report["errors"].append(f"{workload_id}: semantic probe failed")
                    report["workloads"].append(item)
                    continue

                if eligibility == "optimization_trivialized":
                    item["comparison_status"] = (
                        "admitted_noncomparable_optimization_trivialized"
                    )
                    item["noncomparable_reason"] = expected["noncomparable_reason"]
                    report["workloads"].append(item)
                    continue

                c_samples: list[int] = []
                sable_samples: list[int] = []
                try:
                    for warmup in range(args.warmups):
                        pair = (
                            [c_executable, sable_executable]
                            if warmup % 2 == 0
                            else [sable_executable, c_executable]
                        )
                        for executable in pair:
                            timed_run(executable, expected_exit, args.timeout_seconds)
                    for sample in range(args.samples):
                        pair = (
                            [c_executable, sable_executable]
                            if (sample + index) % 2 == 0
                            else [sable_executable, c_executable]
                        )
                        for executable in pair:
                            elapsed = timed_run(executable, expected_exit, args.timeout_seconds)
                            if executable == c_executable:
                                c_samples.append(elapsed)
                            else:
                                sable_samples.append(elapsed)
                except HarnessError as error:
                    item["timing_error"] = str(error)
                    item["comparison_status"] = "timed_execution_failed"
                    report["errors"].append(f"{workload_id}: timed execution failed")
                    report["workloads"].append(item)
                    continue

                item["c_o2"] = timing_summary(c_samples, workload["work_units"])
                item["sable_o2"] = timing_summary(sable_samples, workload["work_units"])
                item["sable_over_c_median_ratio"] = (
                    item["sable_o2"]["median_ns"] / item["c_o2"]["median_ns"]
                )
                item["comparison_status"] = "comparable_admitted_pair"
                report["workloads"].append(item)

        end_revision = first_line(["git", "rev-parse", "HEAD"], args.timeout_seconds)
        end_git_status = command(
            ["git", "status", "--porcelain=v1"], args.timeout_seconds, check=True
        )
        end_dirty = bool(end_git_status.stdout.strip())
        report["provenance"]["end_revision"] = end_revision
        report["provenance"]["end_dirty"] = end_dirty
        if end_revision != start_revision:
            report["errors"].append("checkout HEAD changed during the run")
            evidence_reasons.append("revision_changed_during_run")
        if end_dirty != start_dirty:
            report["errors"].append("checkout dirty state changed during the run")
            evidence_reasons.append("dirty_state_changed_during_run")
        if end_dirty and "dirty_start" not in evidence_reasons:
            evidence_reasons.append("dirty_end")

        input_stability: list[dict[str, Any]] = []
        for label, (path, start_hash) in sorted(authenticated_inputs.items()):
            end_hash = sha256(path)
            stable = start_hash == end_hash
            input_stability.append(
                {
                    "label": label,
                    "path": str(path),
                    "start_sha256": start_hash,
                    "end_sha256": end_hash,
                    "stable": stable,
                }
            )
            if not stable:
                report["errors"].append(f"authenticated input changed during run: {label}")
                evidence_reasons.append("authenticated_input_changed_during_run")
        report["provenance"]["input_stability"] = input_stability
        report["evidence_reasons"] = list(dict.fromkeys(evidence_reasons))
        report["evidence_tier"] = (
            "baseline" if not report["evidence_reasons"] else "smoke_custom"
        )
        if report["errors"]:
            report["status"] = "failed"
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output:
            output = args.output.resolve()
            try:
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text(rendered, encoding="utf-8")
            except OSError as error:
                raise HarnessError(f"cannot write report {output}: {error}") from error
        sys.stdout.write(rendered)
        return 0 if report["status"] == "ok" else 1
    except HarnessError as error:
        print(f"native-perf harness error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

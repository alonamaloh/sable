#!/usr/bin/env python3
"""Find corpus discharge scripts the automation portfolio no longer needs.

A `discharge` block is written the day automation fails and is never
revisited, so the portfolio's improvements strand proofs-by-hand that
`sable_auto` now closes on its own. This audit measures the drift: in a
throwaway git worktree it strips every discharge from `corpus/verifies`,
checks each file, and restores exactly the discharges whose obligations
genuinely fail. What stays deleted is stale, reported per file for a
human to remove (and re-run the corpus) afterwards.

Method, per file (in `use`-dependency order, so an importer is never
measured against a broken import):

  1. check with `SABLE_GRIND_HEARTBEATS=2000` — an obligation that
     passes this cheap can never trip the expensive-automation warning,
     and its discharge is redundant with 25x headroom to spare;
  2. restore the discharges of everything that failed, verify at the
     default budget, and require a clean, warning-free pass — anything
     else is restored too.

Only the cheap pass may declare a discharge stale. An obligation that
grind closes only near the budget is not reliably closable at all: the
search is pointer-order sensitive, and the same goal has been observed
to flip between passing at 2000 and exceeding the full 50000 across
runs. Deleting such a discharge makes the corpus flaky.

Usage: discharge-audit.py <sable-binary> [-j N] [--json FILE]
Read-only with respect to the checkout; needs a clean-enough repo for
`git worktree add` of HEAD, and measures HEAD, not the working tree.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

CLAUSE_KEYWORDS = {
    "pre", "post", "invariant", "variant", "assert", "defer", "assume",
    "def", "spec", "requires", "theorem", "discharge", "use", "lemma",
}


def repo_root():
    return os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


def discharge_blocks(lines):
    """(name, start, end) line ranges of discharge blocks, extended to a
    preceding blank line when removal would leave a double blank."""
    blocks = []
    i = 0
    while i < len(lines):
        m = re.match(r"\s*///\s*discharge\s+(\S+)\s+by\b", lines[i])
        if not m:
            i += 1
            continue
        j = i + 1
        while j < len(lines):
            c = re.match(r"\s*///(.*)", lines[j])
            if not c:
                break
            first = c.group(1).split() or [""]
            if first[0] in CLAUSE_KEYWORDS:
                break
            j += 1
        blocks.append((m.group(1), i, j))
        i = j
    return blocks


class Audit:
    def __init__(self, binary, worktree, jobs):
        self.binary = os.path.abspath(binary)
        self.worktree = worktree
        self.verifies = os.path.join(worktree, "corpus", "verifies")
        self.jobs = jobs
        self.stripped = {}  # file -> {name: block text}

    def strip_all(self):
        for fn in sorted(os.listdir(self.verifies)):
            if not fn.endswith(".sable"):
                continue
            path = os.path.join(self.verifies, fn)
            with open(path) as f:
                lines = f.readlines()
            blocks = discharge_blocks(lines)
            if not blocks:
                continue
            keep = [True] * len(lines)
            removed = {}
            for name, s, e in blocks:
                removed[name] = "".join(lines[s:e])
                for k in range(s, e):
                    keep[k] = False
                if s > 0 and lines[s - 1].strip() == "" and (
                    e >= len(lines) or lines[e].strip() == ""
                ):
                    keep[s - 1] = False
            with open(path, "w") as f:
                f.writelines(l for k, l in zip(keep, lines) if k)
            self.stripped[fn] = removed

    def restore(self, fn, names):
        with open(os.path.join(self.verifies, fn), "a") as f:
            for n in names:
                f.write("\n" + self.stripped[fn][n])

    def check(self, fn, budget):
        env = dict(os.environ)
        env.pop("SABLE_GRIND_HEARTBEATS", None)
        if budget is not None:
            env["SABLE_GRIND_HEARTBEATS"] = str(budget)
        p = subprocess.run(
            [self.binary, "check", os.path.join("corpus", "verifies", fn)],
            cwd=self.worktree, env=env, capture_output=True, text=True,
            timeout=3600,
        )
        raw = p.stdout + p.stderr
        failing = set(re.findall(r"unproved obligation `([^`]+)`", raw))
        failing |= set(re.findall(r"discharge of `([^`]+)` does not prove it", raw))
        warned = bool(re.search(r"expensive automation", raw))
        return p.returncode == 0, sorted(failing), warned, raw

    def audit_file(self, fn):
        t0 = time.time()
        names = list(self.stripped.get(fn, {}))
        result = {"file": fn, "total": len(names)}
        ok, s1, _, _ = self.check(fn, 2000)
        if ok:
            result.update(stale=names, kept=[], seconds=round(time.time() - t0, 1))
            return result
        foreign = [n for n in s1 if n not in names]
        if foreign:
            result["foreign"] = foreign
        kept = [n for n in names if n in s1]
        self.restore(fn, kept)
        for _ in range(4):
            ok3, s3, warned, _ = self.check(fn, None)
            if ok3 and not warned:
                break
            extra = [n for n in names if n in s3 and n not in kept]
            if not extra and not warned:
                result["unresolved"] = s3
                break
            if not extra:
                # warned but nothing nameable failed: restore the remainder
                extra = [n for n in names if n not in kept]
                if not extra:
                    result["unresolved"] = ["expensive-automation warning"]
                    break
            self.restore(fn, extra)
            kept += extra
        result.update(stale=[n for n in names if n not in kept], kept=kept,
                      seconds=round(time.time() - t0, 1))
        return result

    def run(self):
        files = sorted(self.stripped)
        fileset = set(files)
        deps = {}
        for fn in files:
            with open(os.path.join(self.verifies, fn)) as f:
                text = f.read()
            deps[fn] = {
                u + ".sable"
                for u in re.findall(r"^use\s+(\w+)", text, re.M)
                if u + ".sable" in fileset
            }
        done, results = set(), []
        lock = threading.Lock()

        def work(fn):
            r = self.audit_file(fn)
            with lock:
                done.add(fn)
                results.append(r)
                tag = " FOREIGN" if r.get("foreign") else ""
                tag += " UNRESOLVED" if r.get("unresolved") else ""
                print(f"{r['file']}: {len(r['stale'])}/{r['total']} stale"
                      f" [{r['seconds']}s]{tag}", flush=True)

        pending = set(files)
        futures = {}
        with ThreadPoolExecutor(max_workers=self.jobs) as ex:
            while pending or futures:
                with lock:
                    ready = [f for f in sorted(pending) if deps[f] <= done]
                for f in ready:
                    pending.discard(f)
                    futures[f] = ex.submit(work, f)
                for f in [f for f, fu in futures.items() if fu.done()]:
                    futures.pop(f).result()
                if not ready:
                    time.sleep(1)
        return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("binary", help="path to the sable binary")
    ap.add_argument("-j", "--jobs", type=int, default=6)
    ap.add_argument("--json", help="also write full results to this file")
    args = ap.parse_args()

    root = repo_root()
    with tempfile.TemporaryDirectory(prefix="discharge-audit-") as tmp:
        wt = os.path.join(tmp, "wt")
        subprocess.run(["git", "-C", root, "worktree", "add", "--detach", wt],
                       check=True, capture_output=True)
        try:
            audit = Audit(args.binary, wt, args.jobs)
            audit.strip_all()
            total = sum(len(v) for v in audit.stripped.values())
            print(f"stripped {total} discharges from "
                  f"{len(audit.stripped)} files; measuring…", flush=True)
            results = audit.run()
        finally:
            subprocess.run(["git", "-C", root, "worktree", "remove", "--force", wt],
                           capture_output=True)

    stale = [(r["file"], n) for r in results for n in r["stale"]]
    print(f"\n{len(stale)}/{total} discharges are stale:")
    for fn, name in stale:
        print(f"  {fn}: {name}")
    for r in results:
        if r.get("foreign"):
            print(f"note: {r['file']}: an import re-verified over budget at the "
                  f"cheap pass ({r['foreign'][:2]}…); own verdict unaffected")
        if r.get("unresolved"):
            print(f"note: {r['file']} did not settle: {r['unresolved']}")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()

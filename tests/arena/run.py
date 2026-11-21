#!/usr/bin/env python3
"""Run the Lean Kernel Arena test suite against Certus.

The Lean Kernel Arena (https://arena.lean-lang.org,
https://github.com/leanprover/lean-kernel-arena) is a community suite of
lean4export files that an independent Lean checker must accept (`good/`) or
reject (`bad/`). This script downloads a suite into a cache directory outside
the repository, runs `certus check` on every test and compares verdicts.

Suites:
  round-2026-09  the closed round 2026-09, pinned by SHA-256 (default; used by CI)
  live           whatever arena.lean-lang.org serves right now (not pinned)

The suite tarballs leave out the large real-world corpora (init, std, mathlib,
...) and the `either` corner cases, whose outcome is debatable and which the
Arena does not score; both are listed as skipped.

Exit status: 1 if any test that must be rejected was accepted (a false
acceptance, i.e. a soundness bug), else 0. False rejections, crashes and
timeouts are reported but only fail the run with --strict.

A false acceptance that already has a `soundness` issue can be listed in
known-unsound.txt next to this script, so that CI stays useful for catching
new ones. It is still reported in every run. Once Certus rejects that test the
run fails until the entry is removed, so a fix cannot silently regress.

Uses only the Python standard library.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
import time
import urllib.request
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

SUITES = {
    "round-2026-09": {
        "tests": "https://github.com/leanprover/lean-kernel-arena/releases/download/round-2026-09/lean-arena-round-2026-09-tests.tar.gz",
        "tests_sha256": "98a69742b538296c5f413d0527dfeef8c4d1815fe64b12c8623cd33de63bee0d",
        "results": "https://github.com/leanprover/lean-kernel-arena/releases/download/round-2026-09/lean-arena-round-2026-09-results.json",
        "results_sha256": "c48cab650e1bcfbb4231221d0b68820880a077ac67b37e435bf1a4aa9caff9f7",
    },
    "live": {
        "tests": "https://arena.lean-lang.org/lean-arena-tests.tar.gz",
        "tests_sha256": None,
        "results": "https://arena.lean-lang.org/results.json",
        "results_sha256": None,
    },
}

EXPECT_OF_DIR = {"good": "accept", "bad": "reject"}
KNOWN_UNSOUND = Path(__file__).with_name("known-unsound.txt")
UNSUPPORTED = "not supported yet"


def known_unsound() -> dict[str, str]:
    """Test name -> issue, from lines `<test name> <issue>`; lines starting with # are comments."""
    known = {}
    for line in KNOWN_UNSOUND.read_text().splitlines() if KNOWN_UNSOUND.exists() else []:
        if line.strip() and not line.lstrip().startswith("#"):
            name, _, issue = line.strip().partition(" ")
            known[name] = issue.strip()
    return known


def default_cache() -> Path:
    if os.environ.get("CERTUS_ARENA_CACHE"):
        return Path(os.environ["CERTUS_ARENA_CACHE"])
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(Path.home(), ".cache")
    return Path(base) / "certus-arena"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def fetch(url: str, dest: Path, want_sha: str | None, refresh: bool) -> None:
    if dest.exists() and not refresh and (want_sha is None or sha256(dest) == want_sha):
        return
    print(f"downloading {url}", file=sys.stderr)
    tmp = dest.with_suffix(dest.suffix + ".part")
    req = urllib.request.Request(url, headers={"User-Agent": "certus-arena-harness"})
    with urllib.request.urlopen(req, timeout=120) as r, open(tmp, "wb") as f:
        shutil.copyfileobj(r, f)
    if want_sha is not None and sha256(tmp) != want_sha:
        tmp.unlink()
        sys.exit(f"error: {url}: SHA-256 mismatch (expected {want_sha})")
    tmp.replace(dest)


def safe_extract(archive: Path, dest: Path) -> None:
    """Extract only regular files and directories that stay inside dest."""
    tmp = dest.with_name(dest.name + ".part")
    shutil.rmtree(tmp, ignore_errors=True)
    tmp.mkdir(parents=True)
    root = tmp.resolve()
    with tarfile.open(archive, "r:gz") as tar:
        for m in tar.getmembers():
            target = (root / m.name).resolve()
            if not (m.isfile() or m.isdir()) or os.path.isabs(m.name) or root not in target.parents:
                sys.exit(f"error: {archive}: refusing unsafe member {m.name!r}")
            if m.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            src = tar.extractfile(m)
            assert src is not None
            with src, open(target, "wb") as out:
                shutil.copyfileobj(src, out)
    shutil.rmtree(dest, ignore_errors=True)
    tmp.replace(dest)


def prepare(suite: str, cache: Path, refresh: bool) -> tuple[Path, dict]:
    spec = SUITES[suite]
    d = cache / suite
    d.mkdir(parents=True, exist_ok=True)
    archive, results = d / "tests.tar.gz", d / "results.json"
    stamp = d / "tests" / ".source-sha256"
    fetch(spec["tests"], archive, spec["tests_sha256"], refresh)
    fetch(spec["results"], results, spec["results_sha256"], refresh)
    digest = sha256(archive)
    if not stamp.exists() or stamp.read_text().strip() != digest:
        safe_extract(archive, d / "tests")
        stamp.write_text(digest + "\n")
    return d / "tests", json.loads(results.read_text())


def collect(tests_dir: Path, meta: dict) -> tuple[list[dict], list[dict]]:
    """Return (runnable tests, skipped tests) with expected verdicts."""
    by_name = {t["name"]: t for t in meta["tests"]}
    runnable, seen = [], set()
    for path in sorted(tests_dir.rglob("*.ndjson")):
        rel = path.relative_to(tests_dir)
        kind, name = rel.parts[0], str(rel.with_suffix("").relative_to(rel.parts[0]))
        if kind not in EXPECT_OF_DIR:
            sys.exit(f"error: unexpected test directory {kind!r} in {rel}")
        expected = EXPECT_OF_DIR[kind]
        outcome = by_name.get(name, {}).get("outcome")
        if outcome is not None and outcome != expected:
            sys.exit(f"error: {name}: in {kind}/ but results.json says {outcome!r}")
        runnable.append({"name": name, "path": path, "expected": expected})
        seen.add(name)
    skipped = []
    for t in meta["tests"]:
        if t["name"] in seen:
            continue
        why = "outcome 'either' (not scored)" if t["outcome"] == "either" else f"large corpus ({t['size_str']}), not in tarball"
        skipped.append({"name": t["name"], "expected": t["outcome"], "why": why})
    return runnable, skipped


def first_line(text: str, needle: str) -> str:
    for line in text.splitlines():
        if needle in line:
            return line.strip()
    lines = [l for l in text.splitlines() if l.strip()]
    return lines[-1].strip() if lines else ""


def run_one(certus: Path, test: dict, timeout: float) -> dict:
    t0 = time.monotonic()
    try:
        p = subprocess.run([str(certus), "check", str(test["path"])], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {**test, "verdict": "timeout", "reason": f"no verdict after {timeout:.0f} s", "secs": timeout}
    secs = time.monotonic() - t0
    out = p.stdout + p.stderr
    if p.returncode == 0 and "OK:" in p.stdout:
        verdict, reason = "accept", first_line(p.stdout, "OK:")
    elif p.returncode == 1 and "panicked" not in out:
        verdict, reason = "reject", first_line(p.stderr, "error:").removeprefix("error: ")
    else:
        verdict, reason = "error", f"exit {p.returncode}: {first_line(out, 'panicked')}"
    return {**test, "verdict": verdict, "reason": reason, "secs": secs}


def classify(r: dict, known: dict[str, str]) -> str:
    if r["verdict"] in ("timeout", "error"):
        return r["verdict"]
    if r["verdict"] == r["expected"]:
        return "correct-accept" if r["expected"] == "accept" else "correct-reject"
    if r["verdict"] == "accept":
        return "known-false-accept" if r["name"] in known else "FALSE-ACCEPT"
    return "false-reject"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--suite", choices=sorted(SUITES), default="round-2026-09")
    ap.add_argument("--certus", type=Path, default=REPO / "target" / "release" / "certus")
    ap.add_argument("--cache", type=Path, default=default_cache(), help="download cache (default: %(default)s)")
    ap.add_argument("--refresh", action="store_true", help="re-download unpinned suites")
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per test (default: %(default)s)")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("-k", "--filter", default="", help="only run tests whose name contains this")
    ap.add_argument("--json", type=Path, help="write per-test results here")
    ap.add_argument("--summary", type=Path, help="append a Markdown summary here (e.g. $GITHUB_STEP_SUMMARY)")
    ap.add_argument("--strict", action="store_true", help="also fail on false rejections, crashes and timeouts")
    args = ap.parse_args()

    if not args.certus.exists():
        sys.exit(f"error: {args.certus} not found; run `cargo build --release` first")
    tests_dir, meta = prepare(args.suite, args.cache, args.refresh)
    runnable, skipped = collect(tests_dir, meta)
    runnable = [t for t in runnable if args.filter in t["name"]]
    print(f"suite {args.suite}: {len(runnable)} tests to run, {len(skipped)} skipped", file=sys.stderr)

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda t: run_one(args.certus, t, args.timeout), runnable))
    known = known_unsound()
    for r in results:
        r["class"] = classify(r, known)
    ran = {r["name"]: r for r in results}
    stale = sorted(n for n in known if n in ran and ran[n]["class"] == "correct-reject")

    order = ["correct-accept", "correct-reject", "false-reject", "FALSE-ACCEPT", "known-false-accept", "error", "timeout"]
    counts = {c: sum(r["class"] == c for r in results) for c in order}
    for r in sorted(results, key=lambda r: (order.index(r["class"]), r["name"])):
        if r["class"] not in ("correct-accept", "correct-reject"):
            print(f"{r['class']:<18} {r['name']:<40} {r['reason']}")

    lines = [
        f"## Lean Kernel Arena ({args.suite})",
        "",
        f"{len(results)} tests run, {len(skipped)} skipped (large corpora and unscored `either` cases).",
        "",
        "| verdict | count |",
        "|---|---|",
        *(f"| {c} | {counts[c]} |" for c in order),
    ]
    bad = [r for r in results if r["class"] not in ("correct-accept", "correct-reject")]
    if bad:
        lines += ["", "| class | test | reason |", "|---|---|---|"]
        for r in sorted(bad, key=lambda r: (order.index(r["class"]), r["name"])):
            reason = r["reason"].replace("|", "/")
            if r["class"] == "known-false-accept":
                reason = f"**soundness bug {known[r['name']]}**: {reason}"
            lines.append(f"| {r['class']} | `{r['name']}` | {reason} |")
    hollow = sorted(r["name"] for r in results if r["class"] == "correct-reject" and UNSUPPORTED in r["reason"])
    if hollow:
        lines += ["", "Rejected only because a feature is unsupported (re-check once it lands): " + ", ".join(f"`{n}`" for n in hollow) + "."]
    if stale:
        lines += ["", "Now rejected, so remove from `tests/arena/known-unsound.txt`: " + ", ".join(f"`{n}`" for n in stale) + "."]
    report = "\n".join(lines) + "\n"
    print("\n" + report)
    if args.summary:
        with open(args.summary, "a") as f:
            f.write(report)
    if args.json:
        args.json.write_text(json.dumps({"suite": args.suite, "counts": counts, "results": [{k: (str(v) if k == "path" else v) for k, v in r.items()} for r in results], "skipped": skipped}, indent=1))

    if counts["known-false-accept"]:
        print(f"WARNING: {counts['known-false-accept']} known false acceptance(s), see known-unsound.txt", file=sys.stderr)
    if counts["FALSE-ACCEPT"]:
        print(f"FAIL: {counts['FALSE-ACCEPT']} new false acceptance(s): soundness bug", file=sys.stderr)
        return 1
    if stale:
        print(f"FAIL: now rejected, remove from known-unsound.txt: {', '.join(stale)}", file=sys.stderr)
        return 1
    if args.strict and len(bad):
        print(f"FAIL (--strict): {len(bad)} test(s) not handled correctly", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

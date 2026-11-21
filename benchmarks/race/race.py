#!/usr/bin/env python3
"""Proof-checker race: the same theorem, checked by Certus, Lean and others.

Usage:
    PATH=/path/to/lean-4.36/bin:$PATH python3 race.py [--runs 5]

Needs, on PATH: lean, leanexport, leanchecker, nanoda_bin, con-leche.
Needs: ../proof-bench (sources and Metamath build), and a release build of
certus (`cargo build --release` at the repo root).

Round 1: 2·(0+1+…+n) = n(n+1), one theorem.
Round 2: 1,000 copies of it, each with its own recursive definition.
Every checker except Lean-from-source reads the same certificate: the
theorems plus every declaration they depend on, back to the definitions of
Nat and Eq (made with `certus extract`).
"""

import argparse
import json
import os
import resource
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BENCH = os.path.join(ROOT, "benchmarks", "proof-bench")
LEAN_DIR = os.path.join(BENCH, "lean")
MM_DIR = os.path.join(BENCH, "metamath")
CERTUS = os.path.join(ROOT, "target", "release", "certus")


def sh(cmd, cwd=None, env=None, quiet=True):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"command failed: {' '.join(cmd)}\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    return r.stdout


def timed(cmd, cwd, env, runs, check):
    """Best wall time and its CPU time over `runs` runs. `check` validates output."""
    best = None
    for _ in range(runs):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        t0 = time.perf_counter()
        r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
        wall = time.perf_counter() - t0
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
        out = r.stdout + r.stderr
        if r.returncode != 0 or not check(out):
            sys.exit(f"{' '.join(cmd)} did not report success:\n{out[-2000:]}")
        if best is None or wall < best[0]:
            best = (wall, cpu)
    return best


def lean_env():
    lean = shutil.which("lean")
    if not lean:
        sys.exit("lean not on PATH")
    prefix = os.path.dirname(os.path.dirname(lean))
    env = dict(os.environ)
    env["LEAN_PATH"] = os.path.join(prefix, "lib", "lean") + ":olean"
    return env


def make_certificate(work, module, theorems, env):
    os.makedirs(os.path.join(LEAN_DIR, "olean"), exist_ok=True)
    sh(["lean", "-o", f"olean/{module}.olean", f"{module}.lean"], cwd=LEAN_DIR, env=env)
    export = os.path.join(work, f"{module}.ndjson")
    with open(export, "w") as f:
        subprocess.run(["leanexport", module], cwd=LEAN_DIR, env=env, stdout=f, check=True)
    cert = os.path.join(work, f"{module}.cert.ndjson")
    sh([CERTUS, "extract", export, cert, *theorems])
    os.remove(export)
    return cert


def nanoda_config(work, cert):
    cfg = os.path.join(work, os.path.basename(cert) + ".nanoda.json")
    with open(cfg, "w") as f:
        json.dump(
            {
                "export_file_path": cert,
                "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
                "unpermitted_axiom_hard_error": False,
                "nat_extension": True,
                "string_extension": True,
                "num_threads": os.cpu_count(),
                "print_success_message": True,
            },
            f,
        )
    return cfg


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--json", help="write raw results here")
    args = ap.parse_args()
    env = lean_env()
    work = tempfile.mkdtemp(prefix="certus-race-")
    results = {}

    # Round 1: one theorem.
    cert1 = make_certificate(work, "Sum", ["sum_formula_explicit"], env)
    # Round 2: 1,000 theorems (generated if needed).
    gen = os.path.join(LEAN_DIR, "Gen_explicit_1000.lean")
    if not os.path.exists(gen):
        with open(gen, "w") as f:
            f.write(sh([sys.executable, os.path.join(BENCH, "scripts", "gen_lean.py"), "1000", "explicit"]))
    cert2 = make_certificate(work, "Gen_explicit_1000", [f"t{i}" for i in range(1000)], env)

    ok_certus = lambda o: "OK:" in o
    ok_nanoda = lambda o: "no typechecker errors" in o
    ok_leche = lambda o: "accepted" in o
    ok_any = lambda o: True

    rounds = {
        "1 theorem": [
            ("Certus (certificate)", [CERTUS, "check", cert1], None, ok_certus),
            ("nanoda (certificate)", ["nanoda_bin", nanoda_config(work, cert1)], None, ok_nanoda),
            ("con-leche (certificate)", ["con-leche", cert1], None, ok_leche),
            ("Lean kernel replay, trusts imports (leanchecker)", ["leanchecker", "Sum"], LEAN_DIR, ok_any),
            ("Lean, build from source", ["lean", "Sum.lean"], LEAN_DIR, ok_any),
        ],
        "1,000 theorems": [
            ("Certus (certificate)", [CERTUS, "check", cert2], None, ok_certus),
            ("nanoda (certificate)", ["nanoda_bin", nanoda_config(work, cert2)], None, ok_nanoda),
            ("con-leche (certificate)", ["con-leche", cert2], None, ok_leche),
            ("Lean kernel replay, trusts imports (leanchecker)", ["leanchecker", "Gen_explicit_1000"], LEAN_DIR, ok_any),
            ("Lean, build from source", ["lean", "Gen_explicit_1000.lean"], LEAN_DIR, ok_any),
            ("Metamath: all of set.mm (48k theorems)",
             ["./metamath", "set scroll continuous", "read set.mm", "verify proof *", "exit"], MM_DIR,
             lambda o: "All proofs in the database were verified" in o),
        ],
    }
    sizes = {"1 theorem": os.path.getsize(cert1), "1,000 theorems": os.path.getsize(cert2)}

    for rnd, contestants in rounds.items():
        print(f"\n## Round: {rnd}  (certificate {sizes[rnd] / 1e3:.0f} KB)\n")
        print("| Checker | Best wall time | CPU time |")
        print("|---|---|---|")
        rows = []
        for name, cmd, cwd, check in contestants:
            runs = 2 if "from source" in name and "1,000" in rnd else args.runs
            wall, cpu = timed(cmd, cwd, env, runs, check)
            rows.append((name, wall, cpu))
            print(f"| {name} | {wall * 1e3:,.0f} ms | {cpu * 1e3:,.0f} ms |", flush=True)
        results[rnd] = rows
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"results": results, "certificate_bytes": sizes}, f, indent=2)
    shutil.rmtree(work)


if __name__ == "__main__":
    main()

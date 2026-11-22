#!/usr/bin/env python3
"""Proof-checker race: the same theorem, checked by Certus, Lean and others.

Usage:
    PATH=/path/to/lean-4.36/bin:$PATH python3 race.py [--runs 5] [--json out.json]
                                                      [--require all|tool,tool...]

Needs, on PATH: lean and leanexport (to make the certificates), and a release
build of certus (`cargo build --release` at the repo root).

Optional contestants, skipped with a note when missing (unless --require
names them): leanchecker, nanoda_bin, con-leche, and Metamath (an executable
and set.mm in ../proof-bench/metamath, see ../proof-bench/bench.sh).

Round 1: 2·(0+1+…+n) = n(n+1), one theorem.
Round 2: 1,000 copies of it, each with its own recursive definition.
Every checker except Lean-from-source reads the same certificate: the
theorems plus every declaration they depend on, back to the definitions of
Nat and Eq (made with `certus extract`).

Soundness: every contestant must accept the genuine inputs, and Certus must
reject each tampered version of the round-1 certificate. Any failure is
recorded, the JSON is still written, and the exit status is 1.
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
THM1 = "sum_formula_explicit"

# Tool names accepted by --require.
OPTIONAL_TOOLS = ["leanchecker", "nanoda", "con-leche", "metamath"]


def sh(cmd, cwd=None, env=None):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"command failed: {' '.join(cmd)}\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    return r.stdout


def run_once(cmd, cwd, env):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    wall = time.perf_counter() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return r.returncode, r.stdout + r.stderr, wall, cpu


def timed(cmd, cwd, env, runs, check):
    """Best wall time and its CPU time over `runs` runs, or the failing output."""
    best = None
    for _ in range(runs):
        code, out, wall, cpu = run_once(cmd, cwd, env)
        if code != 0 or not check(out):
            return None, out
        if best is None or wall < best[0]:
            best = (wall, cpu)
    return best, None


def lean_env():
    lean = shutil.which("lean")
    if not lean:
        sys.exit("lean not on PATH (needed to make the certificates)")
    if not shutil.which("leanexport"):
        sys.exit("leanexport not on PATH (needed to make the certificates)")
    if not os.access(CERTUS, os.X_OK):
        sys.exit(f"{CERTUS} not found: run `cargo build --release` at the repo root")
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


# ---------------------------------------------------------------------------
# Tampered certificates (the same seven as crates/certus-kernel/tests/soundness.rs)


class Cert:
    def __init__(self, path):
        with open(path) as f:
            self.lines = [json.loads(line) for line in f if line.strip()]
        self.names = {r["in"]: r for r in self.lines if "in" in r}

    def name(self, i):
        parts = []
        while i:
            r = self.names[i]
            if "str" in r:
                parts.append(r["str"]["str"])
                i = r["str"]["pre"]
            else:
                parts.append(str(r["num"]["i"]))
                i = r["num"]["pre"]
        return ".".join(reversed(parts))

    def find(self, kind, name):
        for k, r in enumerate(self.lines):
            d = r.get(kind)
            if d is not None:
                i = d["name"] if "name" in d else d["types"][0]["name"]
                if self.name(i) == name:
                    return k
        raise KeyError(f"{kind} {name}")

    def write(self, path):
        with open(path, "w") as f:
            for r in self.lines:
                f.write(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n")


def tampers():
    """(description, mutate) pairs; each mutates a fresh Cert of the round-1 certificate."""

    def other_proof(c):
        c.lines[c.find("thm", THM1)]["thm"]["value"] = c.lines[c.find("thm", "Nat.add_comm")]["thm"]["value"]

    def other_statement(c):
        c.lines[c.find("thm", THM1)]["thm"]["type"] = c.lines[c.find("thm", "Nat.mul_comm")]["thm"]["type"]

    def missing_nat(c):
        del c.lines[c.find("inductive", "Nat")]

    def forged_recursor(c):
        rules = c.lines[c.find("inductive", "Nat")]["inductive"]["recs"][0]["rules"]
        rules[0]["rhs"], rules[1]["rhs"] = rules[1]["rhs"], rules[0]["rhs"]

    def data_as_theorem(c):
        t, d = c.find("thm", THM1), c.find("def", "sumTo")
        c.lines[t]["thm"]["type"] = c.lines[d]["def"]["type"]
        c.lines[t]["thm"]["value"] = c.lines[d]["def"]["value"]

    def injected_field(c):
        c.lines[c.find("thm", THM1)]["thm"]["trustMe"] = True

    def partial_def(c):
        c.lines[c.find("def", "sumTo")]["def"]["safety"] = "partial"

    return [
        ("a proof of something else", other_proof),
        ("a changed statement", other_statement),
        ("a missing definition (Nat)", missing_nat),
        ("a forged recursor", forged_recursor),
        ("data posing as a theorem", data_as_theorem),
        ("an injected field", injected_field),
        ("a partial definition", partial_def),
    ]


def tamper_suite(work, cert):
    results = []
    for why, mutate in tampers():
        c = Cert(cert)
        mutate(c)
        path = os.path.join(work, "tampered.ndjson")
        c.write(path)
        code, out, _, _ = run_once([CERTUS, "check", path, THM1], None, None)
        rejected = code != 0
        last = out.strip().splitlines()[-1] if out.strip() else ""
        results.append({"tamper": why, "rejected": rejected, "message": last})
        print(f"| {why} | {'rejected' if rejected else '**ACCEPTED**'} | {last} |", flush=True)
    return results


# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--json", help="write raw results here")
    ap.add_argument(
        "--require",
        default="",
        help="fail instead of skipping when these optional tools are missing: "
        f"'all' or a comma list of {','.join(OPTIONAL_TOOLS)}",
    )
    args = ap.parse_args()
    required = set(OPTIONAL_TOOLS) if args.require == "all" else {t for t in args.require.split(",") if t}
    unknown = required - set(OPTIONAL_TOOLS)
    if unknown:
        sys.exit(f"--require: unknown tools {sorted(unknown)}")

    env = lean_env()
    work = tempfile.mkdtemp(prefix="certus-race-")
    failures = []

    # Round 1: one theorem.
    cert1 = make_certificate(work, "Sum", [THM1], env)
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
    ok_mm = lambda o: "All proofs in the database were verified" in o

    have = lambda exe: shutil.which(exe) is not None
    metamath_ok = os.access(os.path.join(MM_DIR, "metamath"), os.X_OK) and os.path.exists(
        os.path.join(MM_DIR, "set.mm")
    )
    # Optional tool -> (available?, why not).
    tools = {
        "leanchecker": (have("leanchecker"), "leanchecker not on PATH"),
        "nanoda": (have("nanoda_bin"), "nanoda_bin not on PATH"),
        "con-leche": (have("con-leche"), "con-leche not on PATH"),
        "metamath": (metamath_ok, f"no metamath + set.mm in {MM_DIR} (see proof-bench/bench.sh)"),
    }

    # (tool, name, cmd, cwd, check)
    rounds = {
        "1 theorem": [
            ("certus", "Certus (certificate)", [CERTUS, "check", cert1], None, ok_certus),
            ("nanoda", "nanoda (certificate)", ["nanoda_bin", nanoda_config(work, cert1)], None, ok_nanoda),
            ("con-leche", "con-leche (certificate)", ["con-leche", cert1], None, ok_leche),
            ("leanchecker", "Lean kernel replay, trusts imports (leanchecker)", ["leanchecker", "Sum"], LEAN_DIR,
             ok_any),
            ("lean", "Lean, build from source", ["lean", "Sum.lean"], LEAN_DIR, ok_any),
        ],
        "1,000 theorems": [
            ("certus", "Certus (certificate)", [CERTUS, "check", cert2], None, ok_certus),
            ("nanoda", "nanoda (certificate)", ["nanoda_bin", nanoda_config(work, cert2)], None, ok_nanoda),
            ("con-leche", "con-leche (certificate)", ["con-leche", cert2], None, ok_leche),
            ("leanchecker", "Lean kernel replay, trusts imports (leanchecker)", ["leanchecker", "Gen_explicit_1000"],
             LEAN_DIR, ok_any),
            ("lean", "Lean, build from source", ["lean", "Gen_explicit_1000.lean"], LEAN_DIR, ok_any),
            ("metamath", "Metamath: all of set.mm (48k theorems)",
             ["./metamath", "set scroll continuous", "read set.mm", "verify proof *", "exit"], MM_DIR, ok_mm),
        ],
    }
    sizes = {"1 theorem": os.path.getsize(cert1), "1,000 theorems": os.path.getsize(cert2)}

    skipped = {}
    for tool, (ok, why) in tools.items():
        if ok:
            continue
        if tool in required:
            failures.append(f"required tool missing: {tool} ({why})")
        skipped[tool] = why
        print(f"note: skipping {tool}: {why}", flush=True)

    results = {}
    for rnd, contestants in rounds.items():
        print(f"\n## Round: {rnd}  (certificate {sizes[rnd] / 1e3:.0f} KB)\n")
        print("| Checker | Best wall time | CPU time |")
        print("|---|---|---|")
        rows = []
        for tool, name, cmd, cwd, check in contestants:
            if tool in skipped:
                rows.append({"checker": name, "tool": tool, "skipped": skipped[tool]})
                print(f"| {name} | skipped | {skipped[tool]} |", flush=True)
                continue
            runs = min(args.runs, 2) if "from source" in name and "1,000" in rnd else args.runs
            best, out = timed(cmd, cwd, env, runs, check)
            if best is None:
                failures.append(f"{name} rejected the valid input in round '{rnd}'")
                rows.append({"checker": name, "tool": tool, "rejected": True, "output": out[-2000:]})
                print(f"| {name} | **REJECTED** | |", flush=True)
                print(out[-2000:], file=sys.stderr)
                continue
            wall, cpu = best
            rows.append({"checker": name, "tool": tool, "wall_ms": round(wall * 1e3, 1),
                         "cpu_ms": round(cpu * 1e3, 1), "runs": runs})
            print(f"| {name} | {wall * 1e3:,.0f} ms | {cpu * 1e3:,.0f} ms |", flush=True)
        results[rnd] = rows

    print("\n## Tampered certificates (Certus must reject every one)\n")
    print("| Tampered with | Certus | Message |")
    print("|---|---|---|")
    tampered = tamper_suite(work, cert1)
    for t in tampered:
        if not t["rejected"]:
            failures.append(f"Certus ACCEPTED a tampered certificate: {t['tamper']}")

    if args.json:
        with open(args.json, "w") as f:
            json.dump(
                {
                    "results": results,
                    "certificate_bytes": sizes,
                    "tampered": tampered,
                    "skipped": skipped,
                    "failures": failures,
                    "runs": args.runs,
                    "cpus": os.cpu_count(),
                },
                f,
                indent=2,
            )
    shutil.rmtree(work)
    if failures:
        print("\nFAILED:\n  " + "\n  ".join(failures), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

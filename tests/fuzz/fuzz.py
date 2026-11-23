#!/usr/bin/env python3
"""Differential mutation fuzzing of the kernel against nanoda.

Usage: python3 -I fuzz.py CERTUS NANODA_BIN EXPORT ITERATIONS SEED OUT_DIR

Each iteration mutates a valid lean4export file (replaces a subterm, a
declaration's type or value, a universe level, a bound-variable index or a
literal with another one defined earlier), de-duplicates and renumbers its
expressions (nanoda refuses duplicate or sparse ids; see dedup.py), and runs
both checkers on the result. nanoda reports type errors by panicking in its
type checker; panics elsewhere (its parser) and timeouts give no verdict.
A mutant is kept in OUT_DIR when Certus crashes, or when one checker accepts
it and the other rejects it: a possible soundness bug if Certus accepts, a
possible false rejection otherwise. Prints statistics as JSON
(C/c: Certus accepts/rejects, N/n: nanoda accepts/rejects).

Uses only the Python standard library."""
import json, os, random, subprocess, sys, tempfile

CERTUS, NANODA, SRC, N, SEED, OUT = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
DEDUP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dedup.py")
rng = random.Random(SEED)
lines = [json.loads(l) for l in open(SRC) if l.strip()]
expr_ids = [r["ie"] for r in lines if "ie" in r]
level_ids = [r["il"] for r in lines if "il" in r] + [0]
decl_idx = [i for i, r in enumerate(lines) if any(k in r for k in ("thm", "def"))]

def mutate(recs):
    recs = json.loads(json.dumps(recs))
    kind = rng.choice(["swap_child", "swap_child", "natlit", "level", "bvar", "decl_value", "decl_type"])
    if kind in ("decl_value", "decl_type"):
        i = rng.choice(decl_idx)
        d = recs[i].get("thm") or recs[i].get("def")
        field = "value" if kind == "decl_value" else "type"
        # only use expressions defined before this declaration
        before = [r["ie"] for r in recs[:i] if "ie" in r]
        d[field] = rng.choice(before)
        return kind, recs
    cands = [i for i, r in enumerate(recs) if "ie" in r]
    i = rng.choice(cands)
    r = recs[i]
    before = [x["ie"] for x in recs[:i] if "ie" in x]
    if not before:
        return None, recs
    if kind == "swap_child":
        for k in ("app", "lam", "forallE", "letE", "proj"):
            if k in r:
                fields = [f for f in ("fn", "arg", "type", "body", "value", "struct") if f in r[k]]
                f = rng.choice(fields)
                r[k][f] = rng.choice(before)
                return kind + ":" + k + "." + f, recs
        return None, recs
    if kind == "natlit":
        lits = [j for j, x in enumerate(recs) if "natVal" in x]
        if not lits: return None, recs
        j = rng.choice(lits)
        recs[j]["natVal"] = str(int(recs[j]["natVal"]) + rng.choice([1, -1 if int(recs[j]["natVal"]) > 0 else 2, 7]))
        return kind, recs
    if kind == "level":
        sorts = [j for j, x in enumerate(recs) if "sort" in x]
        if not sorts: return None, recs
        j = rng.choice(sorts)
        lv = [x["il"] for x in recs[:j] if "il" in x] + [0]
        recs[j]["sort"] = rng.choice(lv)
        return kind, recs
    if kind == "bvar":
        bv = [j for j, x in enumerate(recs) if "bvar" in x]
        if not bv: return None, recs
        j = rng.choice(bv)
        recs[j]["bvar"] = max(0, recs[j]["bvar"] + rng.choice([1, -1, 2]))
        return kind, recs
    return None, recs

def run(cmd, timeout=120):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return "timeout", ""

found = []
stats = {}
with tempfile.TemporaryDirectory() as td:
    path = os.path.join(td, "m.ndjson")
    cfg = os.path.join(td, "n.json")
    json.dump({"export_file_path": path, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
               "unpermitted_axiom_hard_error": False, "nat_extension": True, "string_extension": True,
               "num_threads": 1, "print_success_message": True}, open(cfg, "w"))
    for it in range(N):
        kind, m = mutate(lines)
        if kind is None:
            continue
        raw = path + ".raw"
        with open(raw, "w") as f:
            for r in m:
                f.write(json.dumps(r, ensure_ascii=False) + "\n")
        # Both checkers get the same de-duplicated, densely numbered file
        # (nanoda refuses duplicate or sparse expression ids).
        subprocess.run([sys.executable, "-I", DEDUP, raw, path], check=True)
        cc, co = run([CERTUS, "check", path, "--no-cache", "-j", "1"])
        nc, no = run([NANODA, cfg])
        c_ok = cc == 0
        n_ok = nc == 0 and "no typechecker errors" in no
        c_crash = cc not in (0, 1, 2) or "panicked" in co
        key = ("C" if c_ok else "c") + ("N" if n_ok else "n")
        stats[key] = stats.get(key, 0) + 1
        # nanoda reports type errors by panicking in its type checker.
        n_reject = nc != 0 and ("panicked at src/tc.rs" in no or "panicked at src/inductive" in no or "panicked at src/quot" in no or "typechecker error" in no.lower())
        n_crash = (nc == 101 or nc == "timeout") and not n_reject
        if n_crash and not c_crash:
            stats["nanoda-no-verdict"] = stats.get("nanoda-no-verdict", 0) + 1
            if c_ok:
                name = os.path.join(OUT, f"acc{SEED}_{it}.ndjson")
                os.replace(path, name)
                msg = [l for l in no.splitlines() if "panicked" in l or "Attempted" in l or "error" in l.lower()]
                found.append((name, kind, "certus-accepts-nanoda-crashed", msg[-2:]))
            continue
        if c_crash or (c_ok and n_reject) or (not c_ok and n_ok and cc != 2):
            name = os.path.join(OUT, f"m{SEED}_{it}.ndjson")
            os.replace(path, name)
            found.append((name, kind, cc, co.strip().splitlines()[-1:] if co else "", nc, no.strip().splitlines()[-1:] if no else ""))
print(json.dumps({"stats": stats, "found": found}, indent=1))

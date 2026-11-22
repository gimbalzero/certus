#!/usr/bin/env python3
"""The same theorem in Rocq, Agda, Isabelle and HOL Light, timed.

Usage:
    python3 systems.py rocq|agda|isabelle|hol-light [--runs 3] [--json out.json]
    python3 systems.py --table a.json b.json ...     # markdown table of results

Each system checks <system>/Sum.* (one theorem) and a generated file with
1,000 copies (<system>/gen.py), each copy with its own recursive definition,
as in the Lean race. We record the best wall time (and its CPU time) and the
size of whatever the system stores after checking.

Tools come from PATH: coqc/coqchk (or rocq), agda, isabelle. HOL Light needs
HOL_LIGHT_DIR pointing at a built checkout (`make` done, hol.sh present).
"""

import argparse
import glob
import json
import os
import resource
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
N = 1000


def run(cmd, cwd, stdin=None, env=None):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()
    r = subprocess.run(cmd, cwd=cwd, input=stdin, capture_output=True, text=True, env=env)
    wall = time.perf_counter() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        sys.exit(f"FAILED ({r.returncode}): {' '.join(cmd)}\n{out[-4000:]}")
    return wall, cpu, out


def best(cmd, cwd, runs, before=None, check=None):
    """Best wall time over `runs` runs, with its CPU time and output."""
    top = None
    for _ in range(runs):
        if before:
            before()
        wall, cpu, out = run(cmd, cwd)
        if check and not check(out):
            sys.exit(f"FAILED (output): {' '.join(cmd)}\n{out[-4000:]}")
        if top is None or wall < top[0]:
            top = (wall, cpu, out)
    return top


def version(cmd):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
        return (r.stdout + r.stderr).strip().splitlines()[0]
    except (OSError, IndexError):
        return "unknown"


def setup(system, ext, module_word):
    """Copy Sum.<ext> into a work dir and generate the 1,000-copy file."""
    work = tempfile.mkdtemp(prefix=f"race-{system}-")
    src = os.path.join(HERE, system)
    shutil.copy(os.path.join(src, f"Sum.{ext}"), work)
    gen = f"Gen{N}"
    out = subprocess.run([sys.executable, os.path.join(src, "gen.py"), str(N), gen],
                         capture_output=True, text=True, check=True).stdout
    with open(os.path.join(work, f"{gen}.{ext}"), "w", encoding="utf-8") as f:
        f.write(out)
    return work, gen


def row(rnd, step, wall, cpu, note=""):
    r = {"round": rnd, "step": step, "wall_ms": round(wall * 1e3, 1)}
    if cpu is not None:
        r["cpu_ms"] = round(cpu * 1e3, 1)
    if note:
        r["note"] = note
    print(f"| {rnd} | {step} | {wall * 1e3:,.0f} ms | {'' if cpu is None else f'{cpu * 1e3:,.0f} ms'} | {note} |",
          flush=True)
    return r


def rounds(gen):
    return [("1 theorem", "Sum"), ("1,000 theorems", gen)]


# ---------------------------------------------------------------------------


def rocq(runs):
    work, gen = setup("rocq", "v", "Sum")
    coqc = ["rocq", "compile"] if shutil.which("rocq") else ["coqc"]
    chk = ["rocqchk"] if shutil.which("rocqchk") else ["coqchk"] if shutil.which("coqchk") else ["rocq", "check"]
    rows, sizes = [], {}
    for rnd, mod in rounds(gen):
        vo = os.path.join(work, f"{mod}.vo")
        w, c, _ = best([*coqc, "-q", "-R", ".", "Race", f"{mod}.v"], work, runs)
        rows.append(row(rnd, "rocq compile (elaborate + kernel-check, writes .vo)", w, c))
        sizes[rnd] = os.path.getsize(vo)
        w, c, _ = best([*chk, "-silent", "-R", ".", "Race", "-norec", f"Race.{mod}"], work, runs)
        rows.append(row(rnd, "rocqchk on the .vo, trusts imports (-norec)", w, c))
        w, c, _ = best([*chk, "-silent", "-R", ".", "Race", f"Race.{mod}"], work, runs)
        rows.append(row(rnd, "rocqchk on the .vo and every library it loads", w, c))
    return {"version": version([coqc[0], "--version"]), "rows": rows, "stored": "the compiled .vo",
            "stored_bytes": sizes, "work": work}


def agda(runs):
    work, gen = setup("agda", "agda", "Sum")
    rows, sizes = [], {}

    def clean():
        shutil.rmtree(os.path.join(work, "_build"), ignore_errors=True)
        for f in glob.glob(os.path.join(work, "*.agdai")):
            os.remove(f)

    for rnd, mod in rounds(gen):
        w, c, _ = best(["agda", f"{mod}.agda"], work, runs, before=clean)
        rows.append(row(rnd, "agda (type-check from source, writes .agdai)", w, c))
        files = glob.glob(os.path.join(work, "**", f"{mod}.agdai"), recursive=True)
        sizes[rnd] = os.path.getsize(files[0])
    return {"version": version(["agda", "--version"]), "rows": rows, "stored": "the .agdai interface",
            "stored_bytes": sizes, "work": work}


def isabelle(runs):
    work, gen = setup("isabelle", "thy", "Sum")
    # Isabelle wants one directory per session.
    with open(os.path.join(work, "ROOT"), "w") as f:
        for name, thy in [("Race_Sum", "Sum"), (f"Race_{gen}", gen)]:
            os.makedirs(os.path.join(work, thy))
            shutil.move(os.path.join(work, f"{thy}.thy"), os.path.join(work, thy, f"{thy}.thy"))
            f.write(f'session {name} in "{thy}" = HOL +\n  options [document = false]\n  theories {thy}\n\n')
    heaps = subprocess.run(["isabelle", "getenv", "-b", "ISABELLE_HEAPS"], capture_output=True, text=True,
                           check=True).stdout.strip()
    rows, sizes = [], {}
    for rnd, sess in [("1 theorem", "Race_Sum"), ("1,000 theorems", f"Race_{gen}")]:
        w, c, out = best(["isabelle", "build", "-b", "-c", "-d", ".", sess], work, runs,
                         check=lambda o, s=sess: f"Finished {s}" in o)
        fin = [ln for ln in out.splitlines() if ln.startswith(f"Finished {sess}")]
        rows.append(row(rnd, "isabelle build (session on top of the HOL heap)", w, c, fin[0] if fin else ""))
        heap = glob.glob(os.path.join(heaps, "*", sess))
        sizes[rnd] = os.path.getsize(heap[0]) if heap else None
    return {"version": version(["isabelle", "version"]), "rows": rows,
            "stored": "the session heap (Isabelle keeps no proof objects by default)", "stored_bytes": sizes,
            "work": work}


def hol_light(runs):
    home = os.environ.get("HOL_LIGHT_DIR")
    if not home or not os.path.exists(os.path.join(home, "hol.sh")):
        sys.exit("set HOL_LIGHT_DIR to a built HOL Light checkout (hol.sh)")
    work, gen = setup("hol-light", "ml", "Sum")
    rows, sizes = [], {}
    # Loading the HOL Light core takes minutes, and constants cannot be
    # redefined, so each run is a fresh session that loads both files.
    top = None
    for _ in range(runs):
        script = (
            'print_string "RACE_START\\n";;\n'
            "let race_t0 = Sys.time();;\n"
            f'loadt "{work}/Sum.ml";;\n'
            "let race_t1 = Sys.time();;\n"
            f'loadt "{work}/{gen}.ml";;\n'
            "let race_t2 = Sys.time();;\n"
            'Printf.printf "RACE_TIMES %.6f %.6f\\n%!" (race_t1 -. race_t0) (race_t2 -. race_t1);;\n'
        )
        # hol.sh wraps the toplevel in ledit, which wants a terminal.
        wall, cpu, out = run(["./hol.sh"], home, stdin=script, env=dict(os.environ, LINE_EDITOR="env"))
        after = out.split("RACE_START", 1)[-1]
        if "RACE_START" not in out or "Exception" in after or "Error" in after or "RACE_TIMES" not in after:
            sys.exit(f"HOL Light run failed:\n{out[-6000:]}")
        t1, t2 = (float(x) for x in after.split("RACE_TIMES", 1)[1].split()[:2])
        if top is None or t1 + t2 < top[0] + top[1]:
            top = (t1, t2, wall)
    t1, t2, wall = top
    rows.append(row("1 theorem", "HOL Light, proof script in a loaded session (CPU, Sys.time)", t1, None))
    rows.append(row("1,000 theorems", "HOL Light, proof script in a loaded session (CPU, Sys.time)", t2, None))
    rows.append(row("startup", "whole session: load the HOL Light core, then both files", wall, None))
    for rnd, mod in rounds(gen):
        sizes[rnd] = None
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=home, capture_output=True,
                            text=True).stdout.strip()
    return {"version": f"HOL Light {commit or 'unknown'}, {version(['ocaml', '-version'])}", "rows": rows,
            "stored": "nothing: an LCF kernel keeps theorems, not proofs", "stored_bytes": sizes,
            "source_bytes": {"1 theorem": os.path.getsize(os.path.join(work, "Sum.ml")),
                             "1,000 theorems": os.path.getsize(os.path.join(work, f"{gen}.ml"))},
            "work": work}


SYSTEMS = {"rocq": rocq, "agda": agda, "isabelle": isabelle, "hol-light": hol_light}


def table(paths):
    print("| System | Round | Step | Wall | CPU | Stored proof |")
    print("|---|---|---|---|---|---|")
    for p in paths:
        with open(p) as f:
            d = json.load(f)
        for r in d["rows"]:
            size = d["stored_bytes"].get(r["round"])
            stored = f"{size / 1e3:,.1f} KB" if size else "n/a"
            cpu = f"{r['cpu_ms']:,.0f} ms" if "cpu_ms" in r else ""
            print(f"| {d['system']} ({d['version']}) | {r['round']} | {r['step']} | {r['wall_ms']:,.0f} ms | {cpu} "
                  f"| {stored} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("system", nargs="?", choices=sorted(SYSTEMS))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--json")
    ap.add_argument("--table", nargs="+", metavar="JSON")
    args = ap.parse_args()
    if args.table:
        table(args.table)
        return
    if not args.system:
        ap.error("name a system, or use --table")
    print(f"## {args.system}\n\n| Round | Step | Wall | CPU | Note |\n|---|---|---|---|---|", flush=True)
    res = SYSTEMS[args.system](args.runs)
    res["system"] = args.system
    res["runs"] = args.runs
    res["cpus"] = os.cpu_count()
    print(f"\nversion: {res['version']}\nstored ({res['stored']}): {res['stored_bytes']}")
    shutil.rmtree(res.pop("work"), ignore_errors=True)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(res, f, indent=2)


if __name__ == "__main__":
    main()

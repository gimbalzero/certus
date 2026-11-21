#!/usr/bin/env python3
"""Measure one shard of the Mathlib sample. Writes one JSON record per module.

    run_shard.py --mathlib DIR --tools DIR --out DIR [--budget-min 300] Mathlib.A Mathlib.B ...

For each module:
  1. elab        re-elaborate the file with Mathlib's build options and `-Dprofiler=true`
                 (imports come from the Mathlib cache) and keep Lean's cumulative
                 profiler times per category, plus process wall/CPU time.
  2. replay      kernel-only replay of the module's own declarations with Lean's kernel
                 (lean/KernelReplay.lean), imports loaded from .olean files.
  3. export      lean4export of the dependency closure of the module's own declarations.
  4. nanoda      kernel-only replay of that closure with nanoda.
  5. leanchecker the same closure replayed by Lean's kernel (`leanchecker --from-export`).
  6. certus      `certus extract` of the same roots, then `certus check` of the certificate.

Every step has a timeout, and the closure steps are skipped once the shard's time budget
runs low, so a slow module cannot cost the whole shard. Nothing is estimated: a step that
did not finish is recorded as not finished.
"""

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))

# Mathlib's lakefile `mathlibLeanOptions`, as Lake passes them to `lean` for `lake build`.
MATHLIB_OPTIONS = [
    "-Dpp.unicode.fun=true",
    "-DautoImplicit=false",
    "-DmaxSynthPendingDepth=3",
    "-Dweak.linter.unreachableTactic=false",
    "-Dweak.linter.unnecessarySeqFocus=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-Dweak.linter.style.header=true",
    "-Dweak.linter.checkInitImports=true",
    "-Dweak.linter.allScriptsDocumented=true",
    "-Dweak.linter.style.longFile=1500",
]

UNITS = {"ns": 1e-9, "us": 1e-6, "μs": 1e-6, "ms": 1e-3, "s": 1.0, "min": 60.0, "h": 3600.0}


def run(cmd, cwd, env, timeout, stdout_path=None, tail=4000):
    """Run cmd; return wall, CPU (user+sys), peak RSS and the output (or its tail)."""
    out_f = open(stdout_path, "wb") if stdout_path else subprocess.PIPE
    fd, err_path = tempfile.mkstemp(suffix=".stderr")
    err_f = os.fdopen(fd, "wb")
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=out_f, stderr=err_f, start_new_session=True)
    timed_out = False
    if stdout_path:
        status = None
        while status is None:
            pid, st, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                status = st
                break
            if time.perf_counter() - t0 > timeout:
                os.killpg(p.pid, signal.SIGKILL)
                timed_out = True
            time.sleep(0.05)
        stdout = ""
    else:
        # Read stdout while waiting so a full pipe cannot block the child.
        chunks = []

        def reader():
            for b in iter(lambda: p.stdout.read(1 << 16), b""):
                chunks.append(b)

        th = threading.Thread(target=reader)
        th.start()
        status = None
        while status is None:
            pid, st, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                status = st
                break
            if time.perf_counter() - t0 > timeout:
                os.killpg(p.pid, signal.SIGKILL)
                timed_out = True
            time.sleep(0.05)
        th.join()
        stdout = b"".join(chunks).decode("utf-8", "replace")
    wall = time.perf_counter() - t0
    if stdout_path:
        out_f.close()
    err_f.close()
    with open(err_path, "rb") as f:
        stderr = f.read().decode("utf-8", "replace")
    os.remove(err_path)
    code = os.waitstatus_to_exitcode(status)
    return {
        "ok": code == 0 and not timed_out,
        "exit": code,
        "timed_out": timed_out,
        "wall_s": round(wall, 3),
        "cpu_s": round(ru.ru_utime + ru.ru_stime, 3),
        "user_s": round(ru.ru_utime, 3),
        "sys_s": round(ru.ru_stime, 3),
        "max_rss_mb": round(ru.ru_maxrss / 1024, 1),
        "_stdout": stdout,
        "_stderr": stderr,
        "tail": (stdout + stderr)[-tail:] if code != 0 or timed_out else "",
    }


def clean(r):
    return {k: v for k, v in r.items() if not k.startswith("_")}


def parse_profile(text):
    """Lean's 'cumulative profiling times:' block -> {category: seconds}."""
    cats, inside = {}, False
    for line in text.splitlines():
        if line.startswith("cumulative profiling times"):
            inside = True
            continue
        if inside:
            m = re.match(r"^\s+(.+?) ([\d.]+)(ns|us|μs|ms|s|min|h)\s*$", line)
            if not m:
                if line.strip():
                    inside = False
                continue
            cats[m.group(1)] = cats.get(m.group(1), 0.0) + float(m.group(2)) * UNITS[m.group(3)]
    return cats


def lake_env(mathlib):
    """The environment `lake env` gives commands inside the Mathlib checkout."""
    out = subprocess.run(
        ["lake", "env", sys.executable, "-c", "import os, json; print(json.dumps(dict(os.environ)))"],
        cwd=mathlib, capture_output=True, text=True, check=True,
    ).stdout
    return json.loads(out.strip().splitlines()[-1])


def measure(mod, a, env, deadline, scratch):
    rel = mod.replace(".", "/") + ".lean"
    path = os.path.join(a.mathlib, rel)
    with open(path, encoding="utf-8") as f:
        lines = sum(1 for _ in f)
    rec = {"module": mod, "file": rel, "lines": lines}
    print(f"== {mod} ({lines} lines)", flush=True)

    # 1. Elaboration with the profiler.
    olean = os.path.join(scratch, "elab.olean")
    r = run(["lean", "--root=.", "-Dprofiler=true", *MATHLIB_OPTIONS, "-o", olean, rel],
            a.mathlib, env, a.elab_timeout)
    r["categories"] = parse_profile(r["_stdout"] + "\n" + r["_stderr"])
    if not r["categories"]:
        r["ok"] = False
        r["tail"] = r["tail"] or (r["_stdout"] + r["_stderr"])[-4000:]
    rec["elab"] = clean(r)
    for fn in os.listdir(scratch):
        os.remove(os.path.join(scratch, fn))
    print(f"   elab   ok={r['ok']} wall={r['wall_s']}s cpu={r['cpu_s']}s "
          f"kernel={r['categories'].get('type checking', 0):.2f}s", flush=True)

    # 2. Lean kernel replay of the module's own declarations.
    r = run(["lean", "--run", os.path.join(HERE, "lean", "KernelReplay.lean"), mod],
            a.mathlib, env, a.replay_timeout)
    m = re.search(r"replay_ok constants=(\d+) import_s=([\d.e+-]+) replay_s=([\d.e+-]+)", r["_stdout"])
    if m:
        r.update(constants=int(m.group(1)), import_only_s=float(m.group(2)), replay_only_s=float(m.group(3)))
    else:
        r["ok"] = False
    rec["replay"] = clean(r)
    print(f"   replay ok={r['ok']} wall={r['wall_s']}s replay_only={r.get('replay_only_s')}s", flush=True)

    # 3-6. The module's dependency closure.
    remaining = deadline - time.time()
    if remaining < a.closure_reserve:
        rec["closure_skipped"] = f"shard time budget: {remaining / 60:.0f} min left"
        print(f"   closure skipped ({rec['closure_skipped']})", flush=True)
        return rec

    r = run(["lean", "--run", os.path.join(HERE, "lean", "ModuleDecls.lean"), mod],
            a.mathlib, env, 900)
    roots = r["_stdout"].split()
    rec["roots"] = len(roots)
    if not r["ok"] or not roots:
        rec["roots_error"] = r["tail"] or "no declarations"
        return rec

    export = os.path.join(scratch, "closure.ndjson")
    r = run([os.path.join(a.tools, "lean4export"), mod, "--", *roots],
            a.mathlib, env, a.export_timeout, stdout_path=export)
    r["bytes"] = os.path.getsize(export) if os.path.exists(export) else 0
    rec["export"] = clean(r)
    print(f"   export ok={r['ok']} wall={r['wall_s']}s size={r['bytes'] / 1e6:.0f} MB", flush=True)

    if r["ok"]:
        cfg = os.path.join(scratch, "nanoda.json")
        with open(cfg, "w") as f:
            json.dump({
                "export_file_path": export,
                "use_stdin": False,
                "num_threads": os.cpu_count(),
                "stack_size_bytes": 1 << 30,
                "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
                "unpermitted_axiom_hard_error": False,
                "nat_extension": True,
                "string_extension": True,
                "print_success_message": True,
            }, f)
        r = run([os.path.join(a.tools, "nanoda_bin"), cfg], scratch, env, a.check_timeout)
        r["message"] = (r["_stdout"].strip().splitlines() or [""])[0][:500]
        rec["nanoda"] = clean(r)
        print(f"   nanoda ok={r['ok']} wall={r['wall_s']}s cpu={r['cpu_s']}s {r['message'][:120]}", flush=True)

        if deadline - time.time() > a.closure_reserve / 2:
            r = run(["leanchecker", "--from-export", export], scratch, env, a.check_timeout)
            r["message"] = (r["_stdout"] + r["_stderr"]).strip()[-500:]
            rec["leanchecker"] = clean(r)
            print(f"   leanchecker ok={r['ok']} wall={r['wall_s']}s cpu={r['cpu_s']}s", flush=True)

        cert = os.path.join(scratch, "closure.cert.ndjson")
        certus = os.path.join(a.tools, "certus")
        r = run([certus, "extract", export, cert, *roots], scratch, env, a.export_timeout)
        m = re.search(r"wrote (\d+) declarations", r["_stdout"])
        r["decls"] = int(m.group(1)) if m else None
        rec["certus_extract"] = clean(r)
        os.remove(export)
        if r["ok"] and deadline - time.time() > a.closure_reserve / 2:
            r = run([certus, "check", cert], scratch, env, a.check_timeout)
            out = r["_stdout"] + r["_stderr"]
            m = re.search(r"OK: (\d+) declarations type-checked in ([\d.]+) s", out)
            if m:
                r.update(checked=int(m.group(1)), kernel_s=float(m.group(2)))
            rej = re.search(r"REJECTED (.*)", out)
            r["rejected"] = rej.group(1)[:500] if rej else None
            rec["certus_check"] = clean(r)
            print(f"   certus ok={r['ok']} wall={r['wall_s']}s "
                  f"{('REJECTED ' + r['rejected'][:120]) if r['rejected'] else ''}", flush=True)
    for fn in os.listdir(scratch):
        os.remove(os.path.join(scratch, fn))
    return rec


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--mathlib", required=True)
    p.add_argument("--tools", required=True, help="dir with lean4export, nanoda_bin, certus")
    p.add_argument("--out", required=True)
    p.add_argument("--budget-min", type=float, default=300)
    p.add_argument("--elab-timeout", type=float, default=2400)
    p.add_argument("--replay-timeout", type=float, default=1200)
    p.add_argument("--export-timeout", type=float, default=1200)
    p.add_argument("--check-timeout", type=float, default=2400)
    p.add_argument("--closure-reserve", type=float, default=3600,
                   help="skip closure steps when fewer seconds than this remain")
    p.add_argument("modules", nargs="+")
    a = p.parse_args()
    a.mathlib, a.tools, a.out = map(os.path.abspath, (a.mathlib, a.tools, a.out))
    deadline = time.time() + a.budget_min * 60
    os.makedirs(a.out, exist_ok=True)
    scratch = os.path.join(a.out, "scratch")
    os.makedirs(scratch, exist_ok=True)
    env = lake_env(a.mathlib)
    for mod in a.modules:
        rec = measure(mod, a, env, deadline, scratch)
        rec["cpus"] = os.cpu_count()
        with open(os.path.join(a.out, mod + ".json"), "w") as f:
            json.dump(rec, f, indent=1)
    os.rmdir(scratch)


if __name__ == "__main__":
    main()

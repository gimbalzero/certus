#!/usr/bin/env python3
"""Combine the per-module JSON records from all shards into one report.

    aggregate.py <dir-with-json-files...> --md results.md --json results.json

Shares are ratios of sums over the sampled modules (a ratio estimator for all of
Mathlib, since modules were sampled uniformly). 95% intervals are percentile
bootstrap intervals, resampling modules with replacement (10,000 resamples,
fixed seed).
"""

import argparse
import glob
import json
import os
import random
import re
import statistics

GROUPS = [
    ("kernel", "Kernel type checking", lambda c: c == "type checking"),
    ("typeclass", "Typeclass inference", lambda c: c.startswith("typeclass inference")),
    ("linting", "Linting", lambda c: "lint" in c.lower() or c == "tacticAnalysis"),
    ("waiting", "Blocked waiting on other threads", lambda c: c.startswith("blocked")),
    ("tactics", "Tactics and search",
     lambda c: c in ("tactic execution", "congr simp thm")
     or re.search(r"simp|omega|grind|aesop|norm_num|linarith|positivity|decide", c) is not None),
    ("interpretation", "Interpreted meta code (Mathlib's own tactics)", lambda c: c == "interpretation"),
    ("imports", "Imports and initialization", lambda c: c in ("import", "initialization")),
    ("compilation", "Code generation and .olean output",
     lambda c: c.startswith("compilation") or "serialization" in c),
    ("elaboration", "Other elaboration", lambda c: True),
]
B = 10_000


def group(cats):
    out = {k: 0.0 for k, _, _ in GROUPS}
    for c, t in cats.items():
        for k, _, pred in GROUPS:
            if pred(c):
                out[k] += t
                break
    return out


def boot(pairs, rng):
    """Ratio of sums with a 95% bootstrap interval. pairs = [(num, den)]."""
    n = len(pairs)
    if n == 0:
        return None
    point = sum(p[0] for p in pairs) / sum(p[1] for p in pairs)
    reps = []
    for _ in range(B):
        s = [pairs[rng.randrange(n)] for _ in range(n)]
        den = sum(p[1] for p in s)
        if den > 0:
            reps.append(sum(p[0] for p in s) / den)
    reps.sort()
    return {"n": n, "point": point, "lo": reps[int(0.025 * len(reps))], "hi": reps[int(0.975 * len(reps)) - 1]}


def pct(r):
    return f"{100 * r['point']:.1f}% (95% CI {100 * r['lo']:.1f}–{100 * r['hi']:.1f}%, n={r['n']})" if r else "n/a"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("dirs", nargs="+")
    p.add_argument("--md", required=True)
    p.add_argument("--json", required=True)
    p.add_argument("--meta", default="{}", help="JSON with run metadata to include")
    a = p.parse_args()
    recs = []
    for d in a.dirs:
        for f in sorted(glob.glob(os.path.join(d, "**", "Mathlib.*.json"), recursive=True)):
            with open(f) as fh:
                recs.append(json.load(fh))
    recs.sort(key=lambda r: r["module"])
    rng = random.Random(12)
    meta = json.loads(a.meta)

    ok = [r for r in recs if r.get("elab", {}).get("ok")]
    rows = []
    for r in ok:
        g = group(r["elab"]["categories"])
        rows.append((r, g, sum(g.values())))

    res = {"meta": meta, "modules_sampled": len(recs), "modules_elaborated": len(ok)}
    tot = {k: sum(g[k] for _, g, _ in rows) for k, _, _ in GROUPS}
    total = sum(tot.values())
    res["profiled_total_s"] = total
    res["group_totals_s"] = tot
    res["shares"] = {k: boot([(g[k], t) for _, g, t in rows], rng) for k, _, _ in GROUPS}
    res["kernel_share_of_profile"] = res["shares"]["kernel"]
    res["kernel_share_excl_imports"] = boot([(g["kernel"], t - g["imports"]) for _, g, t in rows], rng)
    res["kernel_share_of_cpu"] = boot([(g["kernel"], r["elab"]["cpu_s"]) for r, g, _ in rows], rng)
    res["search_share"] = boot([(g["tactics"] + g["typeclass"] + g["interpretation"], t) for _, g, t in rows], rng)
    res["elab_wall_s"] = sum(r["elab"]["wall_s"] for r, _, _ in rows)
    res["elab_cpu_s"] = sum(r["elab"]["cpu_s"] for r, _, _ in rows)

    # E2: kernel-only replay of the module's own declarations (Lean kernel, same module).
    rp = [r for r in ok if r.get("replay", {}).get("ok")]
    res["replay_n"] = len(rp)
    res["replay_only_vs_elab_wall"] = boot([(r["replay"]["replay_only_s"], r["elab"]["wall_s"]) for r in rp], rng)
    res["replay_with_imports_vs_elab_wall"] = boot(
        [(r["replay"]["import_only_s"] + r["replay"]["replay_only_s"], r["elab"]["wall_s"]) for r in rp], rng)
    res["replay_only_vs_profiled_kernel"] = boot(
        [(r["replay"]["replay_only_s"], r["elab"]["categories"].get("type checking", 0.0)) for r in rp], rng)

    # E2: replay of the whole dependency closure.
    def closure(tool):
        xs = [r for r in ok if r.get(tool, {}).get("ok")]
        return {
            "n": len(xs),
            "attempted": sum(1 for r in recs if tool in r),
            "wall_s": sum(r[tool]["wall_s"] for r in xs),
            "cpu_s": sum(r[tool]["cpu_s"] for r in xs),
            "elab_wall_s_same_modules": sum(r["elab"]["wall_s"] for r in xs),
            "vs_elab_wall": boot([(r[tool]["wall_s"], r["elab"]["wall_s"]) for r in xs], rng),
            "median_wall_s": statistics.median([r[tool]["wall_s"] for r in xs]) if xs else None,
            "max_rss_mb": max([r[tool]["max_rss_mb"] for r in xs], default=None),
        }

    res["nanoda"] = closure("nanoda")
    res["leanchecker_closure"] = closure("leanchecker")
    cx = [r for r in recs if r.get("certus_extract", {}).get("decls")]
    res["closure_decls"] = {
        "n": len(cx),
        "median": statistics.median([r["certus_extract"]["decls"] for r in cx]) if cx else None,
        "max": max([r["certus_extract"]["decls"] for r in cx], default=None),
        "export_mb_median": statistics.median([r["export"]["bytes"] / 1e6 for r in cx]) if cx else None,
    }
    cc = [r for r in recs if "certus_check" in r]
    reasons = {}
    for r in cc:
        if r["certus_check"].get("rejected"):
            key = re.sub(r"`[^`]*`|'[^']*'|\"[^\"]*\"", "…", r["certus_check"]["rejected"])[:160]
            reasons.setdefault(key, []).append(r["module"])
    res["certus"] = {
        "attempted": len(cc),
        "accepted": sum(1 for r in cc if r["certus_check"]["ok"]),
        "rejected": sum(1 for r in cc if r["certus_check"].get("rejected")),
        "other_failure": sum(1 for r in cc if not r["certus_check"]["ok"] and not r["certus_check"].get("rejected")),
        "rejections": {k: v for k, v in sorted(reasons.items(), key=lambda kv: -len(kv[1]))},
        "accepted_wall_s": sum(r["certus_check"]["wall_s"] for r in cc if r["certus_check"]["ok"]),
        "accepted_modules": [r["module"] for r in cc if r["certus_check"]["ok"]],
        "closures_with_nested_inductives": sum(
            1 for r in recs if r.get("certus_extract", {}).get("nested_inductive_blocks")),
        "closures_scanned": sum(1 for r in recs if "nested_inductive_blocks" in r.get("certus_extract", {})),
    }
    res["failures"] = {
        r["module"]: {s: r[s].get("tail", "")[-300:] or ("timed out" if r[s].get("timed_out") else "failed")
                      for s in ("elab", "replay", "export", "nanoda", "leanchecker", "certus_extract")
                      if s in r and not r[s].get("ok")}
        for r in recs
    }
    res["failures"] = {k: v for k, v in res["failures"].items() if v}
    res["skipped_closure"] = {r["module"]: r["closure_skipped"] for r in recs if "closure_skipped" in r}

    ks = res["kernel_share_of_profile"]
    e1 = "fails" if ks and ks["point"] > 0.5 else "passes"
    if ks and ks["hi"] <= 0.10:
        h1 = "holds (whole 95% interval at or below 10%)"
    elif ks and ks["lo"] > 0.10:
        h1 = "fails (whole 95% interval above 10%)"
    else:
        h1 = "inconclusive (95% interval straddles 10%)"
    def e2v(r):
        return ("fails" if r["point"] > 0.30 else "passes") if r else "not measured"

    e2k = e2v(res["replay_only_vs_elab_wall"])
    e2i = e2v(res["replay_with_imports_vs_elab_wall"])
    res["verdict"] = {"E1": e1, "H1_kernel_le_10pct": h1, "E2_kernel_replay_only": e2k,
                      "E2_replay_with_per_module_imports": e2i}

    with open(a.json, "w") as f:
        json.dump(res, f, indent=1)

    L = []
    L.append("# Mathlib sample: where build time goes (E1/E2)\n")
    if meta:
        L.append(" · ".join(f"{k}: `{v}`" for k, v in meta.items()) + "\n")
    L.append(f"Modules sampled: **{len(recs)}**, elaborated successfully: **{len(ok)}**. "
             f"Total re-elaboration: {res['elab_wall_s']:.0f} s wall, {res['elab_cpu_s']:.0f} CPU-s; "
             f"{total:.0f} s across Lean's profiler categories.\n")
    L.append("## E1: profiler categories (share of profiled time)\n")
    L.append("| Category | Time (s) | Share, 95% CI |\n|---|---:|---|")
    for k, label, _ in GROUPS:
        L.append(f"| {label} | {tot[k]:.1f} | {pct(res['shares'][k])} |")
    L.append("")
    L.append(f"- **Kernel share of profiled time: {pct(ks)}**")
    L.append(f"- Kernel share excluding imports: {pct(res['kernel_share_excl_imports'])}")
    L.append(f"- Kernel time / process CPU time: {pct(res['kernel_share_of_cpu'])}")
    L.append(f"- Search (tactics + typeclass + interpreted tactics): {pct(res['search_share'])}\n")
    L.append("## E2: kernel-only replay\n")
    L.append(f"- Lean kernel replay of each module's own declarations, replay only / elaboration wall: "
             f"{pct(res['replay_only_vs_elab_wall'])}")
    L.append(f"- Same, including loading the module's imports from .olean files / elaboration wall: "
             f"{pct(res['replay_with_imports_vs_elab_wall'])}")
    L.append(f"- Replay-only time / kernel time in the profiler: {pct(res['replay_only_vs_profiled_kernel'])}")
    cd = res["closure_decls"]
    L.append(f"- Dependency closures: {cd['n']} exported; median {cd['median']} declarations "
             f"(max {cd['max']}), median export {cd['export_mb_median'] and round(cd['export_mb_median'])} MB")
    for tool, label in (("nanoda", "nanoda"), ("leanchecker_closure", "Lean kernel (`leanchecker --from-export`)")):
        c = res[tool]
        L.append(f"- {label}, whole closure: {c['n']}/{c['attempted']} finished; {c['wall_s']:.0f} s wall, "
                 f"{c['cpu_s']:.0f} CPU-s, vs {c['elab_wall_s_same_modules']:.0f} s elaborating just those modules "
                 f"(closure / module elaboration, wall: {pct(c['vs_elab_wall'])}); peak RSS {c['max_rss_mb']} MB")
    c = res["certus"]
    L.append(f"\n## Certus\n\n`certus check` on {c['attempted']} closure certificates: {c['accepted']} accepted, "
             f"{c['rejected']} rejected as unsupported, {c['other_failure']} other failures (timeout or crash).\n")
    for reason, mods in c["rejections"].items():
        L.append(f"- {len(mods)}× `{reason}`")
    if c["accepted_modules"]:
        L.append(f"- Accepted: " + ", ".join(f"`{m}`" for m in c["accepted_modules"]))
    L.append(f"- Closures containing at least one nested inductive: {c['closures_with_nested_inductives']} "
             f"of {c['closures_scanned']}")
    L.append("\n## Verdict\n")
    L.append(f"- E1 (fails if kernel share > 50%): **{e1}**")
    L.append(f"- H1 (kernel ≤ 10%): **{h1}**")
    L.append(f"- E2 (fails if replay > 30% of build), kernel replay alone: **{e2k}**")
    L.append(f"- E2, replay including each module's import loading (as `leanchecker` does it): **{e2i}**\n")
    if res["failures"] or res["skipped_closure"]:
        L.append("## Steps that did not finish\n")
        for m, v in res["failures"].items():
            L.append(f"- `{m}`: " + "; ".join(f"{s}: {t.strip().splitlines()[-1][:160] if t.strip() else 'failed'}"
                                              for s, t in v.items()))
        for m, v in res["skipped_closure"].items():
            L.append(f"- `{m}`: closure skipped ({v})")
    L.append("\n## Per module\n")
    L.append("| Module | Lines | Elab wall (s) | Kernel (s) | Kernel % | Replay (s) | nanoda closure (s) | Closure decls | Certus |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---|")
    for r in recs:
        e = r.get("elab", {})
        cats = e.get("categories", {})
        t = sum(cats.values())
        k = cats.get("type checking", 0.0)
        cc_ = r.get("certus_check", {})
        cert = "ok" if cc_.get("ok") else ("rejected" if cc_.get("rejected") else ("failed" if cc_ else "–"))
        L.append(f"| `{r['module']}` | {r['lines']} | {e.get('wall_s', '–') if e.get('ok') else 'failed'} | "
                 f"{k:.2f} | {100 * k / t if t else 0:.1f} | {r.get('replay', {}).get('replay_only_s', '–')} | "
                 f"{r['nanoda']['wall_s'] if r.get('nanoda', {}).get('ok') else '–'} | "
                 f"{r.get('certus_extract', {}).get('decls') or '–'} | {cert} |")
    with open(a.md, "w") as f:
        f.write("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()

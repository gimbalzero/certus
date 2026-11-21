# Hypotheses and experiments

**Main hypothesis:** almost all the time Lean spends building a project goes to repeated *searching*, not essential *checking*. If proofs are stored in explicit form and shared through a content-addressed cache, checking any proof is limited mainly by how fast the proof file can be read. Under that model, the 2026 Riemann Hypothesis formalisation drops from about 20 hours on 256 cores to under an hour on an 8-core laptop, plausibly minutes.

## Model

Build time = **S + I + K + W**

| Term | Meaning |
|---|---|
| **S**, search | Tactics, typeclass search and unification. This finds the proof. |
| **I**, imports | Each file reloading its dependencies. |
| **K**, kernel | Re-checking the finished proof, including unfolding definitions. |
| **W**, waiting | Cores idle on dependency chains. |

Only K is essential for trust, and even part of K is avoidable searching (deciding what to unfold).

## Sub-hypotheses

- **H1, where the time goes:** S + I + W ≥ 90% of a from-scratch build, so K ≤ 10%.
- **H2, checking speed:** fully explicit proofs check at Metamath-like speed, at least about 1M kernel steps per second per core.
- **H3, incremental cost:** with saved tactic results and a shared cache, a build costs in proportion to what changed, not to the size of the whole project.

## Experiments, with kill criteria

| | What | Tests | Hypothesis fails if |
|---|---|---|---|
| **E1** | Profile a Mathlib build per declaration: search, typeclass, imports, kernel | H1 | Kernel share > 50%. Focus then shifts to kernel hints. |
| **E2** | Time a kernel-only replay of Mathlib (nanoda or lean4checker) against the full build | H1 | Replay > 30% of build time |
| **E3** | Export a project and count kernel steps per source line | Size and speed estimates | > 10,000 steps per line puts "minutes" out of reach |
| **E4** | Fully explicit proofs (with unfolding hints) for one Mathlib folder: size and check speed | H2 | > 100× normal proof size, or < 100k steps/s/core |

## Evidence so far

### E1 and E2 on Mathlib (free GitHub Actions runners)

From [`benchmarks/mathlib-sample`](../benchmarks/mathlib-sample) ([results](../benchmarks/mathlib-sample/results/results.md), [run](https://github.com/gimbalzero/certus/actions/runs/44948153611)): 50 modules picked at random (seed 12) from the 8,689 in Mathlib `v4.36.0` (`fc4f59e5`), Lean 4.36.0, 20 runners with 4 vCPUs each. Each file was re-elaborated with `-Dprofiler=true` on top of Mathlib's prebuilt cache. The 50 files total 107 s of wall time, 158 CPU-s, and 174 s across Lean's profiler categories (median file: 158 lines, 1.1 s). Intervals are 95% bootstrap intervals over modules.

| Share of profiled time | Measured |
|---|---|
| **Kernel type checking (K)** | **4.8%** (3.6–6.1%) |
| Typeclass inference | 24.5% (11.8–34.3%) |
| Tactics and `simp` | 14.8% (11.0–19.6%) |
| Interpreted meta code (Mathlib's own tactics) | 12.6% (10.8–15.7%) |
| Imports and initialization (I) | 15.4% (10.2–24.7%) |
| Blocked waiting on other threads (W) | 10.7% (5.8–17.6%) |
| Other elaboration, linting, code generation | 17.2% |

- **H1 holds on Mathlib.** The kernel is 4.8% (95% CI 3.6–6.1%) of profiled time, 5.3% (4.0–6.8%) of process CPU time, and 5.6% (4.3–7.5%) with imports left out. The whole interval is below H1's 10%, and far below E1's 50% kill line. Search alone (tactics, typeclass inference, interpreted tactics) is 51.9% (41.8–58.3%). In one sampled file of 50 the kernel was over 10%: `Mathlib.LinearAlgebra.TensorProduct.Opposite`, at 20.6%.
- **E2, kernel work: passes.** Replaying each module's own declarations through Lean's kernel takes 5.7% (4.2–7.6%) of the time it took to elaborate that module.
- **E2 as `leanchecker` does it: fails.** Before it can replay, a `leanchecker`-style checker loads the module's imports with their proofs. That loading is 1.4 s for the median module, against 0.5 s of imports during elaboration, so replay including imports is 70.8% (48.8–105.9%) of elaboration time. The cost on top of the kernel comes from loading `.olean` files one module at a time, which a single certificate covering the whole closure would avoid.
- **Whole-closure replays.** The median module's dependency closure is 4,942 declarations (max 45,959), a 23 MB export. nanoda replays each full closure, back to `Init`, in a total of 83 s wall and 243 CPU-s for 49 modules, against 106 s to elaborate just those 49 modules. Lean's kernel (`leanchecker --from-export`) needs 367 s for the same closures.
- **Certus checks 3 of 49 closures today.** The other 46 are rejected at `Lean.Syntax`, a nested inductive type, and 46 of the 49 closures contain at least one nested inductive. Nested inductives are the blocker for Mathlib.

Caveats: most Mathlib files are small, so per-file imports and fixed costs weigh heavily here; W measures only waiting inside one file, not idle cores across a whole build; times come from one run on shared cloud machines, timed to about 50 ms.

### Phase 0, one laptop

From [`benchmarks/proof-bench`](../benchmarks/proof-bench), 1,000 copies of one theorem in Lean 4.36:

- **H1 holds at small scale.** With automated tactics, the kernel is about **8%** of CPU time and search is about 92%. The same theorems written explicitly need about 1 CPU-s of kernel time, against an 86 s build.
- **Automation inflates proofs.** `simp`/`omega` proofs are about 7× bigger and need about 23× more kernel work than explicit ones.
- **Checking only what is used is a large win.** `certus deps` shows that the automated proof needs 1,341 of the 58,555 declarations in Lean's core library (2.3%), and the explicit proof needs only 83 (0.1%). Today's independent checkers re-check all 58,555 every time.
- **lean4export already shares every repeated sub-term.** Of 6,138,037 expression nodes, 0 are exact repeats by content hash, so further compression has to come from alpha-normal hashing or a denser encoding, not from naive deduplication.
- **Reading the format is not the bottleneck.** `certus` parses the 348 MB core-library export at about 200 MB/s (3.8M records/s) and hashes all 6.5M nodes in about 1.3 s, on one core.

At Mathlib scale (above), the measured kernel share is 4.8%.

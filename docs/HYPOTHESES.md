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

## Evidence so far (Phase 0, one laptop)

From [`benchmarks/proof-bench`](../benchmarks/proof-bench), 1,000 copies of one theorem in Lean 4.36:

- **H1 holds at small scale.** With automated tactics, the kernel is about **8%** of CPU time and search is about 92%. The same theorems written explicitly need about 1 CPU-s of kernel time, against an 86 s build.
- **Automation inflates proofs.** `simp`/`omega` proofs are about 7× bigger and need about 23× more kernel work than explicit ones.
- **Checking only what is used is a large win.** `certus deps` shows that the automated proof needs 1,341 of the 58,555 declarations in Lean's core library (2.3%), and the explicit proof needs only 83 (0.1%). Today's independent checkers re-check all 58,555 every time.
- **lean4export already shares every repeated sub-term.** Of 6,138,037 expression nodes, 0 are exact repeats by content hash, so further compression has to come from alpha-normal hashing or a denser encoding, not from naive deduplication.
- **Reading the format is not the bottleneck.** `certus` parses the 348 MB core-library export at about 200 MB/s (3.8M records/s) and hashes all 6.5M nodes in about 1.3 s, on one core.

None of this has been tested at Mathlib scale. That is E1 and E2, the next milestone.

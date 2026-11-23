# Scoreboard: 44 axes

How proof systems compare, axis by axis, and where Certus stands. **Measured** numbers link to a benchmark; everything else is an assessment, and corrections are welcome. "Certus" shows the Phase target and current status.

Status key: ⬜ not started · 🟨 started · 🟩 measured win · ➖ out of scope until a later phase

## A. Speed and resources

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 1 | Fresh full check | Source to "verified" | Metamath: all of set.mm (48k theorems) in **6.9–10.1 s**, 1 core ([measured](../benchmarks/proof-bench)) | RH proof ≈ 20 h on 256 cores | Minutes on a laptop, from certificates | 🟩 1,000 theorems + foundations: 0.38 s vs Lean's 5.7 s build ([race](../benchmarks/race)) |
| 2 | Kernel check speed | Steps or declarations per second per core | Metamath Zero | nanoda: core library (58,555 decls) in **63 CPU-s** ([measured](../benchmarks/proof-bench)) | ≥ 1M steps/s/core (H2) | 🟨 Certus kernel: 3,080 decls in 0.38 CPU-s, the least CPU of the checkers raced ([race](../benchmarks/race)); whole core library (58,547 decls) in 18.0 CPU-s on one thread (nanoda 21.6 CPU-s in the same session) and 3.9 s wall on 8 threads (nanoda 6.6 s) ([race](../benchmarks/race#leans-whole-core-library-issue-3)) |
| 3 | Rebuild after one edit | Seconds | Isabelle, Lean | Re-elaborates everything downstream | < 1 s | ⬜ Phase 3 |
| 4 | Re-check unchanged project | Seconds | Nobody | **18 s** wall re-checking the core library every run ([measured](../benchmarks/proof-bench)) | < 1 s (content-hash cache) | 🟩 verdict cache ([docs](CACHE.md)): the whole core library (348 MB, 58,547 decls) re-checked in **0.4 s** when unchanged, against 18 s; one changed definition re-checks only it and its dependents (core library: 2.4 s) |
| 5 | Editor responsiveness | ms per edit | Isabelle | Good on small files, poor on large | < 50 ms | ➖ Phase 4 |
| 6 | Parallel scaling | Speedup with cores | Nobody well | Limited by files and chains | Near-linear (per-declaration) | 🟨 `certus check --jobs N`, same verdict for every N; parsing and hashing use every core too: core library 16.1 s on 1 thread, 3.9 s on 8 (4.1×; the M2 has 4 performance and 4 efficiency cores); 1,000 theorems in 70 ms on 8 threads vs 210 ms on 1 |
| 7 | Memory | Peak RAM | Metamath | High | 10× below Lean | 🟨 whole core library checked in 0.8 GB (each check's terms are forgotten once it is over; each term is stored once); nanoda 0.6–0.7 GB |
| 8 | Proof and cache size | Bytes | Metamath (50 MB text for set.mm) | Automated proofs 7× bigger than explicit ([measured](../benchmarks/proof-bench)) | Smaller than Lean's oleans | ⬜ |
| 9 | Startup and imports | Time to first line | Metamath | 0.8–1.0 s for core Lean ([measured](../benchmarks/proof-bench)) | < 50 ms | ⬜ Phase 3 |
| 10 | Install size | MB to start | Metamath (~1 MB) | ~3.2 GB | < 100 MB checker | 🟨 `certus` binary is about 1 MB |

## B. Trust and correctness

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 11 | Trusted code size | Lines that must be right | Metamath Zero (~730 lines of C) | ~8–20k lines of C++ (est.) | < 5k lines of Rust | 🟨 ~4,800 lines today, tests included (`wc -l crates/certus-kernel/src/*.rs`), with nested inductives and native `Nat` arithmetic |
| 12 | Verified kernel | Formal proof of the checker | Candle (to machine code) | Lean4Lean, partial | Aeneas or Verus proof | ⬜ Phase 2 |
| 13 | Independent checkers | Separately written checkers that agree | **Lean** (nanoda, Lean4Lean, con-leche, …) | Strong | 3+ by default | 🟨 Certus is a new independent checker; agrees with nanoda, con-leche, Lean4Lean and Lean's kernel on every race round, and with the expected verdict on every Lean Kernel Arena test |
| 14 | Soundness record and response | Bugs/year, disclosure process | HOL Light | Kernel bugs exploited in 2026 | Fixed disclosure timeline | 🟨 [SECURITY.md](../SECURITY.md) |
| 15 | Consistency of foundations | Proven consistent? | HOL family | Studied, not fully proven | Proven within a stronger system | ➖ |
| 16 | Escape-hatch control | Every unchecked shortcut detected | Metamath (none exist) | `#print axioms`, comparator | Automatic, for every theorem | 🟨 `certus deps` and `certus check --report` list every axiom (standard, sorry or non-standard) and every unsafe or partial declaration, per theorem; matches `#print axioms` ([docs](AUDIT.md)) |
| 17 | Statement auditing | Shows exactly what was proved | Nobody does this well | comparator (new) | Audit report per theorem | 🟨 `certus check --report` writes an audit report per theorem: exact statement, alpha-normal statement hash, axioms, closure size ([docs](AUDIT.md)); `certus show` prints any statement, with notation or `--raw` |
| 18 | Reproducible verdicts | Same input, same verdict, bit for bit | Metamath | Toolchain drift | Bit-for-bit | 🟨 audit reports are the same byte for byte for the same build and export, on any number of threads ([docs](AUDIT.md)); verdicts are the same for every thread count |
| 19 | Cache integrity | Corruption caught | Nobody | Fragile | Every entry checked by hash | 🟨 every key recomputed from the export, every entry carries a check value; bad entries only cause re-checks ([docs](CACHE.md)) |

## C. Logic and expressiveness

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 20 | Expressive foundations | Dependent types, quotients, univalence | Rocq, Agda | Strong, no univalence | Lean-compatible + optional univalent mode | ➖ Phase 5 |
| 21 | Computation in proofs | Evaluate and decide | Lean, Rocq | Strong | Certified computation | ⬜ |
| 22 | Modelling conveniences | Structures, classes, coercions | Lean | Strong | Keep Lean's | ➖ |
| 23 | Predictable checking | Decidable, no timeouts | HOL, Metamath | Timeouts in practice | Checking follows hints, no search | ⬜ E4 |

## D. Writing proofs

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 24 | Automation | Goals solved automatically | Isabelle Sledgehammer | Catching up | Beat Sledgehammer | ➖ Phase 4 |
| 25 | AI readiness | Datasets, APIs | **Lean** | Best | Stay the default | ➖ |
| 26 | Readable proofs | A mathematician can follow | Isabelle Isar, Mizar | Weak | Structured mode | ➖ Phase 4 |
| 27 | Error messages | Fixable without help | Isabelle | Weak | Explain the fix | ➖ Phase 4 |
| 28 | Robust to library updates | Proofs broken per update | Isabelle AFP | Brittle | Checked certificates never break | ⬜ |
| 29 | Learning curve | Time to productive | Isabelle | Hard | < 1 week | ➖ |
| 30 | Extensibility | Writing your own tactics | **Lean** | Best | Keep Lean's | ➖ |

## E. Library and ecosystem

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 31 | Library breadth | Areas covered | **Lean Mathlib** | Best | All of Mathlib, day one | ⬜ Phase 1 |
| 32 | Library coherence | Unified conventions | **Lean Mathlib** | Strong | Inherit Mathlib | ⬜ |
| 33 | Stability | Old proofs keep working | Isabelle, Rocq | Monthly breaking releases | Certificates are permanent | ⬜ |
| 34 | Portability | Export and translation | Dedukti ecosystem | lean4export only | Export to Dedukti and MM0 | ⬜ |
| 35 | Build tooling | Dependency management | cargo (as a model) | Lake quirks | cargo-smooth | ➖ Phase 3 |
| 36 | Editor support | Editors and quality | Isabelle/jEdit, Lean VS Code | VS Code-centric | 3+ editors | ➖ |
| 37 | Community and review speed | PR wait time | Lean (size) | ~68-day median review wait | < 1 week with bots | ⬜ |
| 38 | Governance and licence | Openness | Varies | Lean FRO, Apache-2.0 | Open foundation, Apache-2.0 | 🟨 Apache-2.0 |
| 39 | Verified software | Extraction track record | Rocq, Isabelle | Growing | Verified extraction | ➖ Phase 5 |
| 40 | Platforms | Where it verifies | Metamath (anywhere) | Desktop | Browser and phone | ⬜ Phase 3 |

## F. Scale and sharing

| # | Axis | Measure | Best today | Lean 4 | Certus target | Status |
|---|---|---|---|---|---|---|
| 41 | Distributed checking | Community splits the work | Nobody | No | Volunteer chunks | ⬜ spec §4 |
| 42 | Proof compression | Bytes per step | Metamath compressed proofs | lean4export already shares every repeated node, even up to alpha (0% unshared repeats; alpha-normal hashing saves 0.00% of 6.1M nodes, [measured](HYPOTHESES.md)) | Smaller than Metamath | 🟨 dedup exhausted ([spec v1](spec/certificate-v1.md)); next: denser encoding |
| 43 | Cheap outside verification | Cost to confirm a result | zkPi (research) | Rebuild everything | Seconds, then zk proofs | 🟨 check only the closure: 0.1–2.3% of the core library for our test theorems |
| 44 | Very large projects | 10M+ lines | Nobody tested | RH proof: the first real test, slow | 100M lines on a laptop | ⬜ |

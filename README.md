# Certus

**Fast, verifiable proof checking for Lean, written in Rust.**

Checking a large Lean project today means rebuilding it. The 2026 formalisation of the Riemann Hypothesis takes about 20 hours on a 256-core machine to build. Most of that time is Lean *searching* for proofs, which the author's machine already did. Only a small part is *checking* them.

Certus separates the two. **Search once, check forever.** The author's machine publishes the finished proofs as a content-addressed certificate. Anyone can then verify it from scratch, checking only what the theorem actually uses, spread across every core, with nothing re-done that has already been checked.

The goal: **minutes on a laptop instead of days on a server**, and the best system on every one of the [44 axes](docs/SCOREBOARD.md) we track.

> **Status: early Phase 1.** Certus has a working kernel: it type-checks Lean proofs from scratch, regenerates every recursor rather than trusting it, and beats Lean by 15–30× on our first benchmark. It supports nested inductive types; multi-core checking is next. See the [plan](docs/PLAN.md).

## The race

The same theorem, 2·(0+1+…+n) = n(n+1), checked from a certificate containing it and everything it depends on, back to the definition of `Nat` ([full results](benchmarks/race)):

| | 1 theorem | 1,000 theorems |
|---|---|---|
| **Certus** (1 core) | **10 ms** | **384 ms** (least CPU of all) |
| nanoda (8 cores) | 8 ms | 125 ms |
| con-leche (8 cores) | 17 ms | 391 ms |
| Lean kernel replay (trusts imports) | 390 ms | 1,210 ms |
| Lean, build from source | 297 ms | 5,650 ms |

## What works today

```bash
cargo build --release
./target/release/certus check export.ndjson My.theorem             # type-check it and everything it uses
./target/release/certus extract export.ndjson cert.ndjson My.theorem   # write a minimal certificate
./target/release/certus stats export.ndjson          # counts, throughput, repeated content
./target/release/certus hash  export.ndjson --manifest decls.tsv   # content hash of every declaration
./target/release/certus deps  export.ndjson My.theorem             # what it depends on, and its axioms
./target/release/certus show  export.ndjson My.theorem [--raw]     # the exact statement that was proved
```

Exports come from [`lean4export`](https://github.com/leanprover/lean4export) (format 3.x).

- **A real kernel** (~2,800 lines of Rust). It checks types, definitions, theorems, inductive types (positivity, universes, and recursors rebuilt from scratch), and quotients. It also has proof irrelevance, eta and fast `Nat` arithmetic, which switches on only after it verifies `Nat` and each operation are the genuine ones. It rejects every tampered certificate in its test suite.
- **Strict reader.** It rejects unknown fields and record kinds, forward references, gaps in ids, duplicate declarations and malformed literals.
- **Content hashes.** Every name, level, expression and declaration gets a BLAKE3 hash, as defined in the [certificate spec v0](docs/spec/certificate-v0.md). This is the basis for a cache that never needs trusting.
- **Dependency closure and axiom audit.** It lists exactly which declarations and axioms a theorem rests on, and flags `sorryAx`, unsafe and partial definitions. Verified to match Lean's `#print axioms` on our benchmark.

## Lean Kernel Arena

CI runs the [Lean Kernel Arena](https://arena.lean-lang.org) test suite on every pull request ([workflow](.github/workflows/arena.yml)). These are the community's export files that a correct checker must accept or reject. The run fails on any new false acceptance. A false acceptance that is already tracked by a `soundness` issue is listed in [`known-unsound.txt`](tests/arena/known-unsound.txt) and is still reported in every run. False rejections are listed in the job summary, and each cause has its own issue. To run it locally:

```bash
cargo build --release
python3 tests/arena/run.py                 # the pinned round 2026-09; downloads ~4 MB to ~/.cache/certus-arena
python3 tests/arena/run.py --suite live    # the tests arena.lean-lang.org serves today
```

The large real-world corpora (Init, Std, Mathlib, …) are not in the Arena's download and are skipped. So are the `either` corner cases, which the Arena does not score.

## First results

The 348 MB export of Lean 4.36's core library plus one test file, on an Apple M2 laptop, single-threaded:

| | |
|---|---|
| Parse 6.5M records | **1.7 s** (200 MB/s) |
| Hash 6.5M nodes | **1.3 s** |
| Peak memory | **0.5 GB** |
| Declarations an automated proof of Σk = n(n+1)/2 depends on | **1,341 of 58,555 (2.3%)** |
| ... with the same proof written out explicitly | **83 of 58,555 (0.1%)** |

From the [Lean vs Metamath benchmark](benchmarks/proof-bench), about **92%** of Lean's build time for those proofs goes to search, not checking. Today's independent checkers re-check all 58,555 core declarations (18 s) before reaching a single user proof. Details are in [HYPOTHESES.md](docs/HYPOTHESES.md).

## Roadmap

| Phase | Goal |
|---|---|
| **0. Foundation** (done) | Spec, tools, baselines; measure Mathlib's search-vs-check split |
| **1. Fastest checker** (now) | Parallel Rust kernel with a content-addressed cache; beat nanoda on Lean's core library |
| **2. Most trusted** | Kernel under 5,000 lines, formal verification, full statement audit |
| **3. Best build experience** | Lake plugin, sub-second rebuilds, verification in the browser |
| **4–5.** | AI-first proof writing, permanent certificates, zero-knowledge verification |

## Built on

Certus stands on the work of the Lean community: [Lean 4](https://github.com/leanprover/lean4), [lean4export](https://github.com/leanprover/lean4export), [nanoda](https://github.com/ammkrn/nanoda_lib), [Lean4Lean](https://github.com/digama0/lean4lean), the Lean Kernel Arena, and the ideas of [Metamath Zero](https://github.com/digama0/mm0).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Soundness bugs are security bugs: see [SECURITY.md](SECURITY.md).

## Licence

[Apache-2.0](LICENSE), the same as Lean.

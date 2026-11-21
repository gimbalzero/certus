# The race: Certus vs Lean vs independent checkers

The same theorem, **2 · (0 + 1 + … + n) = n(n + 1)**, checked by every system we could run. Apple M2, 8 cores, Lean 4.36.0, best of 7 runs (2 for the slow Lean build), 21 Nov 2026.

Every checker except "Lean, build from source" reads **the same certificate**: the theorems plus every declaration they depend on, all the way back to the definitions of `Nat` and `Eq`. Certus made it with `certus extract`. Nothing is trusted or skipped: each checker re-checks all of it.

## Round 1: one theorem (83 declarations, 161 KB certificate)

| Checker | Wall time | CPU time | What it checks |
|---|---|---|---|
| nanoda (Rust, 8 threads) | **8 ms** | 13 ms | all 83 declarations |
| **Certus** (Rust, 1 thread) | **10 ms** | **9 ms** | all 83 declarations |
| con-leche | 17 ms | 29 ms | all 83 declarations |
| Lean, build from source | 297 ms | 307 ms | elaborates the file, kernel-checks 3 declarations, trusts the 80 imported ones |
| Lean kernel replay (`leanchecker`) | 390 ms | 387 ms | re-checks the file's 3 declarations, trusts the imported ones |

## Round 2: 1,000 theorems (3,080 declarations, 3.6 MB certificate)

Each copy has its own recursive definition, so this is 1,000 definitions and 1,000 proofs, plus the shared foundations.

| Checker | Wall time | CPU time | vs Lean build |
|---|---|---|---|
| nanoda (8 threads) | **125 ms** | 602 ms | 45× faster |
| **Certus** (1 thread) | **384 ms** | **382 ms** (least CPU) | **15× faster** |
| con-leche (8 threads) | 391 ms | 1,868 ms | 14× faster |
| Lean kernel replay (`leanchecker`) | 1,210 ms | 1,205 ms | 4.7× faster |
| Lean, build from source | 5,650 ms | 20,434 ms | 1× |
| *Metamath, all of set.mm (48,388 theorems), for scale* | *8,647 ms* | *8,643 ms* | n/a |

## What it shows

1. **Checking a certificate beats rebuilding by 15–45×**, for every independent checker. Most of Lean's build is searching for proofs, which the certificate makes unnecessary. That is the core claim of Certus, now measured end to end.
2. **Certus does the least work.** It uses the least CPU of any checker: 382 ms against nanoda's 602 ms and con-leche's 1,868 ms. It is slower on the clock only because it runs on one core while nanoda uses eight. **Making Certus parallel is the next milestone**, and on CPU time alone it would then be the fastest.
3. **Certus only accepts what all three agree on.** nanoda and con-leche both accept the same certificates. Certus also rejects all seven tampered versions in its test suite: a wrong proof, a changed statement, a missing definition, a forged recursor, data posing as a theorem, an injected field, and a `partial` definition.
4. **Lean's own checkers trust their imports.** `leanchecker` and the Lean build re-check only the file's own declarations and load the rest from `.olean` files. Certus re-checks everything the theorem depends on, and is still faster.

## Not in the race (yet)

- **The automated (`simp`/`omega`) proof.** It depends on `Lean.Syntax`, a *nested* inductive type, which Certus rejects for now rather than skipping. Nested inductives are the next kernel feature.
- **Lean4Lean.** The binary we have was built for a different Lean version.
- **Rocq, Isabelle, Agda, HOL Light.** Each needs several GB to install, which this machine doesn't have free. They are planned for CI.
- **Metamath on just this theorem.** set.mm's `arisum` depends on 4,594 earlier theorems. Verifying them one command at a time took 44 s, almost all of it command overhead, so the number would mislead. The whole-library time above is the fair Metamath figure.

## Reproduce

```bash
cargo build --release                         # at the repo root
export PATH=/path/to/lean-4.36.0/bin:$PATH    # lean, leanexport, leanchecker, nanoda_bin, con-leche
python3 benchmarks/race/race.py --runs 7       # --json out.json for raw numbers
```

Missing optional checkers (leanchecker, nanoda, con-leche, Metamath) are skipped with a note; `--require all` makes them mandatory. The script also feeds Certus seven tampered certificates and fails unless it rejects every one.

## In CI

`.github/workflows/race.yml` runs the race on every push to `main` (and on demand) on a GitHub Linux runner: Lean 4.36.0 via elan, lean4export, nanoda and con-leche built from pinned sources, Metamath and set.mm fetched as in `proof-bench/bench.sh`. The JSON and the tables are uploaded as the `race-results` artifact and shown in the run summary. The job fails if any checker rejects a valid certificate, if Certus accepts a tampered one, or if a checker is missing.

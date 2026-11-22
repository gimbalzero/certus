# The race: Certus vs Lean vs independent checkers

The same theorem, **2 · (0 + 1 + … + n) = n(n + 1)**, checked by every system we could run, first with an explicit proof (rounds 1 and 2), then with an automated `simp`/`omega` proof (rounds 3 and 4). Rounds 1 and 2: Apple M2, 8 cores, Lean 4.36.0, best of 7 runs (2 for the slow Lean build), 21 Nov 2026. The Certus rows are from a later run on the same machine with multi-core checking (`race.py --runs 5`, 22 Nov 2026). In that run nanoda took 5 ms and 84 ms.

Every checker except "Lean, build from source" reads **the same certificate**: the theorems plus every declaration they depend on, all the way back to the definitions of `Nat` and `Eq`. Certus made it with `certus extract`. Nothing is trusted or skipped: each checker re-checks all of it.

## Round 1: one theorem (83 declarations, 161 KB certificate)

| Checker | Wall time | CPU time | What it checks |
|---|---|---|---|
| **Certus** (Rust, 8 threads) | **5 ms** | 11 ms | all 83 declarations |
| nanoda (Rust, 8 threads) | 8 ms | 13 ms | all 83 declarations |
| con-leche | 17 ms | 29 ms | all 83 declarations |
| Lean, build from source | 297 ms | 307 ms | elaborates the file, kernel-checks 3 declarations, trusts the 80 imported ones |
| Lean kernel replay (`leanchecker`) | 390 ms | 387 ms | re-checks the file's 3 declarations, trusts the imported ones |

## Round 2: 1,000 theorems (3,080 declarations, 3.6 MB certificate)

Each copy has its own recursive definition, so this is 1,000 definitions and 1,000 proofs, plus the shared foundations.

| Checker | Wall time | CPU time | vs Lean build |
|---|---|---|---|
| **Certus** (8 threads) | **70 ms** | 373 ms | **81× faster** |
| nanoda (8 threads) | 125 ms | 602 ms | 45× faster |
| con-leche (8 threads) | 391 ms | 1,868 ms | 14× faster |
| Lean kernel replay (`leanchecker`) | 1,210 ms | 1,205 ms | 4.7× faster |
| Lean, build from source | 5,650 ms | 20,434 ms | 1× |
| *Metamath, all of set.mm (48,388 theorems), for scale* | *8,647 ms* | *8,643 ms* | n/a |

## Rounds 3 and 4: the automated proof

The same theorem, proved by automation instead of named rewrites:

```lean
induction n with
| zero => rfl
| succ k ih =>
  simp only [sumTo, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
  omega
```

`omega` builds its proof from Lean's own `Lean.Omega` library, so the certificate is much larger: it re-checks that library and everything under it, including the nested inductive `Lean.Syntax`. Measured on `ubuntu-latest` (4 cores) in CI, [run 44995719467](https://github.com/gimbalzero/certus/actions/runs/44995719467), 21 Nov 2026: best of 5 runs (2 for the 1,000-copy Lean build). The Apple M2 column is a local run, best of 7.

### Round 3: one theorem, automated (1,341 declarations, 4.2 MB certificate)

| Checker | Wall time | CPU time | Apple M2 wall | What it checks |
|---|---|---|---|---|
| nanoda (4 threads) | **101 ms** | 247 ms | 57 ms | all 1,341 declarations |
| con-leche (4 threads) | 152 ms | 487 ms | 1,068 ms | all 1,341 declarations |
| **Certus** (1 thread) | **177 ms** | **176 ms** (least CPU) | 60 ms (8 threads) | all 1,341 declarations |
| Lean, build from source | 248 ms | 275 ms | 182 ms | elaborates `Sum.lean` (both proofs), trusts the imported `Lean.Omega` library |
| Lean kernel replay (`leanchecker`) | 454 ms | 455 ms | 234 ms | re-checks `Sum.lean`'s own declarations, trusts the imported ones |

`Sum.lean` holds both proofs, so the two Lean rows do the same work as in round 1. The con-leche time on the M2 is its best of 7 there; on the CI runner it was 152 ms.

### Round 4: 1,000 automated theorems (5,337 declarations, 28.9 MB certificate)

| Checker | Wall time | CPU time | Apple M2 wall | vs Lean build (CI) |
|---|---|---|---|---|
| nanoda (4 threads) | **2,943 ms** | 10,765 ms | 1,121 ms | 9.5× faster |
| con-leche (4 threads) | 3,509 ms | 13,807 ms | 3,274 ms | 8.0× faster |
| **Certus** (1 thread) | **8,653 ms** | **8,653 ms** (least CPU) | 1,413 ms (8 threads) | **3.2× faster** |
| Lean kernel replay (`leanchecker`) | 10,247 ms | 10,245 ms | 6,307 ms | 2.7× faster |
| Lean, build from source | 27,993 ms | 66,761 ms | 9,039 ms | 1× |

The Apple M2 column for Certus is a local run of `race.py --runs 5` with multi-core checking (8 threads), 22 Nov 2026. In that run nanoda took 1,114 ms on round 4 and 57 ms on round 3. With the kernel speed-ups of [#22](https://github.com/gimbalzero/certus/issues/22) as well, round 4 takes 0.83 s on 8 threads. The CI columns are still single-threaded Certus and will update on the next CI run.

The CI run's explicit rounds, for comparison: round 1 Certus 8 ms, nanoda 6 ms, con-leche 15 ms, Lean build 247 ms; round 2 Certus 301 ms, nanoda 181 ms, con-leche 287 ms, `leanchecker` 1,220 ms, Lean build 10,054 ms, Metamath 6,390 ms.

## What it shows

1. **Checking a certificate beats rebuilding by 15–45×**, for every independent checker. Most of Lean's build is searching for proofs, which the certificate makes unnecessary. That is the core claim of Certus, now measured end to end.
2. **Certus is now the fastest certificate checker on the clock.** Since `certus check --jobs N` (default: all cores, [#2](https://github.com/gimbalzero/certus/issues/2)), it checks round 2 in 70 ms on 8 threads against nanoda's 125 ms (84 ms in the same local run). On one thread it uses the least CPU of any checker (382 ms against nanoda's 602 ms and con-leche's 1,868 ms). The verdict is the same for every number of threads: each thread builds the full environment and type-checks the declarations it claims, so threads repeat some cheap work (converting terms, checking inductive types), and that costs CPU.
3. **Certus only accepts what all three agree on.** nanoda and con-leche both accept the same certificates. Certus also rejects all seven tampered versions in its test suite: a wrong proof, a changed statement, a missing definition, a forged recursor, data posing as a theorem, an injected field, and a `partial` definition.
4. **Lean's own checkers trust their imports.** `leanchecker` and the Lean build re-check only the file's own declarations and load the rest from `.olean` files. Certus re-checks everything the theorem depends on, and is still faster.
5. **Automation narrows the gap but does not close it.** `simp` and `omega` find their proofs quickly, but the proofs they leave behind are large, so checking the certificate costs more. On 1,000 automated copies every certificate checker still beats the Lean build (3.2–9.5× in CI), and Certus still uses the least CPU (8.7 s against nanoda's 10.8 s and con-leche's 13.8 s). Here single-threading costs Certus the most: on the clock it is 3× behind nanoda.

## Lean's whole core library (issue #3)

Not a race round, but the largest test: lean4export's export of `benchmarks/proof-bench/lean/Empty.lean`, which is all of Lean 4.36's `Init` (58,547 declarations, 348 MB, 6.5M records; the export itself takes 31 s). **Certus accepts every declaration**, both on `main` and with the open kernel pull requests. Measured on the Apple M2 (8 cores), 22 Nov 2026, one run each, all in the same session:

| Checker | Wall time | CPU time | Peak memory |
|---|---|---|---|
| nanoda (8 threads) | **8.1 s** | 38.3 s | 0.43 GB |
| **Certus**, with #36, #38, #40, #41 (4 threads) | **9.7 s** | **31.2 s** | 4.5 GB |
| Certus, same, 8 threads | 12.6 s | 62.0 s | 7.7 GB |
| con-leche (8 threads) | 20.1 s | 92.2 s | 0.82 GB |
| Certus, same, 1 thread | 21.2 s | 20.0 s (least CPU) | 1.9 GB |
| Certus `main` (1 thread) | 40.9 s | 40.6 s | 1.9 GB |
| **Certus re-check with the verdict cache (#41), unchanged** | **3.3 s** | 3.3 s | 0.49 GB |

The figures in issue #3 (nanoda 18 s wall / 63 CPU-s, con-leche 56 s / 167 CPU-s) come from an earlier local measurement. The table above measures all three checkers in one session, so compare within it. In the same session, Certus on one thread uses about half of nanoda's CPU, and the kernel speed-ups of #38 halve Certus's own time (40.9 s to 21.2 s). With several threads, every Certus worker converts the whole library into its own term store, so memory grows with the thread count and 8 threads are slower than 4. Sharing the converted terms between workers is #39. Reproduce with `lean -o olean/Empty.olean Empty.lean && leanexport Empty > init.ndjson` in `benchmarks/proof-bench/lean`, then `certus check init.ndjson --no-cache --jobs 4`.

## Other provers: Rocq, Agda, Isabelle, HOL Light

The same theorem, written natively in each system under `benchmarks/race/<system>/` (`Sum.*`, plus `gen.py` for the 1,000-copy file, each copy with its own recursive definition). Each one needs GBs of disk, so `.github/workflows/race-systems.yml` checks them on GitHub Actions with `benchmarks/race/systems.py`. Measured on `ubuntu-latest` (4 cores), [run 44949005331](https://github.com/gimbalzero/certus/actions/runs/44949005331), 21 Nov 2026: best of 3 runs (1 run for HOL Light).

These are **not** certificate checks like the Lean rows above. Each system checks its own file its own way, and the proofs differ: Rocq uses `nia`, Isabelle `auto`, HOL Light `ARITH_TAC`, and Agda has no tactics, so its proof is an explicit term with its own arithmetic lemmas and no standard library.

| System | What is timed | 1 theorem | 1,000 theorems | Stored proof (1 / 1,000) |
|---|---|---|---|---|
| Rocq 9.3.0 | `rocq compile`: elaborate, run tactics, kernel-check, write `.vo` | 284 ms | 4,419 ms | `.vo`: 4.2 KB / 1,028 KB |
| Rocq 9.3.0 | `rocqchk -norec`: re-check the stored `.vo`, trust imports | 284 ms | 1,459 ms | (same `.vo`) |
| Rocq 9.3.0 | `rocqchk`: re-check the `.vo` and every library it loads (Stdlib's `Lia` and its dependencies) | 14,291 ms | 15,575 ms | (same `.vo`) |
| Agda 2.9.0 | `agda`: type-check from source, write `.agdai` | 111 ms | 10,369 ms | `.agdai`: 29 KB / 2,052 KB |
| Isabelle2026 | `isabelle build`: a session on top of the shipped HOL heap (wall includes JVM and ML start-up; CPU is summed over threads) | 10,403 ms (Isabelle reports 4 s elapsed) | 25,802 ms (Isabelle reports 19 s elapsed) | session heap: 4.0 MB / 38.7 MB |
| HOL Light (1a0c0e6, OCaml 4.14.5) | the proof script, run in a session that already loaded the core (CPU time, `Sys.time`) | 38 ms | 34,289 ms | none: an LCF kernel keeps theorems, not proofs (the script is 0.3 KB / 227 KB) |

Loading the HOL Light core before the script took most of that session's 128 s of wall time (that 128 s also includes the 34 s for 1,000 theorems). Isabelle stores no proof objects by default, so its row reports the session heap that the build saves.

## Not in the race (yet)

- **Lean4Lean.** The binary we have was built for a different Lean version.
- **Metamath on just this theorem.** set.mm's `arisum` depends on 4,594 earlier theorems. Verifying them one command at a time took 44 s, almost all of it command overhead, so the number would mislead. The whole-library time above is the fair Metamath figure.

## Reproduce

```bash
cargo build --release                         # at the repo root
export PATH=/path/to/lean-4.36.0/bin:$PATH    # lean, leanexport, leanchecker, nanoda_bin, con-leche
python3 benchmarks/race/race.py --runs 7       # --json out.json for raw numbers
```

Missing optional checkers (leanchecker, nanoda, con-leche, Metamath) are skipped with a note; `--require all` makes them mandatory. The script also feeds Certus seven tampered certificates and fails unless it rejects every one.

## In CI

`.github/workflows/race.yml` runs the race on every push to `main` (and on demand) on a GitHub Linux runner: Lean 4.36.0 via elan, lean4export, nanoda and con-leche built from pinned sources, Metamath and set.mm fetched as in `proof-bench/bench.sh`. It runs all four rounds. The JSON and the tables are uploaded as the `race-results` artifact and shown in the run summary. The job fails if any checker rejects a valid certificate, if Certus accepts a tampered one, or if a checker is missing.

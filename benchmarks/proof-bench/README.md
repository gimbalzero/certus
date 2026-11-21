# Proof benchmark: Lean 4 vs Metamath

The same simple theorem, **2 · (0 + 1 + … + n) = n(n + 1)**, checked in Lean 4 and in Metamath, to see where proof-checking time goes and how far a "search once, check fast" design could go.

Machine: Apple M2, 8 cores, 16 GB RAM, macOS. Lean 4.36.0 (core only, no Mathlib). metamath-exe built from source with `cc -O2`, and `set.mm` from the `develop` branch (20 Nov 2026). Times are from 2–3 runs each, warm disk cache.

## Results

### Lean: same theorem, two proof styles, 1,000 copies

| | Automated proof (`simp` + `omega`) | Explicit proof (named `rw` steps) |
|---|---|---|
| Full Lean build, wall time | **86.1 s** | **28.3 s** |
| Build time per theorem | ~86 ms | ~28 ms |
| Proof-term size (exported lines) | +536,220 | +73,203 (**7.3× smaller**) |
| Kernel-only recheck, nanoda (Rust), CPU | +18.8 CPU-s | +0.8 CPU-s (**~23× less**) |
| Kernel-only recheck, con-leche, CPU | +17 CPU-s | +5 CPU-s (noisy) |

- A single file with both proofs takes 0.78 s, almost all of it Lean starting up. An empty file takes 0.8–1.0 s.
- The recheck rows show the extra cost on top of re-checking Lean's core library (`Init`, about 60,000 declarations). On its own, `Init` costs **63 CPU-s / 18 s wall time with nanoda** and **167 CPU-s / 56 s wall time with con-leche**, every time.

Lean's profiler breakdown for the 1,000 automated proofs (the categories overlap, so read these as shares only):
- kernel type checking 28%;
- `simp` about 30%;
- `omega` 12%;
- typeclass inference 12%;
- general elaboration 7%.

For the explicit proofs, `rw` is 22%, typeclass inference 20%, elaboration 17% and the kernel only 6%.

### Metamath

| | |
|---|---|
| Verify **all of set.mm**: 48,388 theorems, building from the ZFC axioms up to real and complex analysis | **6.9–10.1 s on 1 core** |
| `arisum` (Σk = (n² + n)/2) proof | 387 steps |
| `arisum` with every theorem it depends on, back to the axioms | 4,593 theorems, 245,891 steps |

## What it shows

1. **Search costs far more than checking.** For the automated proofs, the kernel is about 8% of total CPU time (19 of about 246 CPU-s). The other ~92% is tactics and elaboration finding the proof. Written explicitly, the same 1,000 theorems need about **1 CPU-s** of kernel time, against an **86 s** build. That is roughly 100× less wall time, assuming the explicit proofs were already stored. This supports hypothesis **H1** at small scale.
2. **Automation inflates proofs.** `simp` and `omega` produce proof terms about 7× larger, which take about 23× more kernel work. Search makes proofs both slower to find and slower to check.
3. **Even explicit Lean still pays elaboration.** The explicit build still takes 28 s, spent on `rw`, typeclass inference and compiling the definitions, before the ~1 s of real checking.
4. **Re-checking the library every time dominates.** Lean spends 18 s of wall time re-checking `Init` before reaching any user proof. A cache of already-checked results, keyed by content, would remove that cost.
5. **Explicit-proof checkers can be very fast.** Metamath checks a 48k-theorem library built from bare set theory in about 7 s on one core. That is about 7–9× less CPU than nanoda needs for Lean's core library alone, which is smaller and much shallower mathematically.

## Caveats
- This is one small theorem on one laptop with few runs. It's an illustration, not a rigorous benchmark.
- The two systems prove different versions. Metamath's `arisum` works over the complex numbers, built from ZFC. Lean's version uses a recursive `Nat` function on top of Lean's built-in natural numbers. The libraries differ, so compare *trends*, not absolute numbers.
- Profiler categories in Lean are nested and run in parallel, so the percentages are approximate.
- Rocq, Isabelle, Agda and HOL Light were left out because this machine didn't have the disk space (several GB each).

## Reproduce

```bash
export PATH=/path/to/lean-4.36.0/bin:$PATH   # needs lean, leanexport, nanoda_bin
./bench.sh            # N=1000 by default; N=100 ./bench.sh for a quick run
```

Files: [`lean/Sum.lean`](lean/Sum.lean) has the two proofs. [`scripts/gen_lean.py`](scripts/gen_lean.py) generates N copies, and [`scripts/profile_summary.py`](scripts/profile_summary.py) totals Lean's profiler output.

## Next experiments
- **E1/E2 on Mathlib:** profile a full build and time a kernel-only replay. This needs about 20 GB of disk, so a cloud machine.
- **Explicit certificates:** export one Mathlib folder with every unfolding written out, then measure size and checking speed (H2).
- Add Rocq and Isabelle on a machine with more disk, or on GitHub Actions.

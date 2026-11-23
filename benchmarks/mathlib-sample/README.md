# Mathlib sample: where does build time go? (E1/E2)

Tests hypothesis **H1** from [`docs/HYPOTHESES.md`](../../docs/HYPOTHESES.md) on real Mathlib, using only free GitHub Actions runners (4 vCPU, 16 GB RAM). Issue #12.

Run it from the Actions tab, or:

```bash
gh workflow run mathlib-sample.yml -f sample_size=50 -f shards=20 -f seed=12
```

The workflow is [`.github/workflows/mathlib-sample.yml`](../../.github/workflows/mathlib-sample.yml). The report appears in the run summary and in the `mathlib-sample-results` artifact (`results.md`, `results.json`, and every per-module record).

## Results

Committed runs: [`results/results.md`](results/results.md) (seed 12, 50 modules) and [`results/seed23-n100/results.md`](results/seed23-n100/results.md) (seed 23, 100 modules), each with its `results.json`. The summary and the H1 verdict are in [`docs/HYPOTHESES.md`](../../docs/HYPOTHESES.md#evidence-so-far).

## What it does

1. **Pins** Mathlib at tag `v4.36.0` (`fc4f59e5`) with its toolchain, Lean `v4.36.0`.
2. **Samples** modules: the imports of `Mathlib.lean`, sorted, then `random.Random(seed).sample` ([`sample.py`](sample.py)). Module *i* of the sample runs on shard *i* mod *shards*.
3. On each shard, **`lake exe cache get <files>`** downloads only the prebuilt `.olean`s those files need.
4. For each module, [`run_shard.py`](run_shard.py):
   - **E1:** re-elaborates the file with `lean -Dprofiler=true` and Mathlib's `leanOptions`, and keeps Lean's *cumulative profiling times* per category, plus process wall and CPU time. Lean's profiler times are exclusive (a nested category is subtracted from its parent), so the categories add up.
   - **E2, same module:** replays the module's own declarations through Lean's kernel, loading its imports from `.olean`s ([`lean/KernelReplay.lean`](lean/KernelReplay.lean), what `leanchecker` does for one module).
   - **E2, whole closure:** lists the module's own declarations ([`lean/ModuleDecls.lean`](lean/ModuleDecls.lean)), exports them and everything they depend on with `lean4export`, and replays that closure with **nanoda**, with Lean's kernel (`leanchecker --from-export`), and with **Certus** (`certus extract` + `certus check`), recording what Certus rejects as unsupported.
5. [`aggregate.py`](aggregate.py) combines the shards. Shares are ratios of sums over the sampled modules, with 95% percentile-bootstrap intervals (modules resampled, 10,000 times).

Category groups: *kernel* = `type checking`; *typeclass* = `typeclass inference`; *tactics* = `tactic execution`, `simp` and similar; *interpreted meta code* = `interpretation` (Mathlib's own tactics are not precompiled, so they run in the interpreter); *imports* = `import` + `initialization`; *waiting* = `blocked (unaccounted)`; *linting* = every linter; then code generation with `.olean` output, and other elaboration.

## Caveats

- The unit is a module, sampled uniformly, so big and small files count equally in the sample; the ratio-of-sums estimator weights them by time.
- Each file is elaborated once, in a fresh process, on a shared cloud runner. Imports are timed as part of that process, so "imports" is per-file reloading, the **I** of the model. Lean's `blocked (unaccounted)` category is reported as waiting, but it covers only threads waiting inside one file; idle cores across a whole build's dependency chains (the rest of **W**) cannot be seen from one file and are not measured.
- Elaboration runs with Lean's default parallelism (4 threads). Profiler times are summed over threads, so they can exceed wall time.
- Processes are timed by polling every 50 ms, so short steps are only accurate to about 50 ms. The in-process kernel replay times from `KernelReplay.lean` are exact.
- The closure replays check every declaration the module depends on, back to `Init`, while elaboration re-does only the module itself. The like-for-like E2 figure is the same-module replay.

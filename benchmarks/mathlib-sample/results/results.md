# Mathlib sample: where build time goes (E1/E2)

mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` · lean: `v4.36.0` · seed: `12` · sample_size: `50` · runner: `ubuntu-latest, 4 vCPU, 16 GB` · run: `https://github.com/gimbalzero/certus/actions/runs/44948153611`

Modules sampled: **50**, elaborated successfully: **50**. Total re-elaboration: 107 s wall, 158 CPU-s; 174 s across Lean's profiler categories.

## E1: profiler categories (share of profiled time)

| Category | Time (s) | Share, 95% CI |
|---|---:|---|
| Kernel type checking | 8.3 | 4.8% (95% CI 3.6–6.1%, n=50) |
| Typeclass inference | 42.6 | 24.5% (95% CI 11.8–34.3%, n=50) |
| Linting | 4.9 | 2.8% (95% CI 2.4–3.5%, n=50) |
| Blocked waiting on other threads | 18.6 | 10.7% (95% CI 5.8–17.6%, n=50) |
| Tactics and search | 25.8 | 14.8% (95% CI 11.0–19.6%, n=50) |
| Interpreted meta code (Mathlib's own tactics) | 21.9 | 12.6% (95% CI 10.8–15.7%, n=50) |
| Imports and initialization | 26.9 | 15.4% (95% CI 10.2–24.7%, n=50) |
| Code generation and .olean output | 2.4 | 1.4% (95% CI 0.9–2.1%, n=50) |
| Other elaboration | 22.6 | 13.0% (95% CI 8.4–16.5%, n=50) |

- **Kernel share of profiled time: 4.8% (95% CI 3.6–6.1%, n=50)**
- Kernel share excluding imports: 5.6% (95% CI 4.3–7.5%, n=50)
- Kernel time / process CPU time: 5.3% (95% CI 4.0–6.8%, n=50)
- Search (tactics + typeclass + interpreted tactics): 51.9% (95% CI 41.8–58.3%, n=50)

## E2: kernel-only replay

- Lean kernel replay of each module's own declarations, replay only / elaboration wall: 5.7% (95% CI 4.2–7.6%, n=50)
- Same, including loading the module's imports from .olean files / elaboration wall: 70.8% (95% CI 48.8–105.9%, n=50)
- Replay-only time / kernel time in the profiler: 73.6% (95% CI 68.1–79.6%, n=50)
- Dependency closures: 49 exported; median 4942 declarations (max 45959), median export 23 MB
- nanoda, whole closure: 49/49 finished; 83 s wall, 243 CPU-s, vs 106 s elaborating just those modules (closure / module elaboration, wall: 78.0% (95% CI 43.1–134.3%, n=49)); peak RSS 341.6 MB
- Lean kernel (`leanchecker --from-export`), whole closure: 49/49 finished; 367 s wall, 366 CPU-s, vs 106 s elaborating just those modules (closure / module elaboration, wall: 346.0% (95% CI 185.6–607.4%, n=49)); peak RSS 554.5 MB

## Certus

`certus check` on 49 closure certificates: 3 accepted, 46 rejected as unsupported, 0 other failures (timeout or crash).

- 46× `Lean.Syntax: nested inductive types are not supported yet`
- Accepted: `Mathlib.Data.QPF.Multivariate.Constructions.Comp`, `Mathlib.Logic.Function.Conjugate`, `Mathlib.Tactic.SudoSetOption`
- Closures containing at least one nested inductive: 46 of 49

## Verdict

- E1 (fails if kernel share > 50%): **passes**
- H1 (kernel ≤ 10%): **holds (whole 95% interval at or below 10%)**
- E2 (fails if replay > 30% of build), kernel replay alone: **passes**
- E2, replay including each module's import loading (as `leanchecker` does it): **fails**


## Per module

| Module | Lines | Elab wall (s) | Kernel (s) | Kernel % | Replay (s) | nanoda closure (s) | Closure decls | Certus |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Mathlib.Algebra.Algebra.Spectrum.Pi` | 108 | 0.954 | 0.04 | 2.9 | 0.030422 | 0.202 | 2287 | rejected |
| `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric` | 145 | 1.456 | 0.21 | 8.8 | 0.172094 | 1.004 | 3131 | rejected |
| `Mathlib.Algebra.Divisibility.Hom` | 53 | 0.603 | 0.01 | 1.8 | 0.007041 | 0.051 | 431 | rejected |
| `Mathlib.Algebra.Group.Subsemigroup.Membership` | 166 | 0.652 | 0.03 | 3.1 | 0.023124 | 0.051 | 1094 | rejected |
| `Mathlib.Algebra.Module.Opposite` | 50 | 0.502 | 0.01 | 1.0 | 0.005069 | 0.051 | 699 | rejected |
| `Mathlib.Algebra.Order.Archimedean.Defs` | 102 | 0.804 | 0.02 | 1.7 | 0.014867 | 0.104 | 1312 | rejected |
| `Mathlib.Algebra.Order.Floor.Defs` | 413 | 1.005 | 0.05 | 2.7 | 0.038785 | 0.253 | 3229 | rejected |
| `Mathlib.Algebra.Polynomial.Mirror` | 219 | 1.104 | 0.04 | 2.2 | 0.027504 | 0.957 | 7390 | rejected |
| `Mathlib.Algebra.SkewMonoidAlgebra.Lift` | 235 | 1.255 | 0.12 | 6.9 | 0.110772 | 0.457 | 4942 | rejected |
| `Mathlib.Algebra.Star.NonUnitalSubalgebra` | 1303 | 8.129 | 0.96 | 6.8 | 0.682892 | 0.603 | 4825 | rejected |
| `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | 904 | 23.621 | 1.62 | 3.9 | 0.966535 | 1.357 | 7335 | rejected |
| `Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks` | 203 | 5.215 | 0.29 | 3.1 | 0.253381 | 9.94 | 21798 | rejected |
| `Mathlib.Analysis.Calculus.Deriv.Polynomial` | 160 | 1.056 | 0.12 | 7.3 | 0.084164 | 2.059 | 17537 | rejected |
| `Mathlib.Analysis.Normed.Algebra.DualNumber` | 41 | 0.853 | 0.01 | 1.2 | 0.011271 | 0.806 | 9314 | rejected |
| `Mathlib.Analysis.Normed.Operator.Fredholm.Open` | 108 | 1.204 | 0.06 | 3.5 | 0.051688 | 2.81 | 26300 | rejected |
| `Mathlib.Analysis.Polynomial.Fourier` | 114 | 1.409 | 0.12 | 5.3 | 0.090106 | 6.577 | 38909 | rejected |
| `Mathlib.CategoryTheory.Adjunction.Opposites` | 107 | 0.955 | 0.10 | 8.7 | 0.089124 | 0.101 | 839 | rejected |
| `Mathlib.CategoryTheory.Bicategory.Free` | 353 | 4.563 | 0.63 | 9.5 | 0.483495 | 0.303 | 635 | rejected |
| `Mathlib.CategoryTheory.Enriched.FunctorCategory` | 488 | 3.911 | 0.46 | 8.1 | 0.32342 | 0.253 | 1031 | rejected |
| `Mathlib.CategoryTheory.Limits.Shapes.StrongEpi` | 162 | 0.903 | 0.02 | 1.8 | 0.014678 | 0.051 | 578 | rejected |
| `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal` | 119 | 1.454 | 0.05 | 2.5 | 0.039295 | 0.252 | 1942 | rejected |
| `Mathlib.CategoryTheory.Preadditive.Projective.Resolution` | 182 | 1.205 | 0.10 | 6.8 | 0.081852 | 0.353 | 3177 | rejected |
| `Mathlib.CategoryTheory.Subobject.FactorThru` | 212 | 1.105 | 0.05 | 2.7 | 0.031395 | 0.103 | 1006 | rejected |
| `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` | 273 | 2.861 | 0.12 | 2.5 | 0.09931 | 1.008 | 8421 | rejected |
| `Mathlib.Data.Nat.Factorization.Induction` | 132 | 0.954 | 0.01 | 1.3 | 0.011136 | 0.703 | 5850 | rejected |
| `Mathlib.Data.QPF.Multivariate.Constructions.Comp` | 92 | 0.854 | 0.01 | 1.0 | 0.006406 | 0.051 | 102 | ok |
| `Mathlib.GroupTheory.Torsion` | 555 | 1.956 | 0.15 | 5.3 | 0.11845 | 0.803 | 9085 | rejected |
| `Mathlib.LinearAlgebra.TensorProduct.Opposite` | 66 | 1.906 | 0.54 | 20.6 | 0.486362 | 0.703 | 2594 | rejected |
| `Mathlib.Logic.Function.Conjugate` | 191 | 0.587 | 0.01 | 1.0 | 0.005071 | 0.051 | 90 | ok |
| `Mathlib.MeasureTheory.Integral.Gamma` | 145 | 1.808 | 0.15 | 4.6 | 0.101575 | 12.537 | 45959 | rejected |
| `Mathlib.NumberTheory.Height.Northcott` | 41 | 0.755 | 0.00 | 0.1 | 0.000582 | 1.607 | 15430 | rejected |
| `Mathlib.NumberTheory.NumberField.FiniteAdeleRing` | 139 | 2.459 | 0.12 | 2.2 | 0.08553 | 7.123 | 36588 | rejected |
| `Mathlib.Order.Category.Preord` | 174 | 1.104 | 0.06 | 3.9 | 0.038898 | 2.808 | 9785 | rejected |
| `Mathlib.Order.Extension.Linear` | 96 | 0.602 | 0.01 | 1.7 | 0.009706 | 0.151 | 1596 | rejected |
| `Mathlib.Probability.Decision.Risk.Defs` | 140 | 1.154 | 0.02 | 0.9 | 0.011827 | 2.108 | 18596 | rejected |
| `Mathlib.Probability.Kernel.Defs` | 411 | 1.206 | 0.07 | 3.5 | 0.044978 | 1.557 | 18985 | rejected |
| `Mathlib.RingTheory.Etale.StandardEtale` | 449 | 8.527 | 1.42 | 9.4 | 1.097496 | 7.074 | 21005 | rejected |
| `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring` | 137 | 1.405 | 0.09 | 4.1 | 0.067952 | 0.606 | 4824 | rejected |
| `Mathlib.RingTheory.HahnSeries.Cardinal` | 216 | 4.563 | 0.09 | 1.0 | 0.06994 | 1.307 | 10688 | rejected |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | 309 | 2.292 | 0.15 | 3.0 | 0.100919 | 4.018 | 23008 | rejected |
| `Mathlib.RingTheory.PowerSeries.WellKnown` | 216 | 1.154 | 0.07 | 3.1 | 0.04896 | 0.804 | 7410 | rejected |
| `Mathlib.Tactic.ArithMult.Init` | 19 | 0.453 | 0.00 | 0.0 | 0.000285 | – | – | – |
| `Mathlib.Tactic.Hessenberg.Reduce` | 83 | 0.402 | 0.00 | 0.6 | 0.00195 | 0.152 | 2492 | rejected |
| `Mathlib.Tactic.Linter.TextBased` | 598 | 1.104 | 0.04 | 2.3 | 0.028781 | 2.812 | 7038 | rejected |
| `Mathlib.Tactic.NormNum.DivMod` | 183 | 1.306 | 0.02 | 1.4 | 0.015459 | 2.607 | 8681 | rejected |
| `Mathlib.Tactic.SudoSetOption` | 59 | 0.403 | 0.00 | 0.5 | 0.002077 | 0.051 | 272 | ok |
| `Mathlib.Topology.DerivedSet` | 131 | 0.803 | 0.01 | 1.1 | 0.008599 | 0.151 | 2175 | rejected |
| `Mathlib.Topology.Hom.Open` | 155 | 0.703 | 0.02 | 2.2 | 0.012133 | 0.051 | 442 | rejected |
| `Mathlib.Topology.MetricSpace.CantorScheme` | 187 | 1.005 | 0.02 | 1.3 | 0.013386 | 1.154 | 10625 | rejected |
| `Mathlib.Util.DischargerAsTactic` | 36 | 0.403 | 0.00 | 0.2 | 0.001164 | 2.16 | 7799 | rejected |

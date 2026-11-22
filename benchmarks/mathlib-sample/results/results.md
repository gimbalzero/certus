# Mathlib sample: where build time goes (E1/E2)

mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` · lean: `v4.36.0` · seed: `12` · sample_size: `50` · runner: `ubuntu-latest, 4 vCPU, 16 GB` · run: `https://github.com/gimbalzero/certus/actions/runs/44998000065`

Modules sampled: **50**, elaborated successfully: **50**. Total re-elaboration: 92 s wall, 134 CPU-s; 150 s across Lean's profiler categories.

## E1: profiler categories (share of profiled time)

| Category | Time (s) | Share, 95% CI |
|---|---:|---|
| Kernel type checking | 7.5 | 5.0% (95% CI 3.7–6.3%, n=50) |
| Typeclass inference | 28.7 | 19.2% (95% CI 11.6–26.1%, n=50) |
| Linting | 4.7 | 3.2% (95% CI 2.7–3.7%, n=50) |
| Blocked waiting on other threads | 17.6 | 11.8% (95% CI 7.3–17.2%, n=50) |
| Tactics and search | 21.6 | 14.4% (95% CI 11.1–18.1%, n=50) |
| Interpreted meta code (Mathlib's own tactics) | 20.0 | 13.3% (95% CI 11.6–15.8%, n=50) |
| Imports and initialization | 27.5 | 18.3% (95% CI 13.3–25.7%, n=50) |
| Code generation and .olean output | 2.6 | 1.7% (95% CI 1.1–2.6%, n=50) |
| Other elaboration | 19.5 | 13.1% (95% CI 8.7–16.8%, n=50) |

- **Kernel share of profiled time: 5.0% (95% CI 3.7–6.3%, n=50)**
- Kernel share excluding imports: 6.1% (95% CI 4.7–7.7%, n=50)
- Kernel time / process CPU time: 5.6% (95% CI 4.3–7.0%, n=50)
- Search (tactics + typeclass + interpreted tactics): 46.9% (95% CI 40.6–51.7%, n=50)

## E2: kernel-only replay

- Lean kernel replay of each module's own declarations, replay only / elaboration wall: 5.9% (95% CI 4.3–7.5%, n=50)
- Same, including loading the module's imports from .olean files / elaboration wall: 82.2% (95% CI 63.2–108.2%, n=50)
- Replay-only time / kernel time in the profiler: 71.8% (95% CI 66.7–77.0%, n=50)
- Dependency closures: 49 exported; median 4942 declarations (max 45959), median export 23 MB
- nanoda, whole closure: 49/49 finished; 83 s wall, 241 CPU-s, vs 91 s elaborating just those modules (closure / module elaboration, wall: 91.3% (95% CI 55.1–140.0%, n=49)); peak RSS 346.1 MB
- Lean kernel (`leanchecker --from-export`), whole closure: 49/49 finished; 368 s wall, 367 CPU-s, vs 91 s elaborating just those modules (closure / module elaboration, wall: 402.9% (95% CI 240.3–626.5%, n=49)); peak RSS 554.7 MB

## Certus

`certus check` on 49 closure certificates: 49 accepted, 0 rejected as unsupported, 0 other failures (timeout or crash).

- Accepted: `Mathlib.Algebra.Algebra.Spectrum.Pi`, `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric`, `Mathlib.Algebra.Divisibility.Hom`, `Mathlib.Algebra.Group.Subsemigroup.Membership`, `Mathlib.Algebra.Module.Opposite`, `Mathlib.Algebra.Order.Archimedean.Defs`, `Mathlib.Algebra.Order.Floor.Defs`, `Mathlib.Algebra.Polynomial.Mirror`, `Mathlib.Algebra.SkewMonoidAlgebra.Lift`, `Mathlib.Algebra.Star.NonUnitalSubalgebra`, `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula`, `Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks`, `Mathlib.Analysis.Calculus.Deriv.Polynomial`, `Mathlib.Analysis.Normed.Algebra.DualNumber`, `Mathlib.Analysis.Normed.Operator.Fredholm.Open`, `Mathlib.Analysis.Polynomial.Fourier`, `Mathlib.CategoryTheory.Adjunction.Opposites`, `Mathlib.CategoryTheory.Bicategory.Free`, `Mathlib.CategoryTheory.Enriched.FunctorCategory`, `Mathlib.CategoryTheory.Limits.Shapes.StrongEpi`, `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal`, `Mathlib.CategoryTheory.Preadditive.Projective.Resolution`, `Mathlib.CategoryTheory.Subobject.FactorThru`, `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`, `Mathlib.Data.Nat.Factorization.Induction`, `Mathlib.Data.QPF.Multivariate.Constructions.Comp`, `Mathlib.GroupTheory.Torsion`, `Mathlib.LinearAlgebra.TensorProduct.Opposite`, `Mathlib.Logic.Function.Conjugate`, `Mathlib.MeasureTheory.Integral.Gamma`, `Mathlib.NumberTheory.Height.Northcott`, `Mathlib.NumberTheory.NumberField.FiniteAdeleRing`, `Mathlib.Order.Category.Preord`, `Mathlib.Order.Extension.Linear`, `Mathlib.Probability.Decision.Risk.Defs`, `Mathlib.Probability.Kernel.Defs`, `Mathlib.RingTheory.Etale.StandardEtale`, `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring`, `Mathlib.RingTheory.HahnSeries.Cardinal`, `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval`, `Mathlib.RingTheory.PowerSeries.WellKnown`, `Mathlib.Tactic.Hessenberg.Reduce`, `Mathlib.Tactic.Linter.TextBased`, `Mathlib.Tactic.NormNum.DivMod`, `Mathlib.Tactic.SudoSetOption`, `Mathlib.Topology.DerivedSet`, `Mathlib.Topology.Hom.Open`, `Mathlib.Topology.MetricSpace.CantorScheme`, `Mathlib.Util.DischargerAsTactic`
- Closures containing at least one nested inductive: 46 of 49

## Verdict

- E1 (fails if kernel share > 50%): **passes**
- H1 (kernel ≤ 10%): **holds (whole 95% interval at or below 10%)**
- E2 (fails if replay > 30% of build), kernel replay alone: **passes**
- E2, replay including each module's import loading (as `leanchecker` does it): **fails**


## Per module

| Module | Lines | Elab wall (s) | Kernel (s) | Kernel % | Replay (s) | nanoda closure (s) | Closure decls | Certus |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Mathlib.Algebra.Algebra.Spectrum.Pi` | 108 | 0.906 | 0.04 | 2.9 | 0.025835 | 0.152 | 2287 | ok |
| `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric` | 145 | 1.707 | 0.24 | 8.5 | 0.18086 | 0.957 | 3142 | ok |
| `Mathlib.Algebra.Divisibility.Hom` | 53 | 0.703 | 0.01 | 1.3 | 0.007152 | 0.051 | 460 | ok |
| `Mathlib.Algebra.Group.Subsemigroup.Membership` | 166 | 0.853 | 0.03 | 2.6 | 0.024263 | 0.102 | 1115 | ok |
| `Mathlib.Algebra.Module.Opposite` | 50 | 0.602 | 0.01 | 1.1 | 0.006285 | 0.051 | 727 | ok |
| `Mathlib.Algebra.Order.Archimedean.Defs` | 102 | 0.804 | 0.02 | 1.5 | 0.015312 | 0.102 | 1332 | ok |
| `Mathlib.Algebra.Order.Floor.Defs` | 413 | 1.305 | 0.06 | 2.5 | 0.039034 | 0.302 | 3229 | ok |
| `Mathlib.Algebra.Polynomial.Mirror` | 219 | 0.804 | 0.03 | 2.3 | 0.022672 | 0.656 | 7390 | ok |
| `Mathlib.Algebra.SkewMonoidAlgebra.Lift` | 235 | 1.757 | 0.16 | 6.3 | 0.137096 | 0.554 | 4942 | ok |
| `Mathlib.Algebra.Star.NonUnitalSubalgebra` | 1303 | 5.169 | 0.73 | 8.0 | 0.524378 | 0.455 | 4825 | ok |
| `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | 904 | 13.15 | 1.28 | 5.1 | 0.738488 | 1.004 | 7335 | ok |
| `Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks` | 203 | 4.261 | 0.23 | 3.1 | 0.202887 | 7.978 | 21798 | ok |
| `Mathlib.Analysis.Calculus.Deriv.Polynomial` | 160 | 1.557 | 0.16 | 6.6 | 0.106443 | 2.761 | 17537 | ok |
| `Mathlib.Analysis.Normed.Algebra.DualNumber` | 41 | 0.953 | 0.01 | 1.3 | 0.014245 | 1.004 | 9314 | ok |
| `Mathlib.Analysis.Normed.Operator.Fredholm.Open` | 108 | 1.778 | 0.11 | 4.0 | 0.079112 | 4.615 | 26300 | ok |
| `Mathlib.Analysis.Polynomial.Fourier` | 114 | 1.857 | 0.15 | 4.7 | 0.109425 | 9.381 | 38909 | ok |
| `Mathlib.CategoryTheory.Adjunction.Opposites` | 107 | 0.954 | 0.10 | 8.8 | 0.092914 | 0.102 | 861 | ok |
| `Mathlib.CategoryTheory.Bicategory.Free` | 353 | 4.363 | 0.70 | 10.6 | 0.472254 | 0.251 | 658 | ok |
| `Mathlib.CategoryTheory.Enriched.FunctorCategory` | 488 | 3.812 | 0.44 | 8.0 | 0.323418 | 0.252 | 1052 | ok |
| `Mathlib.CategoryTheory.Limits.Shapes.StrongEpi` | 162 | 0.702 | 0.01 | 1.7 | 0.009281 | 0.051 | 599 | ok |
| `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal` | 119 | 1.755 | 0.06 | 2.4 | 0.04935 | 0.304 | 1963 | ok |
| `Mathlib.CategoryTheory.Preadditive.Projective.Resolution` | 182 | 1.606 | 0.16 | 7.5 | 0.10389 | 0.453 | 3177 | ok |
| `Mathlib.CategoryTheory.Subobject.FactorThru` | 212 | 0.802 | 0.03 | 2.6 | 0.020909 | 0.102 | 1029 | ok |
| `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` | 273 | 2.96 | 0.13 | 2.7 | 0.103495 | 1.056 | 8421 | ok |
| `Mathlib.Data.Nat.Factorization.Induction` | 132 | 0.703 | 0.01 | 1.4 | 0.009126 | 0.504 | 5850 | ok |
| `Mathlib.Data.QPF.Multivariate.Constructions.Comp` | 92 | 0.653 | 0.01 | 1.0 | 0.004337 | 0.051 | 102 | ok |
| `Mathlib.GroupTheory.Torsion` | 555 | 1.905 | 0.14 | 5.1 | 0.119533 | 0.802 | 9085 | ok |
| `Mathlib.LinearAlgebra.TensorProduct.Opposite` | 66 | 1.355 | 0.45 | 23.2 | 0.382487 | 0.558 | 2605 | ok |
| `Mathlib.Logic.Function.Conjugate` | 191 | 0.506 | 0.01 | 1.2 | 0.005247 | 0.051 | 90 | ok |
| `Mathlib.MeasureTheory.Integral.Gamma` | 145 | 1.357 | 0.11 | 4.5 | 0.082109 | 9.425 | 45959 | ok |
| `Mathlib.NumberTheory.Height.Northcott` | 41 | 0.954 | 0.00 | 0.1 | 0.000628 | 2.111 | 15430 | ok |
| `Mathlib.NumberTheory.NumberField.FiniteAdeleRing` | 139 | 3.23 | 0.14 | 2.0 | 0.085481 | 9.194 | 36588 | ok |
| `Mathlib.Order.Category.Preord` | 174 | 0.954 | 0.04 | 3.6 | 0.029014 | 2.106 | 9785 | ok |
| `Mathlib.Order.Extension.Linear` | 96 | 0.702 | 0.01 | 1.6 | 0.010093 | 0.152 | 1596 | ok |
| `Mathlib.Probability.Decision.Risk.Defs` | 140 | 1.308 | 0.02 | 0.8 | 0.014716 | 2.362 | 18596 | ok |
| `Mathlib.Probability.Kernel.Defs` | 411 | 1.96 | 0.12 | 3.7 | 0.074327 | 3.113 | 18985 | ok |
| `Mathlib.RingTheory.Etale.StandardEtale` | 449 | 5.72 | 1.06 | 10.4 | 0.817306 | 5.116 | 21005 | ok |
| `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring` | 137 | 0.954 | 0.06 | 4.5 | 0.052842 | 0.453 | 4824 | ok |
| `Mathlib.RingTheory.HahnSeries.Cardinal` | 216 | 4.215 | 0.11 | 1.4 | 0.075712 | 1.616 | 10688 | ok |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | 309 | 1.86 | 0.12 | 3.1 | 0.087172 | 3.064 | 23008 | ok |
| `Mathlib.RingTheory.PowerSeries.WellKnown` | 216 | 1.054 | 0.06 | 3.4 | 0.038122 | 0.652 | 7410 | ok |
| `Mathlib.Tactic.ArithMult.Init` | 19 | 0.402 | 0.00 | 0.0 | 0.000301 | – | – | – |
| `Mathlib.Tactic.Hessenberg.Reduce` | 83 | 0.602 | 0.00 | 0.6 | 0.002862 | 0.302 | 2492 | ok |
| `Mathlib.Tactic.Linter.TextBased` | 598 | 1.406 | 0.05 | 2.3 | 0.035671 | 2.763 | 7038 | ok |
| `Mathlib.Tactic.NormNum.DivMod` | 183 | 1.003 | 0.02 | 1.4 | 0.016213 | 2.258 | 8681 | ok |
| `Mathlib.Tactic.SudoSetOption` | 59 | 0.503 | 0.00 | 0.5 | 0.002536 | 0.051 | 301 | ok |
| `Mathlib.Topology.DerivedSet` | 131 | 0.955 | 0.02 | 1.1 | 0.010848 | 0.153 | 2175 | ok |
| `Mathlib.Topology.Hom.Open` | 155 | 0.903 | 0.02 | 1.9 | 0.014811 | 0.051 | 469 | ok |
| `Mathlib.Topology.MetricSpace.CantorScheme` | 187 | 1.104 | 0.02 | 1.3 | 0.016197 | 1.304 | 10625 | ok |
| `Mathlib.Util.DischargerAsTactic` | 36 | 0.403 | 0.00 | 0.3 | 0.001239 | 2.51 | 7799 | ok |

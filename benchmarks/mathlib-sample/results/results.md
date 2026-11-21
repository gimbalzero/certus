# Mathlib sample: where build time goes (E1/E2)

mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` · lean: `v4.36.0` · seed: `12` · sample_size: `50` · runner: `ubuntu-latest, 4 vCPU, 16 GB` · run: `https://github.com/gimbalzero/certus/actions/runs/44949174171`

Modules sampled: **50**, elaborated successfully: **50**. Total re-elaboration: 103 s wall, 154 CPU-s; 166 s across Lean's profiler categories.

## E1: profiler categories (share of profiled time)

| Category | Time (s) | Share, 95% CI |
|---|---:|---|
| Kernel type checking | 8.3 | 5.0% (95% CI 3.8–6.5%, n=50) |
| Typeclass inference | 41.8 | 25.2% (95% CI 11.2–35.4%, n=50) |
| Linting | 4.8 | 2.9% (95% CI 2.4–3.7%, n=50) |
| Blocked waiting on other threads | 14.3 | 8.6% (95% CI 4.9–14.0%, n=50) |
| Tactics and search | 23.4 | 14.1% (95% CI 10.7–18.8%, n=50) |
| Interpreted meta code (Mathlib's own tactics) | 21.0 | 12.7% (95% CI 10.8–16.0%, n=50) |
| Imports and initialization | 27.8 | 16.7% (95% CI 10.7–27.4%, n=50) |
| Code generation and .olean output | 2.4 | 1.5% (95% CI 1.0–2.2%, n=50) |
| Other elaboration | 22.0 | 13.3% (95% CI 8.9–16.4%, n=50) |

- **Kernel share of profiled time: 5.0% (95% CI 3.8–6.5%, n=50)**
- Kernel share excluding imports: 6.0% (95% CI 4.6–8.1%, n=50)
- Kernel time / process CPU time: 5.4% (95% CI 4.1–7.1%, n=50)
- Search (tactics + typeclass + interpreted tactics): 52.0% (95% CI 40.2–59.2%, n=50)

## E2: kernel-only replay

- Lean kernel replay of each module's own declarations, replay only / elaboration wall: 5.9% (95% CI 4.2–7.9%, n=50)
- Same, including loading the module's imports from .olean files / elaboration wall: 72.5% (95% CI 49.0–110.2%, n=50)
- Replay-only time / kernel time in the profiler: 72.8% (95% CI 67.3–79.7%, n=50)
- Dependency closures: 49 exported; median 4942 declarations (max 45959), median export 23 MB
- nanoda, whole closure: 49/49 finished; 86 s wall, 248 CPU-s, vs 102 s elaborating just those modules (closure / module elaboration, wall: 84.4% (95% CI 45.4–147.9%, n=49)); peak RSS 351.0 MB
- Lean kernel (`leanchecker --from-export`), whole closure: 49/49 finished; 383 s wall, 382 CPU-s, vs 102 s elaborating just those modules (closure / module elaboration, wall: 375.2% (95% CI 198.6–666.0%, n=49)); peak RSS 554.7 MB

## Certus

`certus check` on 49 closure certificates: 44 accepted, 5 rejected as unsupported, 0 other failures (timeout or crash).

- 4× `String.toByteArray_empty: string literal needs String.mk, Char.ofNat, List.nil and List.cons`
- 1× `CategoryTheory.Presieve.map: inductive type: wrong number of indices`
- Accepted: `Mathlib.Algebra.Algebra.Spectrum.Pi`, `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric`, `Mathlib.Algebra.Divisibility.Hom`, `Mathlib.Algebra.Group.Subsemigroup.Membership`, `Mathlib.Algebra.Module.Opposite`, `Mathlib.Algebra.Order.Archimedean.Defs`, `Mathlib.Algebra.Order.Floor.Defs`, `Mathlib.Algebra.Polynomial.Mirror`, `Mathlib.Algebra.SkewMonoidAlgebra.Lift`, `Mathlib.Algebra.Star.NonUnitalSubalgebra`, `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula`, `Mathlib.Analysis.Calculus.Deriv.Polynomial`, `Mathlib.Analysis.Normed.Algebra.DualNumber`, `Mathlib.Analysis.Normed.Operator.Fredholm.Open`, `Mathlib.Analysis.Polynomial.Fourier`, `Mathlib.CategoryTheory.Adjunction.Opposites`, `Mathlib.CategoryTheory.Bicategory.Free`, `Mathlib.CategoryTheory.Enriched.FunctorCategory`, `Mathlib.CategoryTheory.Limits.Shapes.StrongEpi`, `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal`, `Mathlib.CategoryTheory.Preadditive.Projective.Resolution`, `Mathlib.CategoryTheory.Subobject.FactorThru`, `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`, `Mathlib.Data.Nat.Factorization.Induction`, `Mathlib.Data.QPF.Multivariate.Constructions.Comp`, `Mathlib.GroupTheory.Torsion`, `Mathlib.LinearAlgebra.TensorProduct.Opposite`, `Mathlib.Logic.Function.Conjugate`, `Mathlib.MeasureTheory.Integral.Gamma`, `Mathlib.NumberTheory.Height.Northcott`, `Mathlib.NumberTheory.NumberField.FiniteAdeleRing`, `Mathlib.Order.Extension.Linear`, `Mathlib.Probability.Decision.Risk.Defs`, `Mathlib.Probability.Kernel.Defs`, `Mathlib.RingTheory.Etale.StandardEtale`, `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring`, `Mathlib.RingTheory.HahnSeries.Cardinal`, `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval`, `Mathlib.RingTheory.PowerSeries.WellKnown`, `Mathlib.Tactic.Hessenberg.Reduce`, `Mathlib.Tactic.SudoSetOption`, `Mathlib.Topology.DerivedSet`, `Mathlib.Topology.Hom.Open`, `Mathlib.Topology.MetricSpace.CantorScheme`
- Closures containing at least one nested inductive: 46 of 49

## Verdict

- E1 (fails if kernel share > 50%): **passes**
- H1 (kernel ≤ 10%): **holds (whole 95% interval at or below 10%)**
- E2 (fails if replay > 30% of build), kernel replay alone: **passes**
- E2, replay including each module's import loading (as `leanchecker` does it): **fails**


## Per module

| Module | Lines | Elab wall (s) | Kernel (s) | Kernel % | Replay (s) | nanoda closure (s) | Closure decls | Certus |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Mathlib.Algebra.Algebra.Spectrum.Pi` | 108 | 1.005 | 0.05 | 3.5 | 0.040912 | 0.202 | 2287 | ok |
| `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric` | 145 | 1.306 | 0.17 | 8.2 | 0.13597 | 0.803 | 3131 | ok |
| `Mathlib.Algebra.Divisibility.Hom` | 53 | 0.602 | 0.01 | 1.2 | 0.005697 | 0.051 | 431 | ok |
| `Mathlib.Algebra.Group.Subsemigroup.Membership` | 166 | 0.853 | 0.03 | 2.6 | 0.024611 | 0.103 | 1094 | ok |
| `Mathlib.Algebra.Module.Opposite` | 50 | 0.552 | 0.01 | 1.0 | 0.005169 | 0.051 | 699 | ok |
| `Mathlib.Algebra.Order.Archimedean.Defs` | 102 | 0.603 | 0.01 | 1.7 | 0.011544 | 0.103 | 1312 | ok |
| `Mathlib.Algebra.Order.Floor.Defs` | 413 | 1.307 | 0.07 | 2.6 | 0.039268 | 0.251 | 3229 | ok |
| `Mathlib.Algebra.Polynomial.Mirror` | 219 | 1.104 | 0.04 | 2.2 | 0.027373 | 0.906 | 7390 | ok |
| `Mathlib.Algebra.SkewMonoidAlgebra.Lift` | 235 | 1.755 | 0.16 | 6.2 | 0.137538 | 0.602 | 4942 | ok |
| `Mathlib.Algebra.Star.NonUnitalSubalgebra` | 1303 | 8.026 | 0.95 | 6.8 | 0.68947 | 0.606 | 4825 | ok |
| `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | 904 | 24.131 | 1.65 | 4.0 | 0.98048 | 1.356 | 7335 | ok |
| `Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks` | 203 | 3.257 | 0.18 | 3.2 | 0.161572 | 7.026 | 21798 | rejected |
| `Mathlib.Analysis.Calculus.Deriv.Polynomial` | 160 | 1.706 | 0.18 | 6.7 | 0.11329 | 3.064 | 17537 | ok |
| `Mathlib.Analysis.Normed.Algebra.DualNumber` | 41 | 1.304 | 0.01 | 1.0 | 0.014091 | 1.156 | 9314 | ok |
| `Mathlib.Analysis.Normed.Operator.Fredholm.Open` | 108 | 1.255 | 0.06 | 3.6 | 0.049026 | 2.756 | 26300 | ok |
| `Mathlib.Analysis.Polynomial.Fourier` | 114 | 2.058 | 0.15 | 4.5 | 0.124782 | 9.577 | 38909 | ok |
| `Mathlib.CategoryTheory.Adjunction.Opposites` | 107 | 0.805 | 0.11 | 10.6 | 0.087541 | 0.101 | 839 | ok |
| `Mathlib.CategoryTheory.Bicategory.Free` | 353 | 3.56 | 0.50 | 9.6 | 0.358184 | 0.252 | 635 | ok |
| `Mathlib.CategoryTheory.Enriched.FunctorCategory` | 488 | 2.757 | 0.32 | 8.0 | 0.254141 | 0.201 | 1031 | ok |
| `Mathlib.CategoryTheory.Limits.Shapes.StrongEpi` | 162 | 0.702 | 0.02 | 2.1 | 0.013077 | 0.051 | 578 | ok |
| `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal` | 119 | 1.354 | 0.05 | 2.6 | 0.038762 | 0.252 | 1942 | ok |
| `Mathlib.CategoryTheory.Preadditive.Projective.Resolution` | 182 | 1.355 | 0.11 | 6.7 | 0.084721 | 0.352 | 3177 | ok |
| `Mathlib.CategoryTheory.Subobject.FactorThru` | 212 | 0.804 | 0.04 | 3.2 | 0.02779 | 0.101 | 1006 | ok |
| `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` | 273 | 1.813 | 0.09 | 3.0 | 0.066007 | 0.754 | 8421 | ok |
| `Mathlib.Data.Nat.Factorization.Induction` | 132 | 0.904 | 0.01 | 1.4 | 0.011232 | 0.703 | 5850 | ok |
| `Mathlib.Data.QPF.Multivariate.Constructions.Comp` | 92 | 0.606 | 0.01 | 1.2 | 0.005909 | 0.051 | 102 | ok |
| `Mathlib.GroupTheory.Torsion` | 555 | 1.755 | 0.15 | 5.9 | 0.121222 | 0.755 | 9085 | ok |
| `Mathlib.LinearAlgebra.TensorProduct.Opposite` | 66 | 2.107 | 0.60 | 20.6 | 0.564082 | 0.755 | 2594 | ok |
| `Mathlib.Logic.Function.Conjugate` | 191 | 0.453 | 0.01 | 1.0 | 0.004055 | 0.051 | 90 | ok |
| `Mathlib.MeasureTheory.Integral.Gamma` | 145 | 2.061 | 0.17 | 4.4 | 0.112272 | 13.499 | 45959 | ok |
| `Mathlib.NumberTheory.Height.Northcott` | 41 | 1.205 | 0.00 | 0.0 | 0.00063 | 2.615 | 15430 | ok |
| `Mathlib.NumberTheory.NumberField.FiniteAdeleRing` | 139 | 2.985 | 0.12 | 2.0 | 0.084324 | 8.529 | 36588 | ok |
| `Mathlib.Order.Category.Preord` | 174 | 1.057 | 0.05 | 3.9 | 0.038289 | 2.761 | 9785 | rejected |
| `Mathlib.Order.Extension.Linear` | 96 | 0.552 | 0.01 | 1.5 | 0.007823 | 0.101 | 1596 | ok |
| `Mathlib.Probability.Decision.Risk.Defs` | 140 | 1.004 | 0.01 | 0.9 | 0.009984 | 1.758 | 18596 | ok |
| `Mathlib.Probability.Kernel.Defs` | 411 | 1.204 | 0.07 | 3.6 | 0.048261 | 1.809 | 18985 | ok |
| `Mathlib.RingTheory.Etale.StandardEtale` | 449 | 9.332 | 1.62 | 9.8 | 1.186734 | 7.522 | 21005 | ok |
| `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring` | 137 | 1.154 | 0.08 | 4.6 | 0.068097 | 0.605 | 4824 | ok |
| `Mathlib.RingTheory.HahnSeries.Cardinal` | 216 | 2.106 | 0.06 | 1.4 | 0.044425 | 0.853 | 10688 | ok |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | 309 | 2.208 | 0.15 | 3.3 | 0.114344 | 4.319 | 23008 | ok |
| `Mathlib.RingTheory.PowerSeries.WellKnown` | 216 | 1.205 | 0.09 | 3.5 | 0.062281 | 0.958 | 7410 | ok |
| `Mathlib.Tactic.ArithMult.Init` | 19 | 0.352 | 0.00 | 0.0 | 0.000305 | – | – | – |
| `Mathlib.Tactic.Hessenberg.Reduce` | 83 | 0.402 | 0.00 | 0.6 | 0.002119 | 0.153 | 2492 | ok |
| `Mathlib.Tactic.Linter.TextBased` | 598 | 1.056 | 0.04 | 2.4 | 0.027686 | 2.106 | 7038 | rejected |
| `Mathlib.Tactic.NormNum.DivMod` | 183 | 1.255 | 0.02 | 1.3 | 0.014633 | 2.658 | 8681 | rejected |
| `Mathlib.Tactic.SudoSetOption` | 59 | 0.554 | 0.00 | 0.5 | 0.002417 | 0.051 | 272 | ok |
| `Mathlib.Topology.DerivedSet` | 131 | 0.752 | 0.01 | 1.1 | 0.00865 | 0.151 | 2175 | ok |
| `Mathlib.Topology.Hom.Open` | 155 | 0.904 | 0.02 | 2.0 | 0.014987 | 0.051 | 442 | ok |
| `Mathlib.Topology.MetricSpace.CantorScheme` | 187 | 0.954 | 0.01 | 1.2 | 0.012303 | 0.904 | 10625 | ok |
| `Mathlib.Util.DischargerAsTactic` | 36 | 0.403 | 0.00 | 0.2 | 0.001181 | 1.86 | 7799 | rejected |

# Mathlib sample: where build time goes (E1/E2)

mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` · lean: `v4.36.0` · seed: `23` · sample_size: `100` · runner: `ubuntu-latest, 4 vCPU, 16 GB` · run: `https://github.com/gimbalzero/certus/actions/runs/45089250507`

Modules sampled: **100**, elaborated successfully: **100**. Total re-elaboration: 164 s wall, 255 CPU-s; 285 s across Lean's profiler categories.

## E1: profiler categories (share of profiled time)

| Category | Time (s) | Share, 95% CI |
|---|---:|---|
| Kernel type checking | 14.6 | 5.1% (95% CI 3.8–6.7%, n=100) |
| Typeclass inference | 48.3 | 17.0% (95% CI 14.0–19.6%, n=100) |
| Linting | 9.1 | 3.2% (95% CI 2.8–3.6%, n=100) |
| Blocked waiting on other threads | 35.0 | 12.3% (95% CI 8.8–16.0%, n=100) |
| Tactics and search | 44.5 | 15.6% (95% CI 13.4–17.7%, n=100) |
| Interpreted meta code (Mathlib's own tactics) | 43.1 | 15.1% (95% CI 13.4–17.0%, n=100) |
| Imports and initialization | 55.0 | 19.3% (95% CI 16.6–22.6%, n=100) |
| Code generation and .olean output | 4.0 | 1.4% (95% CI 1.1–1.8%, n=100) |
| Other elaboration | 31.3 | 11.0% (95% CI 8.8–13.5%, n=100) |

- **Kernel share of profiled time: 5.1% (95% CI 3.8–6.7%, n=100)**
- Kernel share excluding imports: 6.4% (95% CI 4.7–8.3%, n=100)
- Kernel time / process CPU time: 5.7% (95% CI 4.3–7.4%, n=100)
- Search (tactics + typeclass + interpreted tactics): 47.7% (95% CI 45.1–49.9%, n=100)

## E2: kernel-only replay

- Lean kernel replay of each module's own declarations, replay only / elaboration wall: 6.7% (95% CI 5.0–8.8%, n=100)
- Same, including loading the module's imports from .olean files / elaboration wall: 95.4% (95% CI 86.8–105.3%, n=100)
- Replay-only time / kernel time in the profiler: 75.1% (95% CI 72.8–77.7%, n=100)
- Dependency closures: 98 exported; median 6419.5 declarations (max 53809), median export 31 MB
- nanoda, whole closure: 98/98 finished; 222 s wall, 658 CPU-s, vs 163 s elaborating just those modules (closure / module elaboration, wall: 136.4% (95% CI 100.7–175.8%, n=98)); peak RSS 427.6 MB
- Lean kernel (`leanchecker --from-export`), whole closure: 98/98 finished; 1022 s wall, 1019 CPU-s, vs 163 s elaborating just those modules (closure / module elaboration, wall: 626.7% (95% CI 449.5–824.3%, n=98)); peak RSS 980.4 MB

## Certus

`certus check` on 98 closure certificates: 98 accepted, 0 rejected as unsupported, 0 other failures (timeout or crash).

- Accepted: `Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, `Mathlib.Algebra.Category.Ring.Basic`, `Mathlib.Algebra.CharP.LocalRing`, `Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries`, `Mathlib.Algebra.Field.GeomSum`, `Mathlib.Algebra.Group.Commute.Basic`, `Mathlib.Algebra.Group.Graph`, `Mathlib.Algebra.GroupWithZero.Opposite`, `Mathlib.Algebra.Homology.Additive`, `Mathlib.Algebra.Homology.DerivedCategory.Fractions`, `Mathlib.Algebra.Homology.Embedding.TruncLEHomology`, `Mathlib.Algebra.MvPolynomial.Derivation`, `Mathlib.Algebra.MvPolynomial.Variables`, `Mathlib.Algebra.Notation.Indicator`, `Mathlib.Algebra.PresentedMonoid.Basic`, `Mathlib.Algebra.Ring.TransferInstance`, `Mathlib.Algebra.Star.MonoidHom`, `Mathlib.AlgebraicGeometry.Artinian`, `Mathlib.AlgebraicGeometry.Birational.Birational`, `Mathlib.AlgebraicGeometry.Over`, `Mathlib.AlgebraicGeometry.Sites.BigZariski`, `Mathlib.AlgebraicTopology.SimplexCategory.Truncated`, `Mathlib.AlgebraicTopology.SimplicialSet.CompStruct`, `Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex`, `Mathlib.Analysis.Asymptotics.Prod`, `Mathlib.Analysis.CStarAlgebra.ApproximateUnit`, `Mathlib.Analysis.CStarAlgebra.Hom`, `Mathlib.Analysis.Calculus.FDeriv.Norm`, `Mathlib.Analysis.Complex.IsIntegral`, `Mathlib.Analysis.InnerProductSpace.Orthogonal`, `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap`, `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`, `Mathlib.CategoryTheory.Adjunction.Reflective`, `Mathlib.CategoryTheory.Bicategory.Functor.Cat`, `Mathlib.CategoryTheory.Center.Localization`, `Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic`, `Mathlib.CategoryTheory.Equivalence.Symmetry`, `Mathlib.CategoryTheory.Generator.StrongGenerator`, `Mathlib.CategoryTheory.Groupoid.FreeGroupoid`, `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`, `Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers`, `Mathlib.CategoryTheory.Limits.Types.Pullbacks`, `Mathlib.CategoryTheory.Localization.FiniteProducts`, `Mathlib.CategoryTheory.Localization.Resolution`, `Mathlib.CategoryTheory.MorphismProperty.RetractArgument`, `Mathlib.CategoryTheory.Sites.Continuous`, `Mathlib.CategoryTheory.Sites.CoproductSheafCondition`, `Mathlib.CategoryTheory.Sites.LocalProperties`, `Mathlib.CategoryTheory.Sites.Sieves.Basic`, `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`, `Mathlib.CategoryTheory.Triangulated.TStructure.TExact`, `Mathlib.Combinatorics.SimpleGraph.Walk.Decomp`, `Mathlib.Data.Int.Order.Units`, `Mathlib.Data.Multiset.DershowitzManna`, `Mathlib.Data.Nat.Choose.Basic`, `Mathlib.Data.Rat.Squarefree`, `Mathlib.Data.String.Basic`, `Mathlib.FieldTheory.IntermediateField.Basic`, `Mathlib.FieldTheory.Minpoly.MinpolyDiv`, `Mathlib.Geometry.Euclidean.Sphere.PolePolar`, `Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`, `Mathlib.GroupTheory.GroupAction.SubMulAction.Combination`, `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range`, `Mathlib.LinearAlgebra.FreeProduct.Basic`, `Mathlib.LinearAlgebra.Matrix.Notation`, `Mathlib.LinearAlgebra.Pi`, `Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic`, `Mathlib.MeasureTheory.Measure.SubFinite`, `Mathlib.MeasureTheory.Measure.WithDensity`, `Mathlib.ModelTheory.Encoding`, `Mathlib.NumberTheory.LSeries.Injectivity`, `Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv`, `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`, `Mathlib.NumberTheory.Pell`, `Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity`, `Mathlib.Order.Completion`, `Mathlib.Order.ModularLattice`, `Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion`, `Mathlib.RingTheory.Finiteness.Subalgebra`, `Mathlib.RingTheory.HahnSeries.Binomial`, `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`, `Mathlib.RingTheory.LocalProperties.Exactness`, `Mathlib.RingTheory.RamificationInertia.Ramification`, `Mathlib.RingTheory.RegularLocalRing.Defs`, `Mathlib.RingTheory.SimpleRing.Defs`, `Mathlib.RingTheory.Spectrum.Prime.Homeomorph`, `Mathlib.RingTheory.WittVector.Domain`, `Mathlib.RingTheory.WittVector.IsPoly`, `Mathlib.SetTheory.ZFC.Basic`, `Mathlib.Tactic.Determinant.Echelon.Cert`, `Mathlib.Tactic.Linter.Multigoal`, `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible`, `Mathlib.Topology.Algebra.Monoid.Defs`, `Mathlib.Topology.Category.CompHaus.Basic`, `Mathlib.Topology.LocallyFinsupp.Pushforward`, `Mathlib.Topology.Order.OrderClosedExtr`, `Mathlib.Util.CountHeartbeats`, `Mathlib.Util.TermReduce`
- Closures containing at least one nested inductive: 97 of 98

## Verdict

- E1 (fails if kernel share > 50%): **passes**
- H1 (kernel ≤ 10%): **holds (whole 95% interval at or below 10%)**
- E2 (fails if replay > 30% of build), kernel replay alone: **passes**
- E2, replay including each module's import loading (as `leanchecker` does it): **fails**


## Per module

| Module | Lines | Elab wall (s) | Kernel (s) | Kernel % | Replay (s) | nanoda closure (s) | Closure decls | Certus |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` | 140 | 1.405 | 0.15 | 9.3 | 0.126592 | 3.163 | 12646 | ok |
| `Mathlib.Algebra.Category.Ring.Basic` | 735 | 3.411 | 0.68 | 12.7 | 0.479977 | 3.414 | 9914 | ok |
| `Mathlib.Algebra.CharP.LocalRing` | 66 | 0.953 | 0.01 | 0.8 | 0.008151 | 0.954 | 7695 | ok |
| `Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries` | 123 | 0.855 | 0.01 | 0.8 | 0.009617 | 0.656 | 6609 | ok |
| `Mathlib.Algebra.Field.GeomSum` | 88 | 0.955 | 0.02 | 1.7 | 0.017365 | 0.655 | 5560 | ok |
| `Mathlib.Algebra.Group.Commute.Basic` | 139 | 0.602 | 0.02 | 2.1 | 0.011514 | 0.051 | 722 | ok |
| `Mathlib.Algebra.Group.Graph` | 231 | 1.656 | 0.08 | 3.0 | 0.066161 | 0.102 | 1231 | ok |
| `Mathlib.Algebra.GroupWithZero.Opposite` | 111 | 0.452 | 0.01 | 2.6 | 0.009397 | 0.051 | 670 | ok |
| `Mathlib.Algebra.Homology.Additive` | 346 | 2.608 | 0.36 | 9.0 | 0.248653 | 0.201 | 1447 | ok |
| `Mathlib.Algebra.Homology.DerivedCategory.Fractions` | 197 | 1.406 | 0.10 | 3.8 | 0.064488 | 2.66 | 12969 | ok |
| `Mathlib.Algebra.Homology.Embedding.TruncLEHomology` | 172 | 0.954 | 0.07 | 4.9 | 0.054405 | 1.107 | 8335 | ok |
| `Mathlib.Algebra.MvPolynomial.Derivation` | 150 | 1.555 | 0.13 | 5.4 | 0.08734 | 0.804 | 6230 | ok |
| `Mathlib.Algebra.MvPolynomial.Variables` | 360 | 1.457 | 0.12 | 3.5 | 0.073697 | 1.057 | 7738 | ok |
| `Mathlib.Algebra.Notation.Indicator` | 287 | 1.304 | 0.06 | 2.8 | 0.045378 | 0.152 | 1483 | ok |
| `Mathlib.Algebra.PresentedMonoid.Basic` | 147 | 0.903 | 0.03 | 3.0 | 0.029641 | 0.151 | 1915 | ok |
| `Mathlib.Algebra.Ring.TransferInstance` | 174 | 0.955 | 0.06 | 5.1 | 0.044716 | 0.101 | 1105 | ok |
| `Mathlib.Algebra.Star.MonoidHom` | 358 | 1.355 | 0.08 | 4.0 | 0.057039 | 0.051 | 655 | ok |
| `Mathlib.AlgebraicGeometry.Artinian` | 190 | 1.805 | 0.04 | 1.6 | 0.028298 | 13.594 | 30386 | ok |
| `Mathlib.AlgebraicGeometry.Birational.Birational` | 295 | 1.254 | 0.04 | 2.7 | 0.031702 | 7.221 | 26723 | ok |
| `Mathlib.AlgebraicGeometry.Over` | 60 | 1.154 | 0.00 | 0.1 | 0.0013 | 5.425 | 14626 | ok |
| `Mathlib.AlgebraicGeometry.Sites.BigZariski` | 159 | 1.104 | 0.04 | 2.6 | 0.03208 | 9.137 | 25628 | ok |
| `Mathlib.AlgebraicTopology.SimplexCategory.Truncated` | 165 | 2.258 | 0.10 | 3.1 | 0.07144 | 0.955 | 6890 | ok |
| `Mathlib.AlgebraicTopology.SimplicialSet.CompStruct` | 352 | 2.306 | 0.16 | 5.5 | 0.11549 | 0.505 | 4267 | ok |
| `Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex` | 392 | 1.307 | 0.09 | 3.7 | 0.062931 | 0.452 | 5737 | ok |
| `Mathlib.Analysis.Asymptotics.Prod` | 171 | 1.105 | 0.04 | 2.2 | 0.026754 | 1.354 | 10629 | ok |
| `Mathlib.Analysis.CStarAlgebra.ApproximateUnit` | 342 | 6.872 | 0.32 | 1.9 | 0.269078 | 15.197 | 51336 | ok |
| `Mathlib.Analysis.CStarAlgebra.Hom` | 132 | 2.606 | 0.20 | 4.0 | 0.172314 | 14.909 | 50957 | ok |
| `Mathlib.Analysis.Calculus.FDeriv.Norm` | 198 | 2.257 | 0.24 | 4.8 | 0.149814 | 7.27 | 26618 | ok |
| `Mathlib.Analysis.Complex.IsIntegral` | 33 | 0.653 | 0.00 | 0.3 | 0.002404 | 0.704 | 7720 | ok |
| `Mathlib.Analysis.InnerProductSpace.Orthogonal` | 554 | 3.114 | 0.33 | 4.9 | 0.218894 | 2.106 | 16062 | ok |
| `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap` | 193 | 1.104 | 0.04 | 3.0 | 0.031604 | 1.054 | 10596 | ok |
| `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation` | 127 | 1.806 | 0.06 | 2.1 | 0.047297 | 13.898 | 51206 | ok |
| `Mathlib.CategoryTheory.Adjunction.Reflective` | 235 | 1.153 | 0.07 | 3.8 | 0.048426 | 0.151 | 1066 | ok |
| `Mathlib.CategoryTheory.Bicategory.Functor.Cat` | 101 | 1.104 | 0.05 | 4.2 | 0.033482 | 0.101 | 639 | ok |
| `Mathlib.CategoryTheory.Center.Localization` | 82 | 0.603 | 0.02 | 2.4 | 0.014303 | 0.252 | 2372 | ok |
| `Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic` | 64 | 0.753 | 0.00 | 0.2 | 0.001019 | 0.051 | 376 | ok |
| `Mathlib.CategoryTheory.Equivalence.Symmetry` | 116 | 1.153 | 0.15 | 10.9 | 0.114696 | 0.155 | 787 | ok |
| `Mathlib.CategoryTheory.Generator.StrongGenerator` | 158 | 0.953 | 0.03 | 1.8 | 0.020213 | 0.202 | 1299 | ok |
| `Mathlib.CategoryTheory.Groupoid.FreeGroupoid` | 227 | 1.006 | 0.05 | 3.2 | 0.036339 | 0.101 | 641 | ok |
| `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers` | 578 | 2.96 | 0.24 | 5.2 | 0.171896 | 0.654 | 4427 | ok |
| `Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers` | 735 | 2.159 | 0.26 | 8.0 | 0.206524 | 0.202 | 1178 | ok |
| `Mathlib.CategoryTheory.Limits.Types.Pullbacks` | 239 | 2.006 | 0.11 | 3.0 | 0.073101 | 0.151 | 1196 | ok |
| `Mathlib.CategoryTheory.Localization.FiniteProducts` | 138 | 1.003 | 0.03 | 2.5 | 0.025974 | 0.704 | 4374 | ok |
| `Mathlib.CategoryTheory.Localization.Resolution` | 447 | 2.057 | 0.34 | 9.9 | 0.225334 | 0.252 | 2043 | ok |
| `Mathlib.CategoryTheory.MorphismProperty.RetractArgument` | 71 | 1.003 | 0.02 | 1.8 | 0.014649 | 0.151 | 1451 | ok |
| `Mathlib.CategoryTheory.Sites.Continuous` | 444 | 2.156 | 0.34 | 9.4 | 0.254359 | 0.855 | 4520 | ok |
| `Mathlib.CategoryTheory.Sites.CoproductSheafCondition` | 109 | 0.903 | 0.06 | 5.7 | 0.051168 | 0.404 | 2246 | ok |
| `Mathlib.CategoryTheory.Sites.LocalProperties` | 74 | 0.702 | 0.01 | 1.1 | 0.009637 | 0.655 | 3930 | ok |
| `Mathlib.CategoryTheory.Sites.Sieves.Basic` | 543 | 1.608 | 0.12 | 3.6 | 0.092726 | 0.151 | 1199 | ok |
| `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting` | 302 | 2.407 | 0.22 | 6.8 | 0.157093 | 0.753 | 5428 | ok |
| `Mathlib.CategoryTheory.Triangulated.TStructure.TExact` | 75 | 0.702 | 0.02 | 2.5 | 0.015096 | 0.153 | 1712 | ok |
| `Mathlib.Combinatorics.SimpleGraph.Walk.Decomp` | 378 | 1.608 | 0.18 | 4.0 | 0.15003 | 0.603 | 4142 | ok |
| `Mathlib.Data.Int.Order.Units` | 64 | 0.803 | 0.01 | 1.2 | 0.007989 | 0.202 | 2574 | ok |
| `Mathlib.Data.Multiset.DershowitzManna` | 173 | 0.852 | 0.02 | 1.3 | 0.015386 | 0.205 | 2700 | ok |
| `Mathlib.Data.Nat.Choose.Basic` | 425 | 1.054 | 0.18 | 7.5 | 0.135208 | 0.404 | 3349 | ok |
| `Mathlib.Data.Rat.Squarefree` | 31 | 0.653 | 0.00 | 0.3 | 0.002388 | 0.806 | 8531 | ok |
| `Mathlib.Data.Setoid.Basic` | 5 | 0.352 | 0.00 | 0.0 | 0.000106 | – | – | – |
| `Mathlib.Data.String.Basic` | 154 | 1.305 | 0.03 | 1.6 | 0.023279 | 1.36 | 4852 | ok |
| `Mathlib.FieldTheory.IntermediateField.Basic` | 941 | 5.169 | 1.84 | 20.7 | 1.364177 | 0.958 | 7159 | ok |
| `Mathlib.FieldTheory.Minpoly.MinpolyDiv` | 224 | 1.708 | 0.11 | 3.3 | 0.076844 | 4.717 | 22898 | ok |
| `Mathlib.Geometry.Euclidean.Sphere.PolePolar` | 155 | 1.757 | 0.12 | 3.9 | 0.089796 | 4.314 | 25380 | ok |
| `Mathlib.GroupTheory.FreeGroup.CyclicallyReduced` | 246 | 1.705 | 0.15 | 6.5 | 0.124218 | 0.456 | 4015 | ok |
| `Mathlib.GroupTheory.GroupAction.SubMulAction.Combination` | 291 | 2.307 | 0.11 | 3.1 | 0.087455 | 1.805 | 13679 | ok |
| `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range` | 93 | 1.053 | 0.06 | 4.2 | 0.1512 | 0.201 | 1740 | ok |
| `Mathlib.LinearAlgebra.FreeProduct.Basic` | 224 | 1.556 | 0.20 | 8.5 | 0.16403 | 1.209 | 6743 | ok |
| `Mathlib.LinearAlgebra.Matrix.Notation` | 538 | 2.765 | 0.25 | 4.0 | 0.176266 | 3.166 | 10685 | ok |
| `Mathlib.LinearAlgebra.Pi` | 732 | 3.064 | 0.54 | 8.9 | 0.378682 | 0.708 | 5642 | ok |
| `Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic` | 139 | 2.908 | 0.14 | 4.4 | 0.13008 | 3.712 | 23675 | ok |
| `Mathlib.MeasureTheory.Measure.SubFinite` | 92 | 1.104 | 0.01 | 0.9 | 0.008701 | 2.505 | 18782 | ok |
| `Mathlib.MeasureTheory.Measure.WithDensity` | 811 | 3.362 | 0.16 | 1.9 | 0.099051 | 3.368 | 20919 | ok |
| `Mathlib.ModelTheory.Encoding` | 332 | 1.504 | 0.12 | 4.9 | 0.123131 | 0.604 | 7406 | ok |
| `Mathlib.NumberTheory.LSeries.Injectivity` | 251 | 1.154 | 0.03 | 0.9 | 0.031844 | 3.358 | 26731 | ok |
| `Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv` | 55 | 3.608 | 0.08 | 1.3 | 0.067035 | 16.321 | 53809 | ok |
| `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas` | 219 | 2.509 | 0.07 | 0.8 | 0.0496 | 2.01 | 14757 | ok |
| `Mathlib.NumberTheory.Pell` | 665 | 2.915 | 0.35 | 4.8 | 0.239842 | 1.858 | 12271 | ok |
| `Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity` | 86 | 1.606 | 0.03 | 1.4 | 0.027459 | 3.013 | 17648 | ok |
| `Mathlib.Order.Completion` | 299 | 1.003 | 0.05 | 3.3 | 0.037149 | 0.102 | 1592 | ok |
| `Mathlib.Order.ModularLattice` | 441 | 2.058 | 0.13 | 4.1 | 0.091487 | 0.152 | 1742 | ok |
| `Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion` | 502 | 5.467 | 1.88 | 16.3 | 1.48641 | 6.776 | 27572 | ok |
| `Mathlib.RingTheory.Finiteness.Subalgebra` | 62 | 1.105 | 0.03 | 2.2 | 0.021019 | 0.653 | 4921 | ok |
| `Mathlib.RingTheory.HahnSeries.Binomial` | 124 | 1.406 | 0.09 | 3.1 | 0.058144 | 1.455 | 10271 | ok |
| `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` | 518 | 2.208 | 0.29 | 5.1 | 0.179838 | 3.314 | 19298 | ok |
| `Mathlib.RingTheory.LocalProperties.Exactness` | 330 | 2.711 | 0.30 | 4.3 | 0.200913 | 1.205 | 7685 | ok |
| `Mathlib.RingTheory.RamificationInertia.Ramification` | 352 | 2.807 | 0.57 | 9.5 | 0.406317 | 9.622 | 32237 | ok |
| `Mathlib.RingTheory.RegularLocalRing.Defs` | 131 | 1.755 | 0.03 | 1.6 | 0.023549 | 5.775 | 23345 | ok |
| `Mathlib.RingTheory.SimpleRing.Defs` | 29 | 0.502 | 0.00 | 0.3 | 0.001506 | 0.102 | 1599 | ok |
| `Mathlib.RingTheory.Spectrum.Prime.Homeomorph` | 92 | 1.254 | 0.13 | 7.4 | 0.128605 | 5.375 | 25030 | ok |
| `Mathlib.RingTheory.WittVector.Domain` | 116 | 0.803 | 0.01 | 0.9 | 0.00614 | 1.661 | 15410 | ok |
| `Mathlib.RingTheory.WittVector.IsPoly` | 461 | 2.21 | 0.15 | 4.1 | 0.124421 | 2.358 | 15556 | ok |
| `Mathlib.SetTheory.ZFC.Basic` | 773 | 2.062 | 0.12 | 2.6 | 0.073042 | 0.152 | 1969 | ok |
| `Mathlib.Tactic.Determinant.Echelon.Cert` | 108 | 0.902 | 0.01 | 1.5 | 0.00901 | 2.007 | 9594 | ok |
| `Mathlib.Tactic.Linter.Multigoal` | 187 | 0.402 | 0.00 | 0.8 | 0.00274 | 0.051 | 275 | ok |
| `Mathlib.Tactic.ToAdditive` | 32 | 0.301 | 0.00 | 0.0 | 0.000124 | – | – | – |
| `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible` | 250 | 1.004 | 0.13 | 6.3 | 0.088688 | 0.254 | 2591 | ok |
| `Mathlib.Topology.Algebra.Monoid.Defs` | 179 | 1.003 | 0.02 | 1.8 | 0.015782 | 0.151 | 2051 | ok |
| `Mathlib.Topology.Category.CompHaus.Basic` | 222 | 1.155 | 0.05 | 3.4 | 0.036091 | 3.513 | 22022 | ok |
| `Mathlib.Topology.LocallyFinsupp.Pushforward` | 82 | 1.504 | 0.02 | 1.4 | 0.020177 | 0.453 | 4881 | ok |
| `Mathlib.Topology.Order.OrderClosedExtr` | 45 | 0.702 | 0.00 | 0.2 | 0.0012 | 0.151 | 1793 | ok |
| `Mathlib.Util.CountHeartbeats` | 313 | 0.702 | 0.01 | 0.7 | 0.004877 | 2.061 | 7811 | ok |
| `Mathlib.Util.TermReduce` | 97 | 0.454 | 0.00 | 0.4 | 0.001749 | 2.062 | 7619 | ok |

## Done

- `Basic.lean`: all definitions closed.
- `IntegrationByParts.lean`: `ac_product_integral_eq_boundary`, `ac_weighted_error_integral_eq_boundary`, and `product_integral_derivativeBalance_eq_zero` closed.
- `GuardedInformation.lean`: zero-derivative, guarded scalar/joint score (including density-zero cases), error-numerator, score-centering, and information-decomposition lemmas closed.
- `WeightedL2.lean`: product Fubini and weighted L2 Cauchy--Schwarz closed.
- `Main.lean`: `observation_dependent_van_trees` is closed with the observation-dependent target and full product-measure hypotheses.
- Re-ran project/library and Mathlib searches and inspected the canonical `Causalean.Stat.Limit.van_trees_inequality` source.
- Ground-truth scan finds no `sorry`, `admit`, `native_decide`, custom `axiom`, or research-module import.
- Lean diagnostics for all five files report no errors; `lake build +CausalSmith.Substrate.ObservationDependentVanTreesAc.Main` succeeds.
- Axiom audit of the headline and core helper theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Added `a ≤ b` to the two oriented interval helper statements; without it they were false for reversed endpoints.
- `jointScore_eq_add` now assumes both component densities are positive; density-zero algebra is exposed by `jointScore_mul_jointDensity` and `errorScoreField_eq_numerator`.
- The headline derivative representatives are joint-a.e. under `parameterMeasure.prod μ`. This is the natural Fubini-stable formulation and supplies both section orders via product swap, avoiding the nonmeasurable-null-set gap in the former one-way nested hypothesis.
- Expectations remain explicit weighted integrals under `(volume.restrict (Icc ell u)).prod μ`; the target stays observation-dependent.
- No filler prompts remain: the module is fully proved and ready for review.

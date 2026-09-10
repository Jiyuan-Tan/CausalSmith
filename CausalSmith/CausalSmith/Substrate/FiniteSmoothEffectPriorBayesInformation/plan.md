## Done

- Scaffolded `Prior.lean`: quartic beta prior/derivative, exact ordinary and topological support API, strict ambient support, endpoints, C¹/AC, normalization, score integrability, and exact `10 / a^2` information plus `40 / a^2` bound.
- Scaffolded `FiniteExperiment.lean`: counting-integral/sum bridge, normalization, finite differentiation/centering, guarded score, finite Fisher sum, and averaged pointwise bound.
- Scaffolded `VanTreesAssembly.lean`: finite-model regularity structure, abstract native-real fraction theorem, and canonical smooth-prior specialization; imports `FiniteKernelBayes` for direct downstream composition.
- Targeted build of the umbrella module succeeds with only sorry warnings (27 total), no hard errors.
- Searched the Causalean index first; reused observation-dependent van Trees guarded-score/information APIs. Read arXiv:2402.01895 TeX as an external van Trees reference.

## Remaining

- `Prior.lean`: prove all 17 theorems from `smoothPrior_nonneg` through `priorInformation_smoothPrior_le`.
- `FiniteExperiment.lean`: prove all 8 theorems from `integral_count_eq_sum` through `average_fisherInformation_le`.
- `VanTreesAssembly.lean`: prove `finite_vanTrees_lower_bound` and `smoothPrior_finite_vanTrees_lower_bound`.

## Blocked

- None. The prior's piecewise C¹ and exact integral/information calculations are the main technical proof burden.

## Decisions

- Use `15/(16a) * (1-((θ-c)/a)^2)^2` on `|θ-c|<a`, zero outside; its exact Fisher information is `10/a^2`, hence the requested 40-bound.
- Keep model-specific joint measurability/integrability in `FiniteVanTreesModelRegularity`; canonical prior regularity and boundary vanishing are derived by the specialization rather than re-assumed.
- Keep all risk and information conclusions in `ℝ`; no `ENNReal` bridge and no minimax conclusion is assumed.

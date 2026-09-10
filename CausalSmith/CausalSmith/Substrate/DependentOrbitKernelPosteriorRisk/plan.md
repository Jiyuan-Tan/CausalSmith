## Done

- Ground-truth audit: the target tree was absent; no prior declarations or proofs existed.
- Library search identified the reusable `FinitePosteriorBayesRisk`, `FiniteKernelBayes`, and dependent `FiniteSquaredLoss` conventions.
- `Model.lean`: scaffolded the normalized dependent finite experiment compatible with `FiniteSquaredLoss.risk`.
- `Lower.lean`: scaffolded predictive normalization, null-fiber safety, exact square completion, posterior optimality, fiberwise infimum, and minimax lower transport.
- `Upper.lean`: scaffolded null-design safety, interval preservation, conditional Jensen, bounded procedure construction, and minimax upper transport.

## Remaining

- `Lower.lean`: prove 12 declarations from `sum_predictiveMass` through `sInf_posteriorResidual_le_minimaxValue`.
- `Upper.lean`: prove 6 declarations: `weight_eq_zero_of_designMass_eq_zero`, `conditionalBarycenter_mem_Icc`, `designMass_mul_conditionalBarycenter_sq_le`, `Model.conditionalBarycenter_risk_le`, `Model.risk_barycenterProcedure_le`, and `Model.minimaxValue_le_of_randomizedGridRisk`.

## Blocked

- None.

## Decisions

- Split lower and upper proof chains into independent modules over a small shared model; `Main.lean` is the public entry point.
- Use zero as the guarded posterior mean on null predictive fibers and a caller-supplied bounded default for null design fibers; no support assumptions.
- State the posterior decision optimum over unrestricted real rules, while transporting it to the existing bounded-procedure minimax API without assuming target bounds.
- The standard reference is a general finite Bayesian/Jensen argument rather than a named primary source, so no external source fetch applies.

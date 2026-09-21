## Done
- Created `FiniteSelection.lean`, `AlgebraicLoci.lean`, and the umbrella module.
- Scaffolded genuine finite-uniform convergence, ranked penalized-argmin consistency, success/failure event formulations, and finset/fintype/subtype polynomial-locus APIs.
- `lake build CausalSmith.Substrate.FiniteModelBicAlgebraicLoci` succeeds with only expected `sorry` warnings.
- Library search identified `Tendsto_inProb.pi_comp_continuousAt`, `MeasureTheory.tendstoInMeasure_iff_dist`, `MvPolynomial.eval_prod`, and `Finset.prod_ne_zero_iff`. No specific external primary source was named; statements were grounded in the canonical local Causalean/Mathlib APIs.

## Remaining
- `FiniteSelection.lean`: five sorries in `tendsto_inProb_finiteMaxError`, `tendsto_measure_finiteMaxError_ge_zero`, `IsRankedMinimizer.le`, `finite_penalized_argmin_failure_tendsto_zero`, and `finite_penalized_argmin_consistent`.
- `AlgebraicLoci.lean`: six sorries covering finset, fintype, and subtype locus/product results.
- After closure: rebuild, source scan for `sorry|admit|axiom`, and `#print axioms` for all public theorems.

## Blocked
- None.

## Decisions
- Represent population minimizers as the full set of global loss minimizers, retaining ties.
- Encode fixed deterministic tie-breaking with an injective natural-number rank and lexicographic ranked-minimizer predicate.
- State both failure probability tending to zero and measurable success probability tending to one; the latter needs event measurability for complement arithmetic.
- Keep penalties deterministic by type and assume coordinatewise `penalty n i / n → 0`.
- Use two independent fillers, partitioned by module/import closure.
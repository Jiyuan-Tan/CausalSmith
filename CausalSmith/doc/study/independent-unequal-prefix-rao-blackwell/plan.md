## Done
- `Basic.lean`: all declarations are closed, including measurability, off-overflow agreement, the exact two-prefix product law, and the restricted nonoverflow map law.
- `Risk.lean`: the independent count kernel, fixed-pool composition law, conditional-average integral identity, measurability, and conditional squared-risk contraction are closed.
- Round-3 ground truth: Lean LSP reports zero errors; targeted `lake build CausalSmith.Substrate.IndependentUnequalPrefixRaoBlackwell.Main` succeeds with exactly three `sorry`s, all in `Risk.lean`.
- Rechecked the Causalean index and canonical one-pool proofs in `Causalean.Stat.Minimax.MarkovKernelTransport`; Mathlib search identified `MeasureTheory.setIntegral_le_integral` and `measureReal_union_le` for the remaining layer.

## Remaining
- `Risk.lean`: `sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq`.
- `Risk.lean`: `sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le`.
- `Risk.lean`: headline `sqRisk_independentPrefixRaoBlackwellStatistic_le`; its finite-alphabet specialization remains transitively dependent on it.

## Blocked
- None.

## Decisions
- Preserve the general `FiniteSample X × FiniteSample Y` API with independent counts and unequal capacities; no pairing, equal-alphabet, or shared-length assumptions.
- Reuse the canonical one-pool restricted-risk proofs; comments in `Risk.lean` now record the relevant templates and Mathlib bridge lemmas.
- Assign all three dependency-ordered proofs to one filler because they share one file and the headline consumes both bridge lemmas. None has previously failed, so further decomposition is not yet warranted.
- No primary paper was named; the canonical in-repository Poisson-prefix/Rao–Blackwell implementation grounds the statements. No paper/research module is imported.
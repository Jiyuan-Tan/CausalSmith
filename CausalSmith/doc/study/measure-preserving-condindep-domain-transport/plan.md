## Done
- `WithDensity.lean`: `map_withDensity_comp_measurableEquiv` is proved for arbitrary `ℝ≥0∞` densities.
- `CondExp.lean`: `condExp_comp_measurableEquiv` and `condExpInd_preimage_measurableEquiv` are proved with no `sorry`.
- `Examples.lean`: identity and nontrivial product-coordinate-swap examples are present.
- Ground-truth build `lake build CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.Examples` succeeds with exactly two `sorry` warnings and no errors.
- Project and Mathlib searches identified `ProbabilityTheory.condIndep_iff`, `condIndepFun_iff_condIndep`, and measurable-embedding a.e. transport as the relevant public API. The canonical Mathlib source was inspected; no external reference was named.
- Added concise proof-route comments beside both remaining declarations.

## Remaining
- `CondIndep.lean`: prove `condIndep_comap_measurableEquiv_iff`.
- `CondIndep.lean`: derive `condIndepFun_comp_measurableEquiv_iff` from the generic theorem.
- After filling: rebuild `Examples`, scan the substrate sources, and run `#print axioms` for the primary conditional-independence and weighted-measure theorems.

## Blocked
- None.

## Decisions
- Preserve the current fully generic API and transport all three σ-algebras through `MeasurableSpace.comap e`.
- Prove the generic result through Mathlib's conditional-probability factorization (`condIndep_iff`) and the completed `condExpInd_preimage_measurableEquiv` helper.
- Use one filler: both open proofs share one import closure, and the `CondIndepFun` result directly depends on the generic `CondIndep` result.
- Do not import paper/research modules or reuse their private transport lemmas.
# Substrate requirement: ae-support-retraction-condindep-transport

## Goal

Provide a reusable conditional-independence transport theorem for a pair of measurable maps that are inverses only almost everywhere under the two transported measures. This is the support/retraction analogue of transport along a genuine measurable equivalence.

## Provides (API contract)

- For measurable maps `r : Ω → Ω'` and `s : Ω' → Ω`, finite measures `μ` and `μ'`, with `Measure.map r μ = μ'`, `Measure.map s μ' = μ`, `s ∘ r = id` `μ`-almost everywhere, and `r ∘ s = id` `μ'`-almost everywhere, prove that measurable random variables `X`, `Y`, and `Z` on `Ω'` satisfy
  `CondIndepFun (MeasurableSpace.comap (Z ∘ r) inferInstance) (X ∘ r) (Y ∘ r) μ ↔ CondIndepFun (MeasurableSpace.comap Z inferInstance) X Y μ'`.
- An equivalent formulation using the current explicit measurability arguments of `CondIndepFun` is acceptable.
- A one-direction theorem followed by the iff obtained by applying it to `r` and `s` is acceptable and preferred if it matches the library structure.
- Immediate corollaries for a measurable retraction onto a full-measure support may be supplied, but no paper-specific cube definitions should appear.

## Statement / milestones

1. Establish that composition by `r` and `s` transports the conditioning comap sigma-algebras modulo completion/almost-everywhere equality under the corresponding measures.
2. Transport the integral-factorization or conditional-expectation characterization of `CondIndepFun` through `Measure.map`, using the supplied map equalities.
3. Use the almost-everywhere inverse identities to recover the original measurable functions and conditioning variable in the reverse direction.
4. Derive the symmetric iff theorem and verify it specializes to the existing measurable-equivalence theorem.
5. Include a small full-measure-support/retraction example where the inclusion is not surjective, demonstrating why pointwise measurable equivalence is unnecessary.

Near-Lean target:

`condIndepFun_comp_aeEquiv_iff (hr : Measurable r) (hs : Measurable s) (hmap_r : Measure.map r μ = μ') (hmap_s : Measure.map s μ' = μ) (hsr : s ∘ r =ᵐ[μ] id) (hrs : r ∘ s =ᵐ[μ'] id) ... : CondIndepFun (MeasurableSpace.comap (Z ∘ r) inferInstance) (X ∘ r) (Y ∘ r) μ ↔ CondIndepFun (MeasurableSpace.comap Z inferInstance) X Y μ'`.

The exact namespace, measurability arguments, and finite/sigma-finite assumptions should follow the existing Causalean `CondIndepFun` API.

## Standard reference

Conditional independence depends only on the measure-space structure modulo null sets. A bimeasurable measure-preserving isomorphism modulo null sets therefore preserves conditional independence, including the conditioning sigma-algebra. This is the standard measure-algebra/isomorphism invariance principle.

## Intended reuse

The immediate consumer transports conditional independence between an ambient space carrying a law supported on a measurable subset and the subtype/product coordinate space obtained by retracting to that support. The result should be fully sample-space generic and reusable for support restrictions, subtypes, charts, and almost-everywhere measure-space isomorphisms. It must not mention cubes, DAGs, mechanisms, affine perturbations, MMD, or genericity.

## May assume / must derive

May assume measurability of `r`, `s`, `X`, `Y`, and `Z`; finiteness or sigma-finiteness as required; both map equalities; and both almost-everywhere inverse identities. Equivalent packaging as a reusable AE measure-space isomorphism structure is allowed.

Must derive the transported conditional-independence implication and its iff. Do not assume either conditional-independence proposition, equality of conditional expectations, or pointwise bijectivity/surjectivity.

## Non-goals

- Do not import or mention `CausalSmith.ExactID.*_Research`.
- Do not define the paper's compact cube inclusion/retraction.
- Do not prove any finite-DAG edge characterization, causal-minimality openness, analytic perturbation, MMD, or genericity theorem.
- Do not strengthen AE inverse hypotheses to a genuine measurable equivalence.
- Do not add assumptions or gates to research theorems.

## Known building blocks

- `CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.CondIndep`, especially `condIndepFun_comp_measurableEquiv_iff` and `condIndep_comap_measurableEquiv_iff`.
- `CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.WithDensity`, especially `map_withDensity_comp_measurableEquiv`.
- Mathlib `Measure.map_map`, integral-under-map lemmas, `Filter.EventuallyEq.comp_tendsto`, and AE-congruence for measurable functions and integrals.
- The existing genuine-equivalence theorem is insufficient because a subtype inclusion onto a full-measure support is not surjective on the ambient carrier.

### Research-folder prerequisites to extract

None. The study must remain neutral and use only Mathlib/Causalean plus the verified neutral transport staging modules above.

### Acceptance checks

- Zero `sorry`, `admit`, errors, or nonstandard axioms.
- `#print axioms` for the primary implication and iff reports only standard Lean/Mathlib axioms.
- Semantic review confirms that the conditioning sigma-algebra, both random variables, and the measure are all transported, and that the inverse laws are used only almost everywhere.
- A non-surjective support inclusion/retraction example exercises the theorem.

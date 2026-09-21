# Substrate requirement: measure-preserving-condindep-domain-transport

## Goal

Provide reusable transport theorems for conditional independence and weighted measures under a measure-preserving measurable equivalence of sample domains.

## Provides (API contract)

- `CondIndepFun` invariance under sample-domain equivalence: for `e : Ω ≃ᵐ Ω'` with `MeasurePreserving e μ μ'`, measurable random variables `X`, `Y`, and conditioning variable `Z` on `Ω'`, conditional independence of `X ∘ e` and `Y ∘ e` given `Z ∘ e` under `μ` is equivalent to conditional independence of `X` and `Y` given `Z` under `μ'`.
- An equivalent theorem formulated directly with conditioning sigma-algebras/comaps if that matches the current `CondIndepFun` API.
- Weighted-measure transport: under the same `e`, mapping `μ.withDensity (d ∘ e)` through `e` equals `μ'.withDensity d`, assuming the standard measurability/integrability conditions needed by Mathlib.
- Finite-coordinate or subtype corollaries only if they are immediate specializations of the generic results.

## Statement / milestones

1. Prove the `withDensity` map identity using `MeasurePreserving.map_eq`, change of variables, and measurable equivalence inverse identities.
2. Establish equivalence of conditional expectations/integral factorization characterizations after reparameterizing the sample domain.
3. Derive the `CondIndepFun` iff theorem with both random variables and the conditioning sigma-algebra pulled back through `e`.
4. Verify identity-equivalence and a simple subtype/coordinate-product example.

Near-Lean target:

`CondIndepFun (MeasurableSpace.comap (Z ∘ e) inferInstance) mX mY (X ∘ e) (Y ∘ e) μ ↔ CondIndepFun (MeasurableSpace.comap Z inferInstance) mX mY X Y μ'`.

The exact implicit measurable-space arguments should follow Causalean/Mathlib conventions.

## Standard reference

Conditional independence is invariant under measure-space isomorphism; this follows directly from its conditional-expectation or integral-factorization characterization. Pushforward of a density by a measure-preserving isomorphism is the standard change-of-variables identity for weighted measures.

## Intended reuse

The immediate consumer identifies a compact coordinate-product finite-density model with an ambient restricted-cube model before applying a generic edge conditional-independence characterization. The theorem should be fully sample-space generic and reusable for subtype, coordinate, and chart equivalences; it must not mention DAGs, mechanisms, causal minimality, or the motivating paper.

## May assume / must derive

May assume a measurable equivalence, its `MeasurePreserving` certificate, sigma-finiteness or finiteness where required, measurability of `X`, `Y`, `Z`, and measurability/nonnegativity of density `d` as demanded by the existing APIs.

Must derive the conditional-independence equivalence and weighted-measure map identity. Do not assume equality of the transported conditional-independence propositions or the weighted measures themselves.

## Non-goals (optional)

- Do not import or mention `CausalSmith.ExactID.*_Research`.
- Do not prove any finite-DAG edge characterization, affine perturbation, MMD, or genericity theorem.
- Do not construct the paper's compact-cube equivalence; it is merely a future consumer.
- Do not add assumptions or gates to research theorems.

## Known building blocks (optional)

- `MeasurePreserving.map_eq`, measurable-equivalence inverse identities, `Measure.map_map`, and `Measure.withDensity` integration/map lemmas.
- Causalean/Mathlib `CondIndepFun` characterizations through conditional expectation or product-integral identities.
- Existing `CondIndepFun.comp` is insufficient because it leaves the sample domain, measure, and conditioning sigma-algebra fixed.
- Existing conditional-distribution measurable-equivalence lemmas reparameterize a codomain, not the sample domain.

### Research-folder prerequisites to extract

None. The study must be neutral and use only Mathlib/Causalean foundations.

### Acceptance checks

- Zero `sorry`, `admit`, errors, or nonstandard axioms.
- `#print axioms` for the primary conditional-independence and `withDensity` transport theorems reports only standard Lean/Mathlib axioms.
- Semantic review confirms that the conditioning sigma-algebra is transported along with the sample domain, not silently left fixed.
- A small example exercises the theorem with a nontrivial measurable equivalence.

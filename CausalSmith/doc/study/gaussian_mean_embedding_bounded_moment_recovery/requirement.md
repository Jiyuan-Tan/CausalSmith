# Substrate requirement: gaussian_mean_embedding_bounded_moment_recovery

## Goal
Build a reusable theorem showing that equality of Gaussian-kernel mean embeddings of finite real-valued laws with common bounded support forces equality of their raw second moments (preferably, prove injectivity/equality of the laws as the stronger standard API).

## Provides (API contract)
- A general Mathlib/Causalean-facing explicit Gaussian feature map into a complete real Hilbert space, together with measurability or continuity and Bochner-integrability under finite measures.
- A continuous-linear coordinate evaluation theorem commuting with the Bochner integral of that feature map.
- A bounded-support Gaussian mean-embedding recovery theorem: for finite measures `μ` and `ν` on `ℝ`, concentrated on a common compact interval, equality of their Gaussian feature mean embeddings implies equality of `∫ r, r ^ 2 ∂μ` and `∫ r, r ^ 2 ∂ν`. A stronger conclusion `μ = ν` is acceptable and preferred if it gives the moment corollary directly.
- A norm corollary: unequal second moments imply a strictly positive norm of the difference of Gaussian mean embeddings.

## Statement / milestones
Represent the Gaussian kernel by explicit weighted monomial coordinates, as in the current local `gaussianFeature`. Prove that equality of the two Bochner mean embeddings implies equality of every coordinate integral
`∫ r, exp (-r ^ 2) * r ^ m ∂μ = ∫ r, exp (-r ^ 2) * r ^ m ∂ν`
up to the nonzero normalization coefficient. Do not identify the `m = 2` coordinate directly with the raw second moment: it is an exponentially weighted moment.

For measures concentrated on `Set.Icc (-B) B`, use the full family of weighted moments and uniform polynomial/power-series approximation on the compact interval, or another standard characteristic-Gaussian-kernel argument, to recover equality of the measures or at least equality of the raw second moments. Expose a theorem whose assumptions are finite measures plus common bounded support and whose conclusion can be contraposed to show positivity of the embedding-distance norm from a nonzero second-moment contrast.

All central declarations must be sorry-free and axiom-clean. The final API should make the paper-local application a short bridge: establish bounded support of the two ratio laws, rewrite their second moments, invoke the recovery theorem, and conclude `0 < populationDiscrepancy` from norm nonnegativity and inequality.

## Standard reference
This is the standard characteristicness/moment-determinacy argument for the Gaussian kernel on compactly supported real probability measures. Equality of the explicit Gaussian feature embeddings yields all exponentially weighted polynomial moments; compact-support polynomial density (or an equivalent analytic transform argument) determines the weighted finite measure, and the strictly positive Gaussian weight then determines the original measure. Mathlib continuous-linear-map/Bochner-integral commutation and compact Stone--Weierstrass or polynomial approximation APIs are the expected foundations.

## Intended reuse
The immediate consumer is `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.generic_cover_separation`. Its paper-local proof has a nonzero raw second-moment contrast on each direct edge and must derive positivity of the Gaussian population discrepancy without adding a premise to the headline theorem.

The substrate should live in general Mathlib/Causalean-facing modules and be reusable whenever a Gaussian-kernel mean embedding is used to distinguish compactly supported real laws. It must not mention DAGs, mechanisms, interventions, ratio graphs, cover separation, or this paper's theorem.

## May assume / must derive
May assume that `μ` and `ν` are finite Borel measures on `ℝ`, that both are concentrated on the same bounded closed interval, and the standard measurability/integrability hypotheses needed for Bochner integration. Probability-measure hypotheses are acceptable if they materially simplify the API, provided the paper-local ratio laws can instantiate them.

Must derive coordinate/Bochner interchange, recovery from all weighted moments, equality of the raw second moments (or equality of measures), and the positive-distance contrapositive. Must not assume equality of raw moments, moment determinacy, Gaussian characteristicness, or the desired positive embedding distance.

The study must not import `CausalSmith/*_Research`. Before coordination, main should extract or generalize the current research-folder definitions `gaussianFeature`, `gaussianFeatureMap`, and `meanEmbedding` into a neutral module, or give the study an equivalent general interface. The paper-local RN-derivative identification and derivation of a common compact bound for the canonical ratio laws remain research-folder integration obligations rather than study assumptions about a causal model.

## Non-goals (optional)
Do not prove the paper's analytic edge-perturbation or generic-cover-separation theorem. Do not develop characteristic kernels on arbitrary spaces, unbounded-support Hamburger moment theory, general RKHS embeddings, or causal-model-specific ratio identities.

## Known building blocks (optional)
- Mathlib `lp.evalCLM` (or the corresponding continuous linear coordinate map) and continuous-linear-map commutation with Bochner integrals.
- The existing local explicit identity `gaussianFeature_inner` and unit-norm construction, to be extracted rather than imported from a research module.
- Compact-interval polynomial approximation / Stone--Weierstrass APIs, finite-measure extensionality via equality of integrals of continuous functions, dominated convergence, and multiplication by the strictly positive weight `exp (-r ^ 2)`.
- Norm nonnegativity plus `norm_eq_zero` for the final strict-positivity corollary.

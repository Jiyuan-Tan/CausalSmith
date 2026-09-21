# Substrate requirement: support-localized-moment-matched-mixture

## Goal
Extend the reviewed moment-matched prior-mixture machinery with support-localized likelihood hypotheses: if both priors are supported on `[-a,a]`, nonnegativity, density representation, and the exponential inner-product identity need hold only for parameters in that interval, while the same one-coordinate and finite-product total-variation bounds follow.

## Provides (API contract)
- A support-localized predictive-mixture density/absolute-continuity lemma, assuming component density and likelihood nonnegativity only when `|theta| <= a`.
- A support-localized quadratic mixture-likelihood identity or bound whose exponential Gram identity is assumed only for parameter pairs inside `[-a,a]`.
- Analogues of `momentMatchedMixture_tv_le_sqrt_tail` and `momentMatchedProductMixture_tv_le`, with the same conclusions but localized nonnegativity, density, and inner-product hypotheses.

The localized theorem must be a direct reusable entry point; consumers must not rebuild its support-almost-everywhere arguments.

## Statement / milestones
1. Derive all almost-everywhere support facts from `pi {theta | |theta| <= a} = 1`.
2. Prove that behavior outside prior support does not affect the prior-predictive mixture, including a localized mixture-density identity and its measurability/integrability facts.
3. Localize the four cross-term/Tonelli calculation so the exponential inner-product identity is used only almost everywhere under products of supported priors.
4. Derive the one-coordinate square-root exponential-series-tail TV bound using existing Scheffe/Cauchy--Schwarz machinery.
5. Tensorize it with the existing finite-product TV lemma to get the `d * sqrt(tail)` product bound.
6. Include a regression witness: `(1+theta)^Nplus * (1-theta)^Nminus` is nonnegative on `[-1,1]` but is negative at `theta = 2`, `Nplus = 0`, `Nminus = 1`. Priors supported on `[-1,1]` never use that value. The witness may be a proved or explicitly documented checked example and must not become a hypothesis.

## Standard reference
The standard moment-matching prior-mixture argument for nonsmooth-functional minimax lower bounds, including Cai--Low-style polynomial-approximation constructions. This is a measure-theoretic support localization of the reviewed exponential-Gram mixture argument, not a new statistical assumption.

## Intended reuse
The immediate consumer is a dense-regime fuzzy-hypothesis lower bound with a Poisson sign-count likelihood. The API must remain model-agnostic and reusable whenever a likelihood formula is valid or nonnegative only on the support of mixing priors.

During staging, the study may import reviewed zero-sorry modules under `CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax`; it must never import a paper `*_Research` module. Final Causalean coordination must colocate or cleanly extend the existing moment-matched-mixture API without a Causalean-to-CausalSmith dependency.

## May assume / must derive
May assume probability priors; support equalities on `[-a,a]`; moment matching through the degree; a globally measurable likelihood; a probability kernel; nonnegativity and density representation for supported parameters; and the exponential inner-product identity for supported parameter pairs.

Must derive all support-to-AE conversions, localized predictive-density and absolute-continuity facts, integrability/Tonelli justifications, the localized quadratic tail bound, and the one-coordinate and product TV bounds. Do not assume a final mixture-TV estimate, a consumer-specific certificate containing it, or any global nonnegativity/density/inner-product hypothesis.

## Non-goals
- Do not formalize Cai--Low prior existence, the fuzzy-hypothesis theorem, the paper Poisson embedding, target concentration, de-Poissonization, or the final lower bound.
- Do not import any `CausalSmith/*_Research` module or mention paper declarations in Lean.
- Do not alter already reviewed theorem statements merely to ease this wrapper.
- Do not add axioms, opaque certificates, `sorry`, or `admit`.

## Known building blocks
- `CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax.Analytic`: existing mixture-density, quadratic-energy, one-coordinate TV, and Scheffe/Cauchy--Schwarz results.
- `CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax.Product`: `tvDist_pi_iid_le` and the existing product theorem.
- Mathlib support/AE, product-measure, kernel integration, Tonelli/Fubini, and `Measure.pi` APIs.

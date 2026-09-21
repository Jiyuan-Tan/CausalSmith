# Substrate requirement: gaussian_mean_embedding_quantitative_moment_stability

## Goal
Build a reusable quantitative stability theorem bounding second-moment differences of compactly supported real probability laws by the norm distance between their explicit Gaussian feature mean embeddings, with a rigorous finite-truncation remainder.

## Provides (API contract)
- A general quantitative theorem for probability measures `μ` and `ν` supported in `[0,5]` using the explicit weighted-monomial Gaussian feature map: `|∫ r, r^2 ∂μ - ∫ r, r^2 ∂ν| ≤ 5151 * ‖meanEmbedding μ - meanEmbedding ν‖ + 10^(-15)` (an exactly rational equivalent is preferred).
- A contrapositive/lower-bound corollary turning a certified second-moment gap larger than the remainder into a positive explicit lower bound on Gaussian mean-embedding distance.
- The coordinate-evaluation and finite-sum inequalities needed to pass from embedding norm to the first 203 weighted moments.
- A verified degree-202 polynomial or power-series approximation of `r^2 * exp (r^2)` on `[0,5]`, including a factorial-tail bound strong enough for the displayed constants.

## Statement / milestones
Use the identity `r^2 = exp (-r^2) * (r^2 * exp (r^2))`. Approximate `r^2 * exp (r^2)` uniformly on `[0,5]` by a polynomial through degree 202. Equality is not assumed: derive a norm-controlled bound for each weighted moment from Gaussian feature coordinate evaluation, sum the finitely many coefficient bounds, and bound both measure remainders by the uniform approximation error. Package the resulting explicit inequality with constants no weaker than coefficient `5151` and additive error `10^(-15)`.

The proof must be compatible with the explicit Gaussian weighted-monomial feature representation already used by Causalean/CausalSmith. All central declarations must be sorry-free and axiom-clean. A more general theorem parameterized by support radius, truncation degree, and certified coefficient/tail bounds is welcome, provided the `[0,5]`, degree-202, `5151`, `10^(-15)` specialization is exported.

## Standard reference
This is the standard quantitative compact-support moment-recovery argument for Gaussian kernel mean embeddings: feature coordinates control exponentially weighted moments, a finite Taylor approximation of the reciprocal Gaussian weight converts those to a raw moment, and the exponential-series tail gives an explicit uniform error on a compact interval.

## Intended reuse
The immediate consumer is `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.sparse_witness_certificate`. That proof already has rational certificates for a sparse second-moment gap, a Gaussian MMD coefficient, and the degree-202 tail; the reusable theorem should make the paper-local step a short specialization and arithmetic discharge. The API should remain useful for quantitative identifiability arguments for arbitrary compactly supported real laws.

## May assume / must derive
May assume `μ` and `ν` are Borel probability measures concentrated on `Set.Icc 0 5`, standard Bochner integrability facts for the explicit Gaussian feature, and elementary real/exponential/factorial facts available in Mathlib. A general helper may accept separately verified polynomial coefficient and tail inequalities.

Must derive coordinate/Bochner interchange, weighted-moment norm bounds, finite-sum aggregation, the uniform degree-202 tail estimate, the stated raw second-moment stability inequality, and its positive-distance corollary. Must not assume equality of measures, moment determinacy, the desired moment bound, or the paper's sparse-witness conclusion.

## Non-goals (optional)
Do not formalize the causal model, DAG witnesses, analytic perturbation, genericity, arbitrary kernels, or unbounded-support moment problems. Do not import any `CausalSmith/*_Research` module or use the paper's theorem as an assumption.

## Known building blocks (optional)
- `lp.evalCLM` and continuous-linear-map commutation with Bochner integrals.
- Gaussian weighted-monomial coordinates and the qualitative compact-support recovery argument from the prior neutral Gaussian mean-embedding study (reuse by generalizing or deduplicating its declarations without importing a paper module).
- `Finset` norm/sum bounds, exponential Taylor series, factorial estimates, interval power bounds, and rational normalization/arithmetic tactics.
- Existing paper-local certificates named `sparseWeight_moment_certificate`, `sparseMmdRationalCertificate`, and `sparseMmdTailRationalCertificate` are consumer-side facts only; the reusable study must not import them.

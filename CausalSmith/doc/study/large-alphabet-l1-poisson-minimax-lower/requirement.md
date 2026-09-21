# Substrate requirement: large-alphabet-l1-poisson-minimax-lower

## Goal
Build a reusable all-estimator minimax lower bound for estimating the `L₁` distance between two unknown growing-alphabet distributions from independent Poissonized samples.

## Provides (API contract)
- `poissonizedTwoSampleL1Risk`: the squared-error risk of an arbitrary measurable estimator of `‖p - q‖₁` when the coordinate counts are independent with means `2 n p_i` and `2 n q_i`.
- `poissonizedTwoUnknownL1MinimaxRisk (n d : ℕ) : ℝ`: the infimum over all measurable estimators of the worst-case squared risk over pairs of probability vectors on `d` symbols.
- `poissonizedTwoUnknownL1_minimax_lower`: universal positive constants giving

       poissonizedTwoUnknownL1MinimaxRisk n d ≥ c · min(1, d / (n log(e n)))

  in the growing-alphabet regime `n ≥ c₀ d / log(e d)` and `log(e n) ≤ C₀ log(e d)` (or a formally equivalent constant-factor formulation).
- Projection and rescaling lemmas that expose the constructed prior pair, target separation, mixture-distance control, and the harmless change between Poisson intensity conventions.

## Statement / milestones
1. Formalize the two-unknown-distribution Poisson experiment: for probability vectors `p,q` on `Fin d`, observe mutually independent counts with laws `Pois(2 n p_i)` and `Pois(2 n q_i)` and estimate `∑ i, |p_i - q_i|` under squared loss.
2. Establish the lower bound on a lawful subexperiment. In particular, it is permitted to fix one distribution (for example, uniform `q`) and randomize approximate, nonnegative vectors for the other distribution, as in the cited paper. Prove the approximate-vector normalization/conditioning comparison needed to return to exact probability vectors; do not require both fuzzy priors to vary both distributions.
3. Prove the induced count-mixture laws are close using total variation or χ² bounds from matched moments, while the raw `L₁` targets and total masses concentrate around the required separated values. Apply normalization or conditioning only in the approximate-probability minimax bridge, rather than requiring exact normalized vectors inside the moment-matched mixture construction.
4. Convert mixture closeness and target concentration into a lower bound for every measurable estimator via a Le Cam/fuzzy-hypothesis reduction, yielding squared risk of order `min(1, d / (n log(e n)))` under the stated sample/alphabet regime.
5. The exported minimax theorem must retain the full two-unknown parameter space and estimator experiment. A proved fixed-`q` lower bound satisfies the construction step only when accompanied by the explicit submodel/simulation reduction showing that it lower-bounds the full two-unknown minimax risk. A simple two-point argument or an assumption of the desired large-alphabet theorem does not satisfy the contract.

## Standard reference
Jiao, Han, and Weissman (2018), *Minimax Estimation of the L₁ Distance*, Theorem 3 equation (24) and the Poissonized lower-bound argument in Section III, arXiv:1705.00807v7. The reference establishes the large-alphabet two-distribution lower-bound rate; this study must expose a reusable formal interface rather than assume the paper's theorem.

## Intended reuse
The immediate consumer is the all-estimator lower-bound branch of `stat_discrete_optimal_value_minimax_matched`. The substrate must remain a general theorem about two unknown discrete distributions and Poisson observations, with no causal variables, overlap assumptions, oracle-policy value, or run-specific types in its public interface.

## May assume / must derive
May reuse Mathlib/Causalean probability, product-measure, Poisson, total-variation, χ², Le Cam/minimax, and concentration infrastructure, plus the reusable absolute-value moment-prior duality substrate once available.

Must derive the fuzzy/moment-matching experiment, approximate-vector mass and target concentration, the normalization/conditioning bridge to exact probability vectors, closeness of the induced observation mixtures, and the all-estimator minimax reduction at the claimed rate. It may use a fixed-`q` submodel, but must prove its transfer to the supremum over exact pairs `(p,q)`. The conclusion may not be introduced through an opaque hypothesis, a new `axiom`, or a citation-only wrapper.

Existing staged declarations that demand two non-Dirac prior marginals or exact normalized random vectors in both fuzzy hypotheses are not part of this contract and may be deleted or replaced. Preserve and reuse proven generic components (including scalar moment duality, Poisson/Charlier mixture bounds, and Le Cam plumbing) where they fit the paper-faithful route.

## Non-goals (optional)
An upper-bound estimator, sharp constants, fixed-sample de-Poissonization beyond a reusable intensity-rescaling bridge, and any causal specialization are out of scope.

## Known building blocks (optional)
Prefer existing Causalean total-variation/Le Cam/χ²/minimax plumbing and standard Mathlib finite-probability and Poisson facts. The final promoted dependency closure must import only Mathlib/Causalean modules, contain no `sorry` or `admit`, and introduce no new axioms.

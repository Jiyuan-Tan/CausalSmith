# Substrate requirement: self-normalized Poisson bad-event moments

## Goal
Build a reusable, paper-neutral Lean package for quantitative first-, second-, and fourth-moment bounds on the bad event of a self-normalized Poisson deviation test.  Include the finite independent-product aggregation needed to retain the local scale determined by the sum of the Poisson means.

## Provides (API contract)
The promoted package should expose a coherent public API equivalent to the following; exact names and harmless strengthening may change to fit Causalean conventions.

- For `W` distributed according to `ProbabilityTheory.poissonMeasure lambda`, with `lambda >= 0` and `L >= 1`, measurable/integrable versions of the deviation and radius quantities
  `|W-lambda|` and `sqrt (W*L) + L`.
- A Poisson Bernstein/Chernoff tail bound derived from the Poisson moment-generating function, strong enough to show
  `P(|W-lambda| > sqrt(2*lambda*z) + 2*z) <= 2*exp(-z)` for `z >= 1`, or a quantitatively comparable stronger statement.
- Universal constants `H > 0`, `c > 0`, and finite constants `C_t` for `t = 1, 2, 4` such that the self-normalized bad event
  `Bad(H,L,lambda) = {W : |W-lambda| > (H/4) * (sqrt(W*L) + L)}`
  has weighted moments
  `E[(|W-lambda| + H*(sqrt(W*L)+L))^t * 1_Bad]`
  bounded by
  `C_t * exp(-c*L) * (sqrt(lambda*L)+L)^t`.
  The constants must be strong enough, after increasing the single universal `H` if necessary, to take `c >= 40` before finite-coordinate aggregation.
- The corresponding unconditioned moment bound, for `t = 1, 2, 4`, at scale
  `(sqrt(lambda*L)+L)^t`.  A statement for every fixed natural exponent up to four is welcome.
- A finite-product theorem for independent coordinates `W_i ~ Pois(lambda_i)`.  For a finite index type of cardinality at most a fixed `r`, let `BadAny` be the union of the coordinate self-normalized bad events and let
  `Z = sum_i (|W_i-lambda_i| + H*(sqrt(W_i*L)+L))`.
  Prove for `t = 1, 2` (and preferably `t = 4`) that
  `E[Z^t * 1_BadAny] <= C_{r,t} * exp(-20*L) * (sqrt((sum_i lambda_i)*L)+L)^t`.
  Constants may depend on the fixed finite cardinality bound `r` and exponent, but not on `lambda_i` or `L`.  The API must directly cover `r = 4`.
- Normalized corollaries for `m > 0`, `q_i >= 0`, and `lambda_i = m*q_i`, obtained by division by `m`: the local scale must be
  `sqrt((sum_i q_i)*L/m) + L/m`.

## Statement / milestones
1. Establish the exact Poisson exponential-moment identity needed for upper and lower Chernoff estimates, reusing an existing Mathlib/Causalean theorem when its signature fits exactly.

2. Derive a two-sided Bernstein tail with explicit universal numerical constants.  The result must include `lambda = 0`, where the Poisson count is almost surely zero.

3. Prove the deterministic comparison: outside a sufficiently high Bernstein threshold `z >= b*L`, the threshold `sqrt(2*lambda*z)+2*z` controls the self-normalized radius `sqrt(W*L)+L`, uniformly over `lambda >= 0`.  Equivalently, prove that the self-normalized bad event is contained in a sufficiently remote Bernstein-tail event once one universal `H` is fixed.

4. Integrate the tail to obtain weighted truncated moments of orders 1, 2, and 4.  The proof should use a layer-cake/tail-integral identity or an equivalent discrete summation argument and retain the multiplicative local scale `sqrt(lambda*L)+L`; a bare probability bound is insufficient.

5. Prove matching untruncated moment bounds.  These are needed for the non-bad coordinates when independent products are expanded or estimated by Holder/Cauchy--Schwarz.

6. Tensorize over a finite product of independent Poisson measures.  Combine the union over bad coordinates with independence or Holder/Cauchy--Schwarz, using fourth moments where necessary, to obtain the displayed `exp(-20*L)` first- and second-moment estimates at the aggregate local scale.

7. Package the scaling corollary for means `m*q_i`, including `m > 0`, coordinatewise `q_i >= 0`, and the sum-of-means identity.  Do not replace the local scale by a global constant or a bound depending only on the failure probability.

## Standard reference
The argument is standard Poisson concentration plus integration of exponential tails.  Suitable references are the Poisson moment-generating function, Chernoff/Bennett/Bernstein inequalities, layer-cake formulas for truncated moments, and finite-product Holder inequalities.  The Lean development must provide the quantitative consequences above rather than cite them as assumptions.

## Intended reuse
The immediate consumer has four independent pilot-count coordinates.  Its good event is exactly
`|W_i/m-q_i| <= (H/4) * (sqrt((W_i/m)*L/m)+L/m)` for every coordinate.  On the complement it needs first and second moments of the sum of coordinate deviations and radii at scale
`sqrt((sum_i q_i)*L/m)+L/m` with an `exp(-20*L)` factor.  The promoted result must remain independent of that estimator and be reusable for self-normalized Poisson pilots in other finite-category problems.

## May assume / must derive
May assume standard Mathlib/Causalean facts about `ProbabilityTheory.poissonMeasure`, real powers and square roots, Bochner/Lebesgue integrals of nonnegative functions, finite sums/products, product measures, independence of coordinate projections under a product measure, Holder/Cauchy--Schwarz, and basic exponential integration.

Must derive the Poisson tail estimate if no exact existing theorem is available, the deterministic threshold comparison, the weighted bad-event moment bounds, the unconditioned local moments, and the finite-product aggregation.  Do not expose any of these deliverables as a structure field, caller-supplied certificate, axiom, cited hypothesis, or unproved assumption.

## Non-goals
- Do not import or mention research modules, causal models, optimal policies, Jackson polynomials, factorial estimators, `Cell`, `pilotGoodEvent`, or minimax risk.
- Do not prove the paper-specific cell-statistic bias/variance theorem.
- Do not choose or expose a paper-specific tuning structure.  A universal numerical `H`, or an existence theorem returning one universal `H`, is appropriate.
- Do not weaken the weighted local-moment conclusion to a probability-only estimate or to a scale independent of `lambda`/`sum_i lambda_i`.

## Known building blocks
Search Mathlib and Causalean first for Poisson MGF/moments, Chernoff bounds, integrability of polynomial functions under `poissonMeasure`, product-measure coordinate independence, finite-sum power inequalities, and tail-integral identities.  Existing `Causalean.Stat.finiteCategoryPilot_bad_probability` is a probability-only IID categorical result and does not by itself provide the required weighted local Poisson moments.

## Extraction boundary
Develop and review the study implementation in its normal study location.  Promote the complete paper-neutral dependency closure into Causalean.  The promoted modules must not import any `CausalSmith/*_Research` module or encode the immediate consumer's four-cell vocabulary.

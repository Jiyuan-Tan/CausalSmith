# Substrate requirement: finite-finset-bernstein-gram

## Goal
Build reusable variance-sensitive exponential concentration for finitely indexed sums under a finite i.i.d. product law, together with a localized empirical-Gram coercivity corollary whose exponent scales as N times the local mass p.

## Provides (API contract)
- `iid_sum_bernstein_union_bound`: a finite-family Bernstein bound for coordinate sums under `Measure.pi (fun _ : Fin N => P)`, allowing coordinatewise envelope and variance bounds.
- `localized_empiricalGram_coercive`: a product-law corollary for a bounded local weight q and bounded finite-dimensional feature vector phi; from population Gram coercivity proportional to p, it controls failure of positivity of the empirical local count and empirical Gram coercivity relative to that count by `C d * exp (-c d lambda * N * p)`, with explicit constants depending only on dimension, the population coercivity constant, and envelope constants.

## Statement / milestones
1. For a finite type iota, probability measure P, measurable integrable statistics `g a`, centered envelopes `|g a x - integral (g a) P| <= b a`, centered second moments at most `sigma2 a`, positive thresholds `eta a`, and N > 0, prove under the Fin N product law that the event `exists a, eta a <= |sum_i g a (omega i) - N * integral (g a) P|` has measure at most the sum over a of `2 * exp (-(eta a)^2 / (2 * (2 * N * sigma2 a + b a * eta a)))` (up to an algebraically equivalent standard Bernstein form).
2. Specialize jointly to the local-count coordinate q and Gram coordinates `q x * phi_j x * phi_k x`, assuming `0 <= q <= 1`, `|phi_j| <= B`, `integral q P = p`, and population coercivity `lambda * p * sum_j v_j^2 <= sum_jk v_j v_k * integral (q * phi_j * phi_k) P`. Derive constants and an event inclusion showing, except with probability `C * exp (-c * N * p)`, that the empirical count is positive and the empirical Gram quadratic form is at least `(lambda / 2) * empiricalCount * sum_j v_j^2` for every v. The theorem may expose explicit small-N or N*p side conditions, provided a companion bound absorbs the complementary regime into C.
3. Supply the deterministic entrywise-to-quadratic perturbation and finite-union-bound lemmas needed by milestone 2, rather than assuming the final good event.

## Standard reference
The scalar estimate is the classical two-sided Bernstein inequality for independent bounded centered variables; the finite-family result is its union-bound corollary. The Gram result is the standard fixed-dimensional entrywise perturbation argument for an empirical second-moment matrix, using variance of a localized bounded summand of order p. See the Bernstein inequality treatment in Boucheron, Lugosi, and Massart, Concentration Inequalities, and the standard entrywise Gram perturbation argument used in local-polynomial regression.

## Intended reuse
The immediate consumer is `CausalSmith.Stat.LmtpThresholdAtomFrontier.total_gram_stabilization`: after transporting the arbitrary split block to a Fin-product law and instantiating q as the stratum/local-window indicator and phi as the monomial vector, the result must yield a tail of order `exp (-c * n * h * (delta + h)^kappa)`. The API should remain independent of clamp-law, threshold, and paper-specific definitions so it can be reused for localized random-design Gram matrices.

## May assume / must derive
May assume measurability, probability-law structure, N > 0, explicit pointwise envelope bounds, local mass p >= 0, and the stated population Gram coercivity. Must derive the variance-sensitive N*p exponent, the simultaneous finite-coordinate control, positivity of the empirical count in the nontrivial regime, and empirical coercivity relative to the realized count. Do not assume independence beyond the product law and do not assume the desired concentration event.

## Non-goals (optional)
No operator-norm matrix Bernstein, asymptotic limit theorem, paper-specific density calculation, arbitrary sample-split transport, or estimator-weight algebra is required. The consumer will prove its density-envelope population lower bound and perform its own product-law transport.

## Known building blocks (optional)
Proposed imports: `Causalean.Stat.Concentration.TailBounds.Bernstein`, `Causalean.Stat.Concentration.Matrix.IidSums`, `Causalean.Stat.Concentration.Matrix.InverseUnionBound`, `Causalean.Stat.Nonparametric.LocalPolynomial.GramCoercivity`, and core Mathlib finite-product measure and matrix APIs. Existing `bernstein_abs_ge` has the right variance-sensitive scalar exponent but is phrased for IIDSample initial segments; existing `iid_sum_union_bound` and `designMatrix_inv_concentration` provide the finite-family/matrix shape only with Chebyshev tails. No research-folder prerequisite needs extraction into the study: `iid_block_law_eq`, `CondDensityLaw`, shifted-power population coercivity, and the final l1/l2 weight assembly remain paper-side instantiations.

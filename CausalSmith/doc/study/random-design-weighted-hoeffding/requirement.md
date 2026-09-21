# Substrate requirement: random-design-weighted-hoeffding

## Goal
Build reusable conditional Hoeffding concentration for bounded centered marks under a finite i.i.d. product law when the coefficient array is measurable in the complete random design vector.

## Provides (API contract)
- `product_weighted_centered_conditional_mgf_le`: a conditional or integrated exponential-moment bound for `sum_i w(D_1,...,D_N)_i * (Y_i-m(D_i))`, conditional on the full design vector, with variance proxy `sum_i w_i^2 / 4`.
- `product_weighted_centered_tail_le`: under almost-sure positivity of the realized weight energy, the two-sided self-normalized bound `P(|sum_i w(Dvec)_i*(Y_i-m(D_i))| >= t*sqrt(sum_i w(Dvec)_i^2)) <= 2*exp(-2*t^2)` for `t >= 0`.
- If the clean proof is kernel-native, provide an `attachKernel` theorem plus a Standard-Borel conditional-expectation/disintegration corollary with the same conclusion.

## Statement / milestones
1. For a probability measure P on observations Omega, measurable design `D : Omega -> X`, measurable outcome `Y : Omega -> R` with `0 <= Y <= 1`, and measurable regression m satisfying `P[Y | comap D] = m o D` almost everywhere, derive the conditional Hoeffding exponential bound for one centered mark given its design. Expose Standard-Borel/countable-generation assumptions if required for regular conditional distributions.
2. Lift milestone 1 to `Measure.pi (fun _ : Fin N => P)`. Prove that conditioning on the complete design vector preserves conditional independence of the coordinate marks, or equivalently prove the result through a retained-design Markov-kernel/product factorization. The weights may depend jointly on every coordinate of the design vector.
3. Derive the two-sided tail bound by the conditional Chernoff argument and integrate over the design law. Handle zero energy honestly: either assume energy is positive almost everywhere or state a strict-threshold/zero-energy-safe variant and a positive-energy corollary.
4. Supply measurability of the realized energy, weighted centered sum, normalized event, and any finite-product kernel transport used by the theorem. No independence premise may simply assume the desired conditional product structure.

## Standard reference
This is conditional Hoeffding's lemma followed by tensorization conditional on covariates and the Chernoff bound: for independent responses with `Y_i in [0,1]` conditional on the full covariate vector, `sum_i w_i(Y_i-E[Y_i|D_i])` is conditionally sub-Gaussian with proxy `sum_i w_i^2/4`, even when the weights are arbitrary measurable functions of the full covariate vector.

## Intended reuse
The immediate consumer is `CausalSmith.Stat.LmtpThresholdAtomFrontier.honest_coverage_and_length`. Its local-polynomial weights depend on all observations' `(X,A)` designs, and the theorem supplies the uniform conditional tail needed for honest finite-sample coverage. It is also reusable for random-design regression, inverse-weighted estimators, and sample-split confidence intervals.

## May assume / must derive
May assume probability measures, finite index type, Standard-Borel hypotheses needed for disintegration, measurability, outcome range `[0,1]`, the conditional-expectation identity, and almost-sure positive realized weight energy. Must derive full-design conditional independence/product factorization, conditional centering, the `1/4` Hoeffding proxy, and the unconditional two-sided tail. Do not assume a conditional tail or conditional independence of residuals as an input unless the theorem is explicitly a lower-level kernel-native primitive accompanied by the requested conditional-expectation corollary.

## Non-goals
Do not import any `CausalSmith/*_Research` module. Do not define ClampLaw, local-polynomial weights, honest intervals, bandwidth rates, Gram events, or prove the paper headline.

## Known building blocks / proposed imports
Proposed imports: `Causalean.Mathlib.Probability.WeightedProduct` (already proves the matching square-moment and L1 bounds from conditional expectations), `Causalean.Stat.Concentration.TailBounds.Hoeffding`, `Mathlib.Probability.Moments.SubGaussian`, finite-product measure APIs, conditional expectation, and Standard-Borel Markov-kernel disintegration. `Causalean.Stat.Minimax.ChiSquaredKernel.attachKernel` or its underlying bind construction may be reused for retained-design laws. Existing paper-local `cond_weighted_bounded_sum_tail` handles only an already-given fiber family with independent coordinates and deterministic frozen weights; it is not a prerequisite and must not be imported. Research-folder consumer prerequisites that remain paper-local are `Helpers/RegressionVersion.lean` (the ClampLaw conditional-expectation identity), `Helpers/EstimatorMeasurable.lean` (measurable design-dependent local weights), and `Helpers/TotalGram.lean` (positive energy/Gram control).

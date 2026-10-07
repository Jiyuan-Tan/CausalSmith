module
public import Causalean.Stat.Concentration.VC.Rademacher.EntropyIntegral
public import Causalean.Stat.Concentration.VC.Rademacher.Conditional
public import Causalean.Stat.Concentration.VC.Rademacher.VarianceAdaptive

/-!
# Variance-adaptive Rademacher complexity of VC-type classes

For a countable class of measurable functions bounded by `U`, with population L² norm at most
`σ < U` and polynomial empirical L² covering numbers (base `A ≥ e`, exponent `v ≥ 1`), the
Rademacher complexity at sample size `n` is at most a universal constant times
`σ √(v L / n) + v U L / n`, where `L = log max(e, A U / σ)`. The proof conditions on the sample,
bounds Dudley's entropy integral up to the random empirical L² radius, and controls that radius by
a contraction argument.

## Main results

* `varianceAdaptiveRademacherComplexity_le` — the bound above (constant `8192`, half of
  `varianceAdaptiveVCConstant`).
* `empiricalRademacher_conditional_le` — the conditional (fixed-sample) entropy-integral estimate.
* `polynomialCover_entropyIntegral_le` — the Dudley entropy integral of a class with polynomial
  empirical covering numbers, after anchoring the class at one of its members (`anchoredClass`).
* `empiricalL2Radius_sq_le_uniformDeviation` — the squared empirical L² radius `empiricalL2Radius`
  is controlled by a uniform deviation of the squared class.

This file only gathers the three modules under `Rademacher/`.
-/

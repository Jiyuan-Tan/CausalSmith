module
public import Causalean.Estimation.ATT.Score.MeanZero
public import Causalean.Estimation.ATT.Score.FiniteVar

/-!
# The AIPW influence function for the average treatment effect on the treated

Population properties of the AIPW score for the average treatment effect on the treated (ATT).
The unnormalized moment is A·(Y − μ₀(X)) − (1 − A)·e(X)/(1 − e(X))·(Y − μ₀(X)) − A·θ, with μ₀
the control outcome regression and e the propensity score. Under the one-sided back-door ATT
assumptions, a positive treatment probability and integrability of the odds-weighted control
residual, the moment at the true nuisances and true ATT has mean zero under the law of the
observed triple; under one-sided overlap e ≤ 1 − ε and finite second moments of the outcome and
of the untreated potential outcome it is square-integrable.

## Main definitions

* `TreatedEstimationSystem`, `OneSidedOverlap`, `θ₀` — the estimation system, the overlap
  condition and the ATT target (`θ₀_eq_ATT` identifies it with the potential-outcome ATT).
* `aipwMomentATT`, `ψ_ATT` — the unnormalized moment and the influence function, which divides
  the moment by the treatment probability.

## Main results

* `aipw_mean_zero_ATT` — the moment at the truth has mean zero (`Score/MeanZero`).
* `aipw_finite_var_ATT` — the moment at the truth is square-integrable (`Score/FiniteVar`);
  `ipw_estimated_integrable` and `ipw_truth_integrable` give integrability of the odds-weighted
  corrections.
-/

public section

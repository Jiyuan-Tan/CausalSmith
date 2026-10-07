module
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Analytic
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
public import Causalean.Stat.Minimax.Mixture.MomentMatched.ExponentialEnergy
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Main
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized
/-!
# Moment-matched mixtures and fuzzy minimax lower bounds

The method of two fuzzy hypotheses with moment-matched priors, in a model-agnostic form. If two
priors supported in a bounded interval share their first `K` moments and the likelihoods have an
exponential inner-product form, the two prior-predictive mixtures are close in total variation:
within the square root of an explicit exponential-series tail for one coordinate, and within `d`
times that for a product of `d` independent coordinates. Combined with separation of the target
under the two priors, this yields explicit squared-error lower bounds for every estimator and for
the minimax risk over measurable estimators.

## Contents

* `FuzzyHypotheses` — `twoFuzzyHypotheses_bayesRisk_lower`,
  `twoFuzzyHypotheses_minimax_lower_standard`: if the two priors concentrate the target around
  centres at least `s` apart and the predictive mixtures are within 1/16 in total variation, the
  minimax squared risk is at least `11 s² / 512`.
* `ExponentialEnergy` — `exponentialPriorEnergy_quadratic_le_tail`: matching moments through
  degree `K` leaves an energy of at most four times the unmatched series tail.
* `Analytic`, `SupportLocalized` — `momentMatchedMixture_tv_le_sqrt_tail`, the one-coordinate
  total-variation bound, and its version needing the likelihood assumptions only on the support.
* `Product` — `momentMatchedProductMixture_tv_le`, the `d`-coordinate bound.
* `MarkedPoisson` (also reachable through `Main`) — finite signed moment certificates, their
  Jordan and zero-inflated priors, and geometric total-variation bounds for marked-Poisson
  count experiments.
* `BoundedMultivariate` — existence of finitely supported prior pairs on parameter triples with
  matched mixed moments through degree `3K` and a separated target, and the resulting
  marked-Poisson total-variation bounds.

This file only gathers the modules above.
-/

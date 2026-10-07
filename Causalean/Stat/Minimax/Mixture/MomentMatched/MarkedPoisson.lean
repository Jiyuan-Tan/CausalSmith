module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.AggregatePoisson
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Certificate
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.PalmSplit
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.PredictiveIdentities
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Product
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.TVBound
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.ZeroInflated

/-!
# Moment-matched marked-Poisson experiments

Total-variation bounds for mixtures of Poisson count experiments under priors built from a signed
measure with vanishing low-order moments. A normalized finite signed moment certificate (distinct
nodes, signed weights of total absolute mass one, zero moments through degree `K`) splits into
positive and negative Jordan priors with equal moments through degree `K`. In the four-count
label-gated marked-Poisson experiment, the total-variation distance between the two predictive
mixtures is at most the labelled intensity times the distance between two aggregate Poisson
mixtures, and that distance decays geometrically in `K` when the intensity times the support bound
is small relative to `K`.

## Main definitions and results

* `Certificate` — `NormalizedFiniteSignedMomentCertificate`, its `positivePrior` and
  `negativePrior`, `jordanPriors_moments_eq`, and the oriented priors with nonnegative target
  separation.
* `ZeroInflated` — `zeroInflatedPrior`: the variation measure tilted by `a / (p + a)` with the
  missing mass at zero; its support, mean and variance, also for i.i.d. products.
* `AggregatePoisson` — `exists_geometric_aggregatePoisson_jordan_tv_bound` for two independent
  Poisson counts with affine rates.
* `PalmSplit`, `PredictiveIdentities` — the experiment `markedPoissonLaw`, its predictive mixture,
  and the Palm-splitting identities relating it to the aggregate experiment.
* `TVBound` — `tvDist_markedPoissonPredictive_le_palm_aggregate` and
  `exists_geometric_markedPoisson_tv_bound`.
* `Product` — `markedPoissonProductPredictive_geometric_tv_le_of_one_coordinate_bound`: an assumed
  one-coordinate geometric bound tensorizes over `k` coordinates with a factor `k`; the
  one-coordinate bound is a hypothesis of this statement.
-/

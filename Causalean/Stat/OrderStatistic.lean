module
public import Causalean.Stat.OrderStatistic.Basic
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Causalean.Stat.OrderStatistic.Comparison
public import Causalean.Stat.OrderStatistic.DensityEnvelope
public import Causalean.Stat.OrderStatistic.Dirichlet
public import Causalean.Stat.OrderStatistic.Moments
public import Causalean.Stat.OrderStatistic.SimplexIntegrals
public import Causalean.Stat.OrderStatistic.WeightedConcomitant

/-!
# Finite-sample order statistics and spacings

Exact distribution theory for the order statistics of `n` i.i.d. uniform draws on `[0, 1]`, and
comparison bounds for general continuous laws. The sorted sample has density `n!` on the ordered
region and its spacings are uniform on the simplex (the Dirichlet law). Each interior gap between
adjacent order statistics has second moment exactly `2 / ((n+1)(n+2))`, and for even `n` the
expected sum of squares of every other gap is `n / ((n+1)(n+2))`. For a real law with density
between two positive constants on an interval, the CDF transform reduces its sorted gaps to
uniform ones, so the same moments hold up to the inverse squared density bounds.

## Main results

* `sorted_uniform_law` (`Basic`), `uniform_firstN_spacings_law` (`Dirichlet`) — the laws of the
  sorted sample and of its spacings.
* `uniform_gap_second_moment`, `uniform_alternating_gap_second_moment` (`Moments`) — the exact
  squared-gap moments.
* `cdf_pushforward_uniform01`, `iid_cdf_pushforward_uniform01` (`Comparison`) — the
  probability-integral transform for a law with a density.
* `real_gap_second_moment_bounds`, `real_alternating_gap_second_moment_bounds` (`Comparison`) —
  two-sided bounds on squared-gap moments under a density envelope.
* `withDensity_interval_mass_bounds` (`DensityEnvelope`) — interval masses are bounded by lengths
  times the density bounds.

`WeightedConcomitant` adds rank-weighted sums of marks attached to the sorted observations;
`SimplexIntegrals` and `CDFTransport` hold the supporting integrals and transport lemmas.
-/

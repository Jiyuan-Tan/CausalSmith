module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.AeDescent
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.BernsteinKernel
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ConcomitantCore
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ConcomitantExpectation
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ConcomitantTagged
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.OrderStatisticMoments
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerApproximation
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerCells
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerCurvature
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1Core
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1Error
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ReplacementLaw
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ReplacementSensitivity
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ReplacementVariance
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformOrderCDF
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformOrderMoments
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformTaggedRank

/-!
# Rank-weighted concomitants

Finite-sample theory of the statistic `∑ⱼ aⱼ Y₍ⱼ₎`, where the marks `Y` are sorted by a
continuously distributed coordinate and `aⱼ` are fixed cell weights. For marks in `[0, 1]` its
expectation is `∫₀¹ m(u) B_a(u) du`, where `m` is the conditional mean of the mark given the
uniformized sorting coordinate and `B_a` is the Bernstein kernel of the weights. For nonnegative
antitone weights (and marks in `[0, 1]`) its variance is at most `2 ∑ⱼ aⱼ²`. For the power
weights `aⱼ = (1 − j/N)^s − (1 − (j+1)/N)^s` with `s ≥ 1`, the Bernstein kernel approximates the
density `s (1 − u)^(s−1)` in L¹ within `2 √(s/N)`.

## Main definitions and results

* `rankConcomitant`, `bernsteinCell`, `powerCell`, `powerDensity` — the statistic, the Bernstein
  cell kernel, and the power weights with their limiting density.
* `integral_rankConcomitant_eq_bernstein` (`ConcomitantExpectation`) — the expectation formula.
* `variance_rankConcomitant_le_twice_sum_sq` (`ReplacementVariance`) — the variance bound, by
  independent replacement of one observation (`rankConcomitant_replacement_sensitivity`).
* `power_bernstein_L1` (`PowerL1`) — the L¹ approximation of the power density.
* `sum_powerCell_sq_le` (`PowerCells`) — `∑ⱼ aⱼ² ≤ s/N` for the power weights.
* `uniform_order_mean`, `uniform_order_second_moment` (`UniformOrderMoments`) — the `j`-th
  (zero-based) uniform order statistic has mean `(j+1)/(n+1)` and second moment
  `(j+1)(j+2)/((n+1)(n+2))`.
* `uniform_sorted_cdf_eq_binomial_tail` (`UniformOrderCDF`) — its CDF as a binomial tail.
-/

module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1Core
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerL1Error

/-!
# Bernstein approximation of power weights

For sample size `N ≥ 1` and a real power `s ≥ 1`, the Bernstein kernel built from the power cell
masses `(1 − j/N)^s − (1 − (j+1)/N)^s` approximates the density `s (1 − u)^(s−1)` on `[0, 1]`
with L¹ error at most `2 √(s/N)`. The proof writes the power as an integral of hinge functions
against its curvature, identifies the Bernstein kernel of a hinge cell with the CDF of a mixture
of two adjacent uniform order statistics, and bounds the resulting threshold error by the
mixture's standard deviation.

## Main results

* `power_bernstein_L1` (`PowerL1Error`) — the bound `2 √(s/N)`; `power_bernstein_L1_small` and
  `power_bernstein_L1_large` treat `s ≤ N` and `s > N`.
* `bernsteinCell_hinge_eq_adjacent_cdf` (`PowerL1Core`) — the hinge-cell Bernstein kernel is an
  adjacent order-statistic CDF.
* `bernsteinCell_power_eq_sub_curvature_hinge_integral` (`PowerL1Core`) — the curvature
  representation of the Bernstein power kernel.
-/

module
public import Causalean.Stat.UStatistic.LocalizedVariance.Basic
public import Causalean.Stat.UStatistic.LocalizedVariance.Bounds
public import Causalean.Stat.UStatistic.LocalizedVariance.Bridge
public import Causalean.Stat.UStatistic.LocalizedVariance.Coordinates
public import Causalean.Stat.UStatistic.LocalizedVariance.Counting
public import Causalean.Stat.UStatistic.LocalizedVariance.Main
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean
public import Causalean.Stat.UStatistic.LocalizedVariance.SumBound

/-!
# Localized variance bounds for order-two U-statistics

A variance bound for U-statistics whose kernel is concentrated on a small set, as with kernel
smoothing. Let `H` be a symmetric kernel with `|H| ≤ M · W` for a symmetric weight `0 ≤ W ≤ 1`, and
let `Uₙ` be the average of `H` over unordered pairs of `n ≥ 2` i.i.d. draws. Then

    Var(Uₙ) ≤ 16 M² (R/n + Q/n²),

where the pair mass `Q = E W(X₁, X₂)` and the squared row mass `R = E[(E[W(X₁, X₂) | X₁])²]`.
Keeping both scales matters: `Q` governs pairs that coincide, `R` governs pairs sharing one
index.

## Main definitions and results

* `LocalizedKernel`, `uStatistic`, `pairMass`, `rowMassSq` (`Basic`) — the setting.
* `centered_second_moment_le` (`Main`) — the displayed bound;
  `lintegral_centered_second_moment_le` (`Bridge`) — the same bound for the extended-nonnegative
  integral.
* `integral_uStatistic_eq_pair` (`Mean`) — the mean of `Uₙ` is the two-draw mean of the kernel.
* `pair_sum_variance_eq_covariance_sum`, `pair_sum_variance_le_localized_counts` (`SumBound`) —
  the covariance expansion over pairs of pairs and its bound.
* `covariance_disjoint_pairs_eq_zero`, `covariance_shared_pairs_le_rowMassSq`,
  `covariance_identical_pair_le_pairMass` (`Bounds`) — the three overlap cases.
* `Coordinates`, `Counting` — integrals over distinct sample coordinates and counts of overlapping
  index pairs.
-/

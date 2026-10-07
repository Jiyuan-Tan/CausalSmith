module
public import Causalean.Stat.UStatistic.Basic
public import Causalean.Stat.UStatistic.Hajek
public import Causalean.Stat.UStatistic.LocalizedVariance
public import Causalean.Stat.UStatistic.OrderM.Basic
public import Causalean.Stat.UStatistic.OrderM.CLT
public import Causalean.Stat.UStatistic.OrderM.ExactVariance
public import Causalean.Stat.UStatistic.OrderM.FirstDegenKernel
public import Causalean.Stat.UStatistic.OrderM.Hajek
public import Causalean.Stat.UStatistic.OrderM.MixedOrderBounds
public import Causalean.Stat.UStatistic.OrderM.MixedOrderCovariance
public import Causalean.Stat.UStatistic.OrderM.OrderTwo
public import Causalean.Stat.UStatistic.OrderM.PartialMatching
public import Causalean.Stat.UStatistic.OrderM.RemainderNegligible
public import Causalean.Stat.UStatistic.OrderM.RemainderSecondMoment
public import Causalean.Stat.UStatistic.OrderM.Variance
public import Causalean.Stat.UStatistic.Variance

/-!
# U-statistics

Asymptotic theory of U-statistics of fixed order `m` built from an i.i.d. sample. The kernel
splits into its mean, the sum of its `m` first-order Hoeffding projections, and a degenerate
residual; the U-statistic of the residual has `√n`-rescaled second moment of order `1/n`, so the
U-statistic is asymptotically linear with influence function `ψ` equal to the summed first
projections, and `√n (Uₙ − θ)` converges in distribution to the centred Gaussian with variance
`∫ ψ² dP` (for a symmetric order-two kernel, `4 ζ₁`). For a completely degenerate kernel the
rescaled second moment is computed exactly: `n · m! · ζₘ / n^(m)`, which is `2ζ/(n − 1)` when
`m = 2`.

## Contents

* `Basic` — order-two `uStatistic`, `uMean`, `uProj`, `uDegen`; `hoeffding_decomp`.
* `Variance` — `DegenKernel`; `IIDSample.integral_rescaled_sq` (the exact `2ζ/(n − 1)`), and
  `variance_offDiag_kernel_le` for a bounded kernel without degeneracy.
* `OrderM/Basic`, `OrderM/Hajek` — `uStatisticOrder` over injective `m`-tuples,
  `hajek_decomp_order`, `uStatisticOrder_isAsymLinear`.
* `OrderM/RemainderSecondMoment`, `OrderM/RemainderNegligible` —
  `IIDSample.integral_rescaled_order_sq_le` (the `C/n` bound for a first-order degenerate kernel)
  and `orderDegenerateNegligible_of_residual`.
* `OrderM/ExactVariance` — `IIDSample.integral_rescaled_order_sq_degen`.
* `OrderM/CLT`, `OrderM/OrderTwo` — `uStatisticOrder_clt` (remainder negligibility as a
  hypothesis), `uStatisticOrder_clt_of_explicit_conditions` (negligibility derived from
  square-integrability of the residual and integrability of the kernel sections), and the
  order-two case `uStatistic_clt_of_symmetric_explicit_conditions_via_orderM`.
* `OrderM/PartialMatching`, `OrderM/MixedOrderCovariance`, `OrderM/MixedOrderBounds` — expansion
  of the product of two U-statistics of different orders by the matching of shared indices.
* `LocalizedVariance` — a variance bound for order-two U-statistics with a kernel dominated by a
  localization weight.

Each limit theorem takes almost-everywhere measurability of the rescaled statistic as a hypothesis.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.Manski.IntervalForm

/-! # Manski Bounds

Worst-case (Manski) bounds on the average treatment effect of a binary treatment with an outcome
bounded in [lo, hi] and a discrete instrument, together with their sharpenings under shape
restrictions. Under consistency, bounded and integrable potential outcomes, and mean independence
of the potential outcomes from the instrument, the effect lies between the differences of the
stratum-wise worst-case bounds on the two arm means, for any pair of instrument values in the
support and hence for the best such pair. Monotone treatment response gives a nonnegative effect
and a tighter upper bound; monotone treatment selection bounds the effect above by the observed
treated-minus-control mean contrast; a monotone instrument (finite instrument space) gives
bounds by integrated running-maximum and running-minimum envelopes.

## Main results

* `manski_bounds_ATE`, `manski_bounds_ATE_ciSup` — the baseline bounds, for a pair of instrument
  values and in supremum/infimum form over the instrument support.
* `mtr_nonneg_ATE`, `mtr_bounds_ATE` — monotone treatment response, Y(0) ≤ Y(1) almost surely.
* `mts_bounds_ATE` — monotone treatment selection.
* `miv_bounds_ATE` — monotone instrumental variable, finite instrument space.
* `mtr_mts_bounds_ATE`, `mtr_miv_bounds_ATE` — combined restrictions: the effect lies between 0
  and the selection (respectively monotone-instrument) upper bound.
* `manski_ATE_mem_Icc`, `manski_ATE_mem_Icc_ciSup`, `mtr_mts_ATE_mem_Icc`,
  `mtr_miv_ATE_mem_Icc` — the same bounds as closed-interval membership.

Stratum means are normalized restricted integrals, equal to zero on a null stratum. These are
validity (outer-bound) results; sharpness of the intervals is not proved here.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.CutoffConstruct.VariableCutoff

/-! # Calibrating cutoffs for the treated-arm MSM upper bound

In the marginal sensitivity model with parameter Λ, the largest value of E[Y(1)] is reached by a
propensity that takes its extreme admissible values above and below a covariate-dependent outcome
cutoff. This module constructs that cutoff. It first proves the survival bridge: for treatment
indicator Z, propensity e(X) and conditional distribution function F(· | X) of the treated
outcome, E[Z·1{Y > c(X)} | X] = e(X)·(1 − F(c(X) | X)) almost surely, for constant and for
covariate-measurable cutoffs c. It then takes c to be the conditional quantile of the treated
outcome at the calibration level, which makes the treatment-weighted conditional survival match
the target survival function.

## Main results

* `treatedSurv_const_eq`, `treatedSurv_eq` (in `CutoffConstruct.ConstantCutoff`,
  `CutoffConstruct.VariableCutoff`) — the survival bridge for constant and variable cutoffs.
* `exists_calibrating_cutoff` — under two-sided overlap, a continuous treated conditional
  distribution function, and a calibration level strictly between 0 and 1 almost surely, a
  covariate-measurable calibrating cutoff exists.
* `msmUpperCalib_eq_cutoff_of_calibrating_cutoff_integrability` — for Λ > 1, the calibrated
  upper bound on E[Y(1)] equals the mean of a calibrating cutoff candidate, assuming the
  cutoff-dependent conditions only for measurable cutoffs that satisfy the calibration equation
  and assuming the cutoff-independent integrability conditions separately.
-/

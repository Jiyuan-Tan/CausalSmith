/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.SpectralCalculus_Part3

/-! # Spectral source condition and Tikhonov bias

This public facade exports the spectral construction on `L²(sigma(X))`, where
the normal operator is `T*T : L²(sigma(X)) → L²(sigma(X))`.  It derives a
single bias certificate uniform over all positive regularization levels and
provides the strong and weak Tikhonov bias bounds used by the primal rate.
-/

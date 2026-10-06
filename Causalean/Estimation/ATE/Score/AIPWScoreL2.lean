/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.Score.AIPWScoreL2.Truncation

/-!
Proves L² continuity of the AIPW score on the a.e. overlap-bounded nuisance
space, supplying the empirical-process input used by double machine learning
for the average treatment effect.

The file defines the overlap-dependent Lipschitz constant `K_AIPW`, proves the
a.e. pointwise score bound `aipw_score_diff_pointwise_bound`, shows
integrability of the residual-weighted cross term via
`yMuVal_residual_sq_integrable`, and packages the final
`o_p(1)` L²-score continuity theorem as `aipw_score_diff_isLittleOp_one`.
-/

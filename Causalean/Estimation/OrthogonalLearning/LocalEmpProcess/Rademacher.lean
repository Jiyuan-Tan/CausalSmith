/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher_Part3
/-!
# Global Rademacher bounds for the empirical process in orthogonal learning

A sufficient condition, in terms of ordinary (non-localized) Rademacher complexity, for the
uniform deviation condition used by the orthogonal-learning oracle inequalities: with
probability at least 1 − δ, for every target θ in the class and a fixed nuisance g, the
population excess risk of θ over θ₀ exceeds its empirical counterpart on the evaluation fold by
at most ρ_n·‖θ − θ₀‖ + ρ_n². If the loss is bounded by b over the class and continuous in θ, a
sequence of targets is dense in the class, and R_n bounds the Rademacher complexity of the
centred losses along that sequence at the evaluation-fold size m, then the condition holds with
ρ_n² = 2·R_n + 2·b·sqrt(2·log(1/δ)/m), and with ρ_n² = 2b when the fold is empty. Only the ρ_n²
term is used, so this bound does not give the fast localized rate; the sibling `Localized`
module does.

## Main definitions

* `RademacherBound` — R_n is nonnegative and bounds the population Rademacher complexity of the
  centred loss class on the evaluation fold.
* `UniformlyBoundedLoss`, `UniformlyBoundedLossAE`, `LossContinuousOnΘset` — the loss conditions.

## Main results

* `localEmpProcessModulus_of_bounded_rademacher` — the bound above for an everywhere-bounded loss.
* `localEmpProcessModulus_of_bounded_rademacher_ae` — the same for an almost-everywhere bound.
* `localEmpProcessModulus_singleton` — rate zero when the target class is {θ₀}.
-/

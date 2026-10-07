/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Localized_Part3
/-!
# Localized Rademacher bounds for the empirical process in orthogonal learning

Sufficient conditions, in terms of local Rademacher complexity, for the uniform deviation
condition used by the orthogonal-learning oracle inequalities: with probability at least 1 − δ,
for every target θ in the class and a fixed nuisance g, the population excess risk of θ over θ₀
exceeds its empirical counterpart on the evaluation fold by at most ρ_n·‖θ − θ₀‖ + ρ_n². The
main result is a version of Foster & Syrgkanis (2023, Lemma 14) for a separable target class:
if the loss is continuous in θ, the centred loss is bounded, Lipschitz in θ in a norm that
dominates its standard deviation, and its local Rademacher complexity has a sub-root envelope ψ
with positive critical radius, and a single peeling depth absorbs the concentration slack at
level δ, then the condition holds with ρ_n = (10·L + 3) times the critical radius of ψ at the
evaluation-fold size. A cruder bound ρ_n = sqrt(2b) follows from boundedness of the centred loss
by b alone.

## Main definitions

* `LocalizedRademacherRegime`, `LocalizedRademacherRegimeAE` — the bundled boundedness and
  sub-root-envelope assumptions, everywhere and almost everywhere.

## Main results

* `localEmpProcessModulus_of_localized_sharp` — the critical-radius rate.
* `localEmpProcessModulus_of_localized_sharp_ae` — the same rate from an almost-everywhere bound
  on the centred loss.
* `localEmpProcessModulus_of_localized_bounded`, `localEmpProcessModulus_of_localized_bounded_ae`
  — the constant rate sqrt(2b).
-/

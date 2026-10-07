/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MomentProblems.GaussianPerturbation.Main

/-!
# Non-Gaussian laws matching finitely many Gaussian moments

Finitely many moments cannot distinguish the Gaussian. For every cutoff `K ≥ 3` and every radius
`ρ > 0` there is a probability law on the real line that is not Gaussian, has mean zero and
variance one, lies within total-variation distance `ρ` of the standard Gaussian, has the same raw
moments and the same cumulants as the standard Gaussian through order `K`, has all absolute
moments finite, and has a divergent Hamburger–Carleman series (Carleman's sufficient condition
for moment determinacy; determinacy itself is not derived here). The law has density `1 + ε h` with respect to the standard Gaussian, where `h`
is a bounded nonzero function orthogonal to all monomials of degree at most `K`.

## Main results

* `exists_finiteMoment_near_gaussian_perturbation` — the existence statement above.
* `exists_bounded_gaussian_orthogonal_perturbation` — a nonzero bounded measurable function
  orthogonal under the standard Gaussian to every monomial through a given degree.
* `gaussianPerturbation_spec` — properties of the perturbed law `gaussianPerturbation`.
* `sourceCumulant_eq_of_rawMoment_eq_up_to` — equal raw moments through order `K` give equal
  cumulants through order `K`.
* `hamburgerCarlemanSeries_eq_top_of_evenMoment_le` — the even-moment growth bound
  `|m_(2n)| ≤ 2 (2n)^n` forces the Carleman series `hamburgerCarlemanSeries` to diverge.
-/

public section

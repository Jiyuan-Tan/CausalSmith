/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Nonparametric.MomentProblems.MomentCumulantInversion
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Raw moments, testing total variation, and the Hamburger--Carleman series

This module fixes the neutral notation used by the finite Gaussian perturbation
construction.  The total-variation definition is deliberately the measurable-set
supremum appearing in statistical testing, while the Carleman series uses the
positive even orders `2 * (s + 1)`.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Given [a real measure](hyp:ν) and [a nonnegative integer order](hyp:k), the [raw moment](goal)
is [given by integrating the corresponding power](step:1). -/
noncomputable def rawMoment (ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂ν

/-- For [a real measure](hyp:ν) at [a nonnegative integer order](hyp:k), [the raw-moment
notation equals the integral of the corresponding power](goal). -/
@[simp] theorem rawMoment_eq_integral (ν : Measure ℝ) (k : ℕ) :
    rawMoment ν k = ∫ x, x ^ k ∂ν := rfl

/-- Given [two measures on the same measurable outcome space](hyp:P,Q), the [testing
total-variation distance](goal) is [given by the supremum of their absolute probability gaps
over measurable events](step:1). -/
noncomputable def totalVariationDistance {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) : ℝ :=
  sSup {d : ℝ | ∃ A : Set α, MeasurableSet A ∧
    d = |(P A).toReal - (Q A).toReal|}

/-- For [two probability measures on the same measurable outcome space](hyp:P,Q), [the
set-supremum testing distance equals the library's indexed total-variation distance](goal). -/
theorem totalVariationDistance_eq_tvDist {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q = Causalean.Stat.tvDist P Q := by
  rw [totalVariationDistance, Causalean.Stat.tvDist, ← sSup_range]
  congr 1
  ext d
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨⟨A, hA⟩, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A.1, A.2, rfl⟩

/-- Given [a real measure](hyp:ν), the [explicit Hamburger--Carleman series](goal) is [given by
the sum of inverse roots of its positive even raw moments](step:1). -/
noncomputable def hamburgerCarlemanSeries (ν : Measure ℝ) : ℝ≥0∞ :=
  ∑' s : ℕ,
    (ENNReal.ofReal |rawMoment ν (2 * (s + 1))|).rpow
      (-(1 : ℝ) / (2 * (s + 1)))

/-- For [a real measure](hyp:ν), [the Hamburger--Carleman notation equals its explicit
integral-series formula](goal). -/
theorem hamburgerCarlemanSeries_eq (ν : Measure ℝ) :
    hamburgerCarlemanSeries ν =
      ∑' s : ℕ,
        (ENNReal.ofReal |∫ x, x ^ (2 * (s + 1)) ∂ν|).rpow
          (-(1 : ℝ) / (2 * (s + 1))) := rfl

end Causalean.Stat.MomentProblems

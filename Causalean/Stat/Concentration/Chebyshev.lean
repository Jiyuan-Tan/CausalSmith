/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Probability.Moments.Variance

/-!
# Chebyshev bounds with a supplied variance envelope

This module provides a real-valued Chebyshev probability bound for one
square-integrable statistic whose mean is known and whose variance has a
supplied upper bound. This differs from `iid_sum_chebyshev`, which specializes
to an i.i.d. sum with its exact variance and states the result as an `ENNReal`
measure bound.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- For [a real-valued error under a finite measure](hyp:Q,e), [a positive threshold](hyp:hr),
and [an integrable squared error](hyp:hi), [the measure of the strict absolute-error tail is at
most the second moment divided by the squared threshold](goal). -/
lemma absolute_error_tail_le_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    (e : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hi : Integrable (fun omega => e omega ^ 2) Q) :
    (Q {omega | r < |e omega|}).toReal ≤ (∫ omega, e omega ^ 2 ∂Q) / r ^ 2 := by
  have hsub : {omega | r < |e omega|} ⊆ {omega | r ^ 2 ≤ e omega ^ 2} := by
    intro omega homega
    have hs := sq_abs (e omega)
    have ha := abs_nonneg (e omega)
    change r < |e omega| at homega
    change r ^ 2 ≤ e omega ^ 2
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun omega => sq_nonneg (e omega)) hi (r ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  calc
    (Q {omega | r < |e omega|}).toReal * r ^ 2 ≤
        (Q {omega | r ^ 2 ≤ e omega ^ 2}).toReal * r ^ 2 :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsub) (sq_nonneg r)
    _ ≤ _ := by simpa [Measure.real, mul_comm] using hmarkov

/-- For a finite measure `Q` and a statistic `F` on the underlying space, if [`F` is
square-integrable under `Q`](hyp:hF), [the deviation threshold `a` is positive](hyp:ha), [`F`
has mean equal to `mean` under `Q`](hyp:hmean), and [the variance of `F` under `Q` is at most
the envelope `v`](hyp:hvar), then [the probability that `F` deviates from `mean` by more than
`a` in absolute value is at most `v/a²`](goal). -/
lemma probability_abs_sub_mean_gt_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsFiniteMeasure Q] (F : Ω → ℝ) (mean v a : ℝ)
    (hF : MemLp F 2 Q) (ha : 0 < a)
    (hmean : (∫ x, F x ∂Q) = mean)
    (hvar : variance F Q ≤ v) :
    (Q {x | a < |F x - mean|}).toReal ≤ v / a ^ 2 := by
  have hcheb := meas_ge_le_variance_div_sq hF ha
  have hsub :
      {x | a < |F x - mean|} ⊆
        {x | a ≤ |F x - ∫ y, F y ∂Q|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hmean]
    exact hx.le
  calc
    (Q {x | a < |F x - mean|}).toReal ≤
        (Q {x | a ≤ |F x - ∫ y, F y ∂Q|}).toReal :=
      measureReal_mono hsub
    _ ≤ (ENNReal.ofReal (variance F Q / a ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance F Q / a ^ 2 := by
      rw [ENNReal.toReal_ofReal]
      exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
    _ ≤ v / a ^ 2 := by
      exact div_le_div_of_nonneg_right hvar (sq_nonneg _)

end Causalean.Stat.Concentration

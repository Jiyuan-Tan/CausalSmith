/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Open positivity of unit-interval volume

This file shows that Lebesgue volume on the closed unit-interval subtype is positive on every
nonempty relatively open set.
-/

open MeasureTheory Set

noncomputable section

namespace Causalean.Mathlib.MeasureTheory

attribute [local instance] Measure.Subtype.measureSpace

/-- [Lebesgue volume on the closed unit interval is positive on every nonempty relatively open
set](goal). -/
instance unitIntervalVolumeIsOpenPosMeasure :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).IsOpenPosMeasure where
  open_pos U hU hUne := by
    rcases hUne with ⟨x, hx⟩
    rcases Metric.isOpen_iff.mp hU x hx with ⟨ε, hε, hball⟩
    let δ := min (ε / 4) (1 / 4 : ℝ)
    have hδ : 0 < δ := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have hδε : δ < ε :=
      (min_le_left _ _).trans_lt (by linarith)
    have hδq : δ ≤ 1 / 4 := min_le_right _ _
    let a : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 ((x : ℝ) - δ), by
        constructor
        · exact le_max_left _ _
        · exact max_le (by norm_num) (by linarith [x.property.2])⟩
    let b : Set.Icc (0 : ℝ) 1 :=
      ⟨min 1 ((x : ℝ) + δ), by
        constructor
        · exact le_min (by norm_num) (by linarith [x.property.1])
        · exact min_le_left _ _⟩
    have hab : a < b := by
      change max 0 ((x : ℝ) - δ) < min 1 ((x : ℝ) + δ)
      by_cases hm : (x : ℝ) ≤ 1 / 2
      · rw [min_eq_right (by linarith)]
        exact (max_lt_iff).2 ⟨by linarith [x.property.1], by linarith⟩
      · rw [max_eq_right (by linarith)]
        exact (lt_min_iff).2 ⟨by linarith [x.property.2], by linarith⟩
    have hsub : Set.Ioo a b ⊆ U := by
      intro y hy
      apply hball
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
      constructor
      · have hay : max 0 ((x : ℝ) - δ) < y := hy.1
        have : (x : ℝ) - δ ≤ max 0 ((x : ℝ) - δ) := le_max_right _ _
        linarith
      · have hyb : (y : ℝ) < min 1 ((x : ℝ) + δ) := hy.2
        have : min 1 ((x : ℝ) + δ) ≤ (x : ℝ) + δ := min_le_right _ _
        linarith
    apply ne_of_gt
    calc
      0 < volume (Set.Ioo a b) := by
        rw [unitInterval.volume_Ioo, ENNReal.ofReal_pos]
        exact sub_pos.mpr hab
      _ ≤ volume U := measure_mono hsub

end Causalean.Mathlib.MeasureTheory

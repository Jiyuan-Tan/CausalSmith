/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

/-! # Cancellation for reciprocal real densities

This file supplies a real-valued form of density cancellation: weighting a
measure by the nonnegative density `1 / h` and then by `h` recovers the
original measure whenever `h` is positive almost everywhere.
-/

open MeasureTheory

public section

namespace Causalean.Mathlib.MeasureTheory

/-- For [a measure](hyp:μ), [a measurable real function](hyp:h,hh), and the assumption that
[the function is positive almost everywhere](hyp:hpos), [weighting the measure first by
`max(1/h,0)` and then by `max(h,0)` recovers the original measure](goal). -/
theorem withDensity_one_div_ofReal_cancel
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
    (hh : Measurable h) (hpos : ∀ᵐ a ∂μ, 0 < h a) :
    (μ.withDensity (fun a => ENNReal.ofReal (1 / h a))).withDensity
        (fun a => ENNReal.ofReal (h a)) = μ := by
  rw [← withDensity_mul μ (by fun_prop) (by fun_prop)]
  rw [withDensity_congr_ae]
  · exact withDensity_one
  filter_upwards [hpos] with a ha
  simp only [Pi.mul_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / h a)]
  convert ENNReal.ofReal_one using 1
  field_simp

end Causalean.Mathlib.MeasureTheory

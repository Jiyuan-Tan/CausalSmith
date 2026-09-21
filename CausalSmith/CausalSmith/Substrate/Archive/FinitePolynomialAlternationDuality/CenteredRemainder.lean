/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Centered real remainders

This module isolates the Archimedean reduction of a real angle modulo a
positive step to a centered fundamental interval.
-/

public section

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- Every real angle differs from an integer multiple of `π/L` by at most
half of that positive step. -/
theorem exists_int_abs_sub_mul_pi_div_le
    {L : ℕ} (hL : 0 < L) (θ : ℝ) :
    ∃ m : ℤ,
      |θ - (m : ℝ) * (Real.pi / (L : ℝ))| ≤
        Real.pi / (2 * (L : ℝ)) := by
  -- Choose the nearest integer to `θ / (π/L)`. Mathlib's floor/round
  -- bounds give a remainder in `[-1/2,1/2]`; positivity of `π/L` then
  -- rescales that bound to the displayed interval.
  let d : ℝ := Real.pi / (L : ℝ)
  have hd : 0 < d := div_pos Real.pi_pos (by exact_mod_cast hL)
  refine ⟨round (θ / d), ?_⟩
  have hr : |θ / d - (round (θ / d) : ℝ)| ≤ (1 : ℝ) / 2 :=
    abs_sub_round (θ / d)
  have heq :
      θ - (round (θ / d) : ℝ) * d =
        d * (θ / d - (round (θ / d) : ℝ)) := by
    field_simp
  rw [show Real.pi / (L : ℝ) = d by rfl, heq, abs_mul, abs_of_pos hd]
  calc
    d * |θ / d - (round (θ / d) : ℝ)| ≤ d * ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hr hd.le
    _ = Real.pi / (2 * (L : ℝ)) := by
      dsimp [d]
      field_simp

end CausalSmith.Substrate.FinitePolynomialAlternationDuality

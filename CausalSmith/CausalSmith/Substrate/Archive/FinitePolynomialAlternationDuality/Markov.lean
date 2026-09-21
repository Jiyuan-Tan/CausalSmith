/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.Affine
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.MarkovUnit

/-!
# Markov's derivative inequality on a compact real interval

This module transports the unit-interval Markov inequality through the affine
equivalence from `[-1,1]` to an arbitrary nondegenerate interval `[r,s]`.
-/

public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- If `r < s` and a real polynomial has degree at most `L`, then its derivative
supremum norm on `[r,s]` is at most `2 L²/(s-r)` times the polynomial's
supremum norm on that interval. -/
theorem markov_derivative_Icc
    (Q : Polynomial ℝ) {r s : ℝ} (hrs : r < s)
    (L : ℕ) (hQ : Q.natDegree ≤ L) :
    intervalSupNorm (fun x => Q.derivative.eval x) r s ≤
      (2 * (L : ℝ) ^ 2 / (s - r)) *
        intervalSupNorm (fun x => Q.eval x) r s := by
  let P := pullbackToUnitInterval Q r s
  have hP : P.natDegree ≤ L :=
    (natDegree_pullbackToUnitInterval_le Q r s).trans hQ
  have hunit := markov_derivative_unitInterval P L hP
  have hden : 0 < s - r := sub_pos.mpr hrs
  have hhalf : 0 < (s - r) / 2 := by positivity
  rw [intervalSupNorm_le_iff Q.derivative.continuous.continuousOn hrs.le]
  intro x hx
  let t : ℝ := (2 * x - (r + s)) / (s - r)
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hden).2
      linarith [hx.1]
    · apply (div_le_iff₀ hden).2
      linarith [hx.2]
  have hmap : ((s - r) / 2) * t + (r + s) / 2 = x := by
    dsimp [t]
    field_simp [ne_of_gt hden]
    ring
  have hpoint :=
    ((intervalSupNorm_le_iff P.derivative.continuous.continuousOn
      (by norm_num : (-1 : ℝ) ≤ 1)).mp hunit) t ht
  have hpull :
      |((s - r) / 2) * Q.derivative.eval x| ≤
        (L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s := by
    simpa [P, derivative_eval_pullbackToUnitInterval, hmap,
      intervalSupNorm_pullbackToUnitInterval Q hrs] using hpoint
  have hscaled :
      ((s - r) / 2) * |Q.derivative.eval x| ≤
        (L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s := by
    simpa [abs_mul, abs_of_pos hhalf] using hpull
  calc
    |Q.derivative.eval x| ≤
        ((L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s) /
          ((s - r) / 2) := (le_div_iff₀ hhalf).2 (by
            simpa [mul_comm] using hscaled)
    _ = (2 * (L : ℝ) ^ 2 / (s - r)) *
          intervalSupNorm (fun x => Q.eval x) r s := by
      field_simp [ne_of_gt hden]

end CausalSmith.Substrate.FinitePolynomialAlternationDuality

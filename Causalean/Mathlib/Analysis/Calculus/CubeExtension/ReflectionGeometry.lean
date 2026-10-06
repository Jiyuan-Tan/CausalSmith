module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# Geometry of inward samples at a cube face

An exterior point in a thin collar of the left face has finitely many
reflected sample points inside the closed cube. These affine samples are the
arguments of the one-sided reflection operator.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The inward reflection sample](goal) of [a point x](hyp:x) across the left
face in [coordinate i](hyp:i), with [dilation index q](hyp:q), in [dimension
d](hyp:d), replaces the i-th coordinate of x by −1 + (q + 1)·(−1 − x_i) and keeps
every other coordinate; it reflects a point just outside the face to a point
q + 1 times as far inside. -/
def leftFaceSample (d : ℕ) (i : Fin d) (q : ℕ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  Function.update x i (-1 + ((q : ℝ) + 1) * (-1 - x i))

/-- [The open exterior collar](goal) at the left face of the normalized cube in
[dimension d](hyp:d), for [derivative order m](hyp:m) and [coordinate i](hyp:i),
is the set of points whose i-th coordinate lies strictly between
−1 − 1/(m + 1) and −1 and whose other coordinates lie strictly between −1 and
1. -/
def leftOpenCubeCollar (d m : ℕ) (i : Fin d) : Set (Fin d → ℝ) :=
  {x | ∀ j : Fin d,
    if j = i then x j ∈ Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
    else x j ∈ Set.Ioo (-1 : ℝ) 1}

/-- If [x lies in the open exterior collar at the left face in coordinate
i](hyp:hx), then [for every dilation index q ≤ m, the inward reflection sample of
x lies in the open normalized cube](goal). -/
theorem leftFaceSample_mem_openCube {d m : ℕ} (i : Fin d)
    (q : Fin (m + 1)) (x : Fin d → ℝ)
    (hx : x ∈ leftOpenCubeCollar d m i) :
    leftFaceSample d i q x ∈ openCube d := by
  have hxi : x i ∈ Set.Ioo
      (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1) := by
    simpa [leftOpenCubeCollar] using hx i
  have ht0 : 0 < -1 - x i := by linarith [hxi.2]
  have ht1 : -1 - x i < 1 / ((m : ℝ) + 1) := by linarith [hxi.1]
  have hq : ((q : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_le_of_lt q.isLt)
  have hprod : (((q : ℕ) : ℝ) + 1) * (-1 - x i) < 1 := by
    calc
      _ ≤ ((m : ℝ) + 1) * (-1 - x i) :=
        mul_le_mul_of_nonneg_right hq ht0.le
      _ < ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left ht1 (by positivity)
      _ = 1 := by field_simp
  have hpos : 0 < (((q : ℕ) : ℝ) + 1) * (-1 - x i) :=
    mul_pos (by positivity) ht0
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa [leftFaceSample] using
      (show -1 < -1 + (((q : ℕ) : ℝ) + 1) * (-1 - x i) ∧
        -1 + (((q : ℕ) : ℝ) + 1) * (-1 - x i) < 1 by
          constructor <;> linarith)
  · simpa [leftFaceSample, leftOpenCubeCollar, hji] using hx j

/-- If [coordinate j differs from the face coordinate i](hyp:hji), then [the
inward reflection sample of a point leaves its j-th coordinate unchanged](goal). -/
theorem leftFaceSample_other {d : ℕ} (i j : Fin d) (q : ℕ)
    (x : Fin d → ℝ) (hji : j ≠ i) :
    leftFaceSample d i q x j = x j := by
  simp [leftFaceSample, hji]

/-- If [a point x lies on the left face, that is its i-th coordinate equals
−1](hyp:hxi), then [every inward reflection sample of x equals x](goal). -/
theorem leftFaceSample_fixed {d : ℕ} (i : Fin d) (q : ℕ)
    (x : Fin d → ℝ) (hxi : x i = -1) :
    leftFaceSample d i q x = x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [leftFaceSample, hxi]
  · exact leftFaceSample_other i j q x h

/-- If [the i-th coordinate of x lies in `[-1 - 1/(m+1), -1]`](hyp:hxi), so that
x is at most 1/(m + 1) outside the left face, and [every other coordinate of x
lies in `[-1,1]`](hyp:hother), then [for every dilation index q ≤ m the inward
reflection sample of x lies in the closed normalized cube](goal). -/
theorem leftFaceSample_mem_cube {d m : ℕ} (i : Fin d)
    (q : Fin (m + 1)) (x : Fin d → ℝ)
    (hxi : x i ∈ Set.Icc
      (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1))
    (hother : ∀ j : Fin d, j ≠ i → -1 ≤ x j ∧ x j ≤ 1) :
    leftFaceSample d i q x ∈ cube d := by
  /- At coordinate `i`, put `t = -1 - x i`. The collar gives
  `0 ≤ t ≤ 1/(m+1)` and `q < m+1`, hence
  `-1 ≤ -1 + (q+1)t ≤ 0 ≤ 1`. Other coordinates are unchanged. -/
  have ht0 : 0 ≤ -1 - x i := by
    exact sub_nonneg.mpr (by linarith [hxi.2])
  have ht1 : -1 - x i ≤ 1 / ((m : ℝ) + 1) := by
    linarith [hxi.1]
  have hq : ((q : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_le_of_lt q.isLt)
  have hprod : (((q : ℕ) : ℝ) + 1) * (-1 - x i) ≤ 1 := by
    calc
      _ ≤ ((m : ℝ) + 1) * (-1 - x i) :=
        mul_le_mul_of_nonneg_right hq ht0
      _ ≤ ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = 1 := by field_simp
  change ∀ j : Fin d, leftFaceSample d i (q : ℕ) x j ∈ Set.Icc (-1 : ℝ) 1
  intro j
  by_cases hji : j = i
  · subst j
    have hnonneg : 0 ≤ (((q : ℕ) : ℝ) + 1) * (-1 - x i) :=
      mul_nonneg (by positivity) ht0
    simpa [leftFaceSample] using
      (show -1 ≤ -1 + (((q : ℕ) : ℝ) + 1) * (-1 - x i) ∧
        -1 + (((q : ℕ) : ℝ) + 1) * (-1 - x i) ≤ 1 by
          constructor <;> linarith)
  · rw [leftFaceSample_other i j (q : ℕ) x hji]
    exact hother j hji

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

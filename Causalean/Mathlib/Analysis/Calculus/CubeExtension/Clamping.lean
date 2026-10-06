module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# Coordinatewise retraction onto the normalized cube

Clamping each coordinate to `[-1,1]` fixes the cube and is nonexpansive in
the supremum norm. This is the extension map for the zero-order Hölder case.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [Coordinatewise clamping](goal) in [dimension d](hyp:d) sends [a point
x](hyp:x) to the point whose i-th coordinate is max(−1, min(1, x_i)), that is,
x_i truncated to `[-1,1]`; the result lies in the normalized cube. -/
def cubeClamp (d : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => max (-1) (min 1 (x i))

/-- [Every coordinatewise clamped point lies in the normalized closed cube
`[-1,1]^d`](goal). -/
theorem cubeClamp_mem_cube (d : ℕ) (x : Fin d → ℝ) : cubeClamp d x ∈ cube d := by
  intro i
  change -1 ≤ cubeClamp d x i ∧ cubeClamp d x i ≤ 1
  simp only [cubeClamp]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- [Coordinatewise clamping leaves fixed](goal) [every point already in the
normalized cube](hyp:hx). -/
theorem cubeClamp_fixed {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ cube d) :
    cubeClamp d x = x := by
  ext i
  have hi := hx i
  change -1 ≤ x i ∧ x i ≤ 1 at hi
  simp [cubeClamp, min_eq_right hi.2, max_eq_right hi.1]

/-- [Coordinatewise clamping is nonexpansive for the supremum norm: the clamped
images of two points are no farther apart than the points themselves](goal). -/
theorem cubeClamp_nonexpansive (d : ℕ) (x y : Fin d → ℝ) :
    ‖cubeClamp d x - cubeClamp d y‖ ≤ ‖x - y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
  intro i
  have h := (LipschitzWith.projIcc (a := (-1 : ℝ)) (b := 1) (by norm_num)).dist_le_mul
    (x i) (y i)
  calc
    ‖(cubeClamp d x - cubeClamp d y) i‖ ≤ ‖x i - y i‖ := by
      simpa [cubeClamp, Subtype.dist_eq, Set.coe_projIcc, Real.dist_eq, Real.norm_eq_abs]
        using h
    _ ≤ ‖x - y‖ := by
      simpa using norm_le_pi_norm (x - y) i

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

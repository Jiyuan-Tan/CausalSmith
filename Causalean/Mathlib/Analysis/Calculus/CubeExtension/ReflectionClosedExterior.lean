module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionOperator

/-!
# Regularity on the closed exterior face slab

The finite reflection sum inherits within-set regularity on the closed
exterior part of a one-face cube collar. This includes its edges and corners,
where ambient derivatives of an arbitrary representative need not exist.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The closed exterior slab](goal) of the normalized cube's left collar in
[dimension d](hyp:d), for [derivative order m](hyp:m) and [coordinate i](hyp:i),
is the part of that collar whose i-th coordinate is at most −1, that is, on or
beyond the left face. -/
def leftClosedExteriorCollar (d m : ℕ) (i : Fin d) : Set (Fin d → ℝ) :=
  leftCubeCollar d m i ∩ {x | x i ≤ -1}

/-- If [the reflection weights a sum to one](hyp:ha), so that the reflection
reproduces constants, and [a response u is m times continuously differentiable
within the closed cube](hyp:hu), then [the one-face reflection of u across the
left face in coordinate i is m times continuously differentiable within the
closed exterior slab of the left collar](goal), including all exterior edges
and corners. -/
theorem leftFaceReflection_contDiffOn_closedExterior (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : (∑ q : Fin (m + 1), a q) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d)) :
    ContDiffOn ℝ m (leftFaceReflection d m i a u)
      (leftClosedExteriorCollar d m i) := by
  /- On the slab, each affine inward sample lies in the closed cube, so
  `hu.comp` gives regularity of the finite sum. At the face, all samples
  equal the base point and `ha` identifies the sum with the `else` branch.
  Use `ContDiffOn.congr` to replace the sum by `leftFaceReflection`. -/
  have hsample (q : Fin (m + 1)) :
      ContDiff ℝ m (leftFaceSample d i q) := by
    rw [contDiff_pi]
    intro j
    by_cases h : j = i
    · subst j
      simpa [leftFaceSample] using
        (show ContDiff ℝ m (fun x : Fin d → ℝ =>
          -1 + ((q : ℝ) + 1) * (-1 - x i)) by fun_prop)
    · simpa [leftFaceSample, h] using
        (show ContDiff ℝ m (fun x : Fin d → ℝ => x j) by fun_prop)
  have hsum : ContDiffOn ℝ m
      (fun x => ∑ q : Fin (m + 1), a q * u (leftFaceSample d i q x))
      (leftClosedExteriorCollar d m i) := by
    apply ContDiffOn.sum
    intro q hq
    apply ContDiffOn.mul contDiffOn_const
    exact hu.comp (hsample q).contDiffOn (by
      intro x hx
      apply leftFaceSample_mem_cube i q x
      · have hmem : x i ∈ Set.Icc
            (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1 := by
          simpa [leftCubeCollar] using hx.1 i
        exact ⟨hmem.1, hx.2⟩
      · intro j hji
        simpa [leftCubeCollar, hji] using hx.1 j)
  apply hsum.congr
  intro x hx
  by_cases hxi : x i < -1
  · simp [leftFaceReflection, hxi]
  · have hface : x i = -1 := le_antisymm hx.2 (le_of_not_gt hxi)
    simp [leftFaceReflection, hxi, leftFaceSample_fixed i _ x hface,
      ← Finset.sum_mul, ha]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

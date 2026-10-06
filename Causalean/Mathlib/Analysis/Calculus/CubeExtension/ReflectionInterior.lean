module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionOperator

/-!
# Interior regularity of a one-face reflection

Every inward sample of an open collar point lies in the open cube. Thus the
finite reflection sum inherits all available interior derivatives of the
original response. This is the interior half of the face-gluing argument;
matching the derivatives at the face is a separate obligation.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [a response u is m times continuously differentiable within the closed
cube](hyp:hu), then [for any reflection weights a the one-face reflection of u
across the left face in coordinate i is m times continuously differentiable on
the open exterior collar](goal). -/
theorem leftFaceReflection_contDiffOn_openCollar (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (hu : ContDiffOn ℝ m u (cube d)) :
    ContDiffOn ℝ m (leftFaceReflection d m i a u)
      (leftOpenCubeCollar d m i) := by
  /- On the open collar `x i < -1`, the reflection is the finite sum of
  `a q * u (leftFaceSample d i q x)`. Each sample is affine and maps the
  collar into `openCube d` by `leftFaceSample_mem_openCube`. Restrict `hu`
  to the open cube, use the composition rule for `ContDiffOn`, and sum. -/
  have hopen : openCube d ⊆ cube d := by
    intro x hx j
    exact ⟨(hx j (Set.mem_univ j)).1.le, (hx j (Set.mem_univ j)).2.le⟩
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
      (leftOpenCubeCollar d m i) := by
    apply ContDiffOn.sum
    intro q hq
    apply ContDiffOn.mul contDiffOn_const
    exact (hu.mono hopen).comp (hsample q).contDiffOn
      (fun x hx => leftFaceSample_mem_openCube i q x hx)
  apply hsum.congr
  intro x hx
  have hxi : x i < -1 := by
    have hmem : x i ∈ Set.Ioo
        (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1) := by
      simpa [leftOpenCubeCollar] using hx i
    exact hmem.2
  simp [leftFaceReflection, hxi]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

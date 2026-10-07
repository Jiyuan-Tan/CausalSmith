module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionInterior

/-!
# Quantitative estimates for inward face samples

The affine samples used by one-face reflection have a uniform Lipschitz
constant. On the exterior collar, their weighted sum inherits a value bound
from the intrinsic cube ball. These estimates are inputs to the higher-jet
reflection bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The inward reflection sample with dilation index q is Lipschitz for the
supremum norm with constant q + 1](goal): it moves two points apart by at most
q + 1 times their distance. -/
theorem leftFaceSample_lipschitz (d : ℕ) (i : Fin d) (q : ℕ)
    (x y : Fin d → ℝ) :
    ‖leftFaceSample d i q x - leftFaceSample d i q y‖ ≤
      ((q : ℝ) + 1) * ‖x - y‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by positivity) (norm_nonneg (x - y)))).2
  intro j
  by_cases hji : j = i
  · subst j
    have heq : (leftFaceSample d i q x - leftFaceSample d i q y) i =
        -((q : ℝ) + 1) * (x - y) i := by
      simp [leftFaceSample, Pi.sub_apply]
      ring
    rw [heq, norm_mul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (q : ℝ) + 1 by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) i) (by positivity)
  · have heq : (leftFaceSample d i q x - leftFaceSample d i q y) j =
        (x - y) j := by
      simp [leftFaceSample_other i j q x hji,
        leftFaceSample_other i j q y hji, Pi.sub_apply]
    rw [heq]
    calc
      ‖(x - y) j‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) j
      _ ≤ ((q : ℝ) + 1) * ‖x - y‖ := by
        nlinarith [norm_nonneg (x - y), Nat.cast_nonneg (α := ℝ) q]

/-- If [a response u lies in the intrinsic Hölder ball of
order m, exponent s and radius L on the normalized cube](hyp:hu), then at
[every point x of the open exterior collar](hyp:hx) [the one-face reflection of u
has absolute value at most (Σ_q |a_q|)·L](goal). -/
theorem leftFaceReflection_abs_le_openCollar (d m : ℕ) (s : ℝ)
    (i : Fin d) (a : Fin (m + 1) → ℝ)
    (u : (Fin d → ℝ) → ℝ) (L : ℝ)
    (hu : CubeHolderBall d m s L u)
    (x : Fin d → ℝ) (hx : x ∈ leftOpenCubeCollar d m i) :
    |leftFaceReflection d m i a u x| ≤
      (∑ q : Fin (m + 1), |a q|) * L := by
  have hbound (q : Fin (m + 1)) : |u (leftFaceSample d i q x)| ≤ L := by
    have hs : leftFaceSample d i q x ∈ cube d := by
      intro j
      have hj := leftFaceSample_mem_openCube i q x hx j trivial
      exact ⟨hj.1.le, hj.2.le⟩
    have hb := hu.derivBound 0 (Nat.zero_le m) (Fin.elim0)
      (leftFaceSample d i q x) hs
    simpa [coordJetOn, iteratedFDerivWithin_zero_apply] using hb
  have hxi : x i < -1 := by
    have hi : x i ∈ Set.Ioo
        (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1) := by
      simpa [leftOpenCubeCollar] using hx i
    exact hi.2
  simp only [leftFaceReflection, if_pos hxi]
  calc
    |∑ q : Fin (m + 1), a q * u (leftFaceSample d i q x)| ≤
        ∑ q : Fin (m + 1), |a q * u (leftFaceSample d i q x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin (m + 1), |a q| * |u (leftFaceSample d i q x)| := by
      simp_rw [abs_mul]
    _ ≤ ∑ q : Fin (m + 1), |a q| * L := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hbound q) (abs_nonneg _)
    _ = (∑ q : Fin (m + 1), |a q|) * L := by rw [Finset.sum_mul]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

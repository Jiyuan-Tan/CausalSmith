module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarEstimates
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarModulus
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceGluing
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionQuantitative
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionSampleJets

/-!
# Intrinsic Hölder control after one face reflection

This module packages the regularity and quantitative jet estimates of a
single face reflection on the enlarged closed cube collar. It is the local
input for iterating reflections over all faces.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1) and [the reflection weights a
satisfy the moment conditions Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha),
then for [the left face in coordinate i](hyp:i) [there is a positive constant C
such that the one-face reflection of every response u in the intrinsic Hölder
ball of order m, exponent s and radius L ≥ 0 on the normalized cube lies in the
intrinsic Hölder ball of radius C·L on the closed left collar](goal). The
constant depends only on the dimension, m, s, the face and the weights. -/
theorem exists_leftFaceReflection_collar_holder_constant
    (d m : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        HolderBallOn (leftCubeCollar d m i) m s (C * L)
          (leftFaceReflection d m i a u) := by
  /- Regularity comes from `leftFaceReflection_contDiffOn_collar`.
  Combine `exists_leftFaceReflection_collar_derivBound_constant` and
  `exists_leftFaceReflection_collar_modulus_constant` using the sum of their
  positive constants. The regularity field comes from
  `leftFaceReflection_contDiffOn_collar`. -/
  obtain ⟨Cd, hCd, hd⟩ :=
    exists_leftFaceReflection_collar_derivBound_constant d m s i a ha
  obtain ⟨Ch, hCh, hh⟩ :=
    exists_leftFaceReflection_collar_modulus_constant d m s hs hs1 i a ha
  refine ⟨Cd + Ch, add_pos hCd hCh, ?_⟩
  intro u L hL hu
  refine ⟨leftFaceReflection_contDiffOn_collar d m i a ha u hu.regularity, ?_, ?_⟩
  · intro j hj f x hx
    exact (hd u L hL hu j hj f x hx).trans (by
      nlinarith [mul_nonneg (le_of_lt hCh) hL])
  · intro f x hx y hy
    exact (hh u L hL hu f x hx y hy).trans (by
      have hp : 0 ≤ ‖x - y‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
      nlinarith [mul_nonneg (mul_nonneg (le_of_lt hCd) hL) hp])

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

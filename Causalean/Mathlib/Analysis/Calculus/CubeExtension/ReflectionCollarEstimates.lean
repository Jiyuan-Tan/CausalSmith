module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarCubeEstimates
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarRestriction
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarSideEstimates
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceGluing
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionQuantitative

/-!
# Quantitative bounds on a closed one-face reflection collar

The open exterior estimates extend to the closed exterior by continuity of
intrinsic jets. Bounds on the cube and exterior then combine on the collar.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), then [there is a positive
constant C such that, for every response u in the intrinsic Hölder ball of order
m, exponent s and radius L ≥ 0 on the normalized cube, every intrinsic
coordinate jet of order at most m of the one-face reflection of u is bounded in
absolute value by C·L throughout the closed left collar](goal). -/
theorem exists_leftFaceReflection_collar_derivBound_constant
    (d m : ℕ) (s : ℝ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        DerivBoundOn (leftCubeCollar d m i) m (C * L)
          (leftFaceReflection d m i a u) := by
  obtain ⟨Ce, hCe, he⟩ :=
    exists_leftFaceReflection_closedExterior_jet_bound d m s i a ha
  obtain ⟨Cc, hCc, hc⟩ :=
    exists_leftFaceReflection_cube_jet_control_constant d m s i a ha
  refine ⟨Ce + Cc, add_pos hCe hCc, ?_⟩
  intro u L hL hu
  intro j hj f x hx
  have hnorm :
      ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
        (leftCubeCollar d m i) x‖ ≤ (Ce + Cc) * L := by
    rw [← leftClosedExteriorCollar_union_cube d m i] at hx
    rcases hx with hx | hx
    · exact (he u L hL hu j hj x hx).trans (by nlinarith [mul_nonneg (le_of_lt hCc) hL])
    · exact ((hc u L hL hu).1 j hj x hx).trans
        (by nlinarith [mul_nonneg (le_of_lt hCe) hL])
  have hcoord :=
    (iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
      (leftCubeCollar d m i) x).le_opNorm
        (fun k => Pi.single (f k) (1 : ℝ))
  have hcoord' :
      |coordJetOn (leftCubeCollar d m i) j
        (leftFaceReflection d m i a u) f x| ≤
      ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
        (leftCubeCollar d m i) x‖ := by
    simpa [coordJetOn, Pi.norm_single] using hcoord
  exact hcoord'.trans hnorm

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarCrossing
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarCubeEstimates
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarSideEstimates

/-!
# Hölder modulus across a reflected cube face

The top-order derivative has a controlled modulus on each closed side of the
face. A segment crossing point combines those bounds for opposite-side pairs.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [0 < s](hyp:hs) and [the reflection weights a
satisfy the moment conditions Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha),
then [there is a positive constant C such that, for every response u in the
intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the normalized
cube, the top-order intrinsic coordinate jets of the one-face reflection of u
have an s-Hölder modulus with coefficient C·L throughout the closed left
collar](goal). -/
theorem exists_leftFaceReflection_collar_modulus_constant
    (d m : ℕ) (s : ℝ) (hs : 0 < s)
    (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        TopHolderOn (leftCubeCollar d m i) m s (C * L)
          (leftFaceReflection d m i a u) := by
  obtain ⟨Ce, hCe, he⟩ :=
    exists_leftFaceReflection_closedExterior_top_modulus d m s hs i a ha
  obtain ⟨Cc, hCc, hc⟩ :=
    exists_leftFaceReflection_cube_jet_control_constant d m s i a ha
  refine ⟨Ce + Cc, add_pos hCe hCc, ?_⟩
  intro u L hL hu
  let J := iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
    (leftCubeCollar d m i)
  have hcross (x y : Fin d → ℝ)
      (hxe : x ∈ leftClosedExteriorCollar d m i)
      (hyc : y ∈ cube d) :
      ‖J x - J y‖ ≤ (Ce + Cc) * L * ‖x - y‖ ^ s := by
    obtain ⟨z, -, hze, hzc, hxz, hzy⟩ :=
      exists_leftFaceReflection_crossing_point d m i x y hxe hyc
    have hp : ‖x - z‖ ^ s ≤ ‖x - y‖ ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) hxz hs.le
    have hq : ‖z - y‖ ^ s ≤ ‖x - y‖ ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) hzy hs.le
    calc
      ‖J x - J y‖ ≤ ‖J x - J z‖ + ‖J z - J y‖ := by
        calc
          ‖J x - J y‖ = ‖(J x - J z) + (J z - J y)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      _ ≤ Ce * L * ‖x - z‖ ^ s + Cc * L * ‖z - y‖ ^ s :=
        add_le_add (he u L hL hu x hxe z hze) ((hc u L hL hu).2 z hzc y hyc)
      _ ≤ (Ce + Cc) * L * ‖x - y‖ ^ s := by
        have hp' : Ce * L * ‖x - z‖ ^ s ≤ Ce * L * ‖x - y‖ ^ s := by
          gcongr
        have hq' : Cc * L * ‖z - y‖ ^ s ≤ Cc * L * ‖x - y‖ ^ s := by
          gcongr
        nlinarith
  have hpair (x y : Fin d → ℝ)
      (hx : x ∈ leftCubeCollar d m i)
      (hy : y ∈ leftCubeCollar d m i) :
      ‖J x - J y‖ ≤ (Ce + Cc) * L * ‖x - y‖ ^ s := by
    rw [← leftClosedExteriorCollar_union_cube d m i] at hx hy
    rcases hx with hxe | hxc
    · rcases hy with hye | hyc
      · exact (he u L hL hu x hxe y hye).trans (by
          have : 0 ≤ Cc * L * ‖x - y‖ ^ s := by positivity
          nlinarith)
      · exact hcross x y hxe hyc
    · rcases hy with hye | hyc
      · have h := hcross y x hye hxc
        simpa only [norm_sub_rev] using h
      · exact ((hc u L hL hu).2 x hxc y hyc).trans (by
          have : 0 ≤ Ce * L * ‖x - y‖ ^ s := by positivity
          nlinarith)
  intro f x hx y hy
  have hnorm := hpair x y hx hy
  have hcoord := (J x - J y).le_opNorm
    (fun k => Pi.single (f k) (1 : ℝ))
  have hcoord' :
      |coordJetOn (leftCubeCollar d m i) m
          (leftFaceReflection d m i a u) f x -
        coordJetOn (leftCubeCollar d m i) m
          (leftFaceReflection d m i a u) f y| ≤ ‖J x - J y‖ := by
    simpa [J, coordJetOn, Pi.norm_single, sub_apply] using hcoord
  exact hcoord'.trans hnorm

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

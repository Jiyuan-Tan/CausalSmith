module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetNorm
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCollarRestriction

/-!
# Quantitative reflected jets on the original cube

The reflected function agrees with the input on the original cube. Its
within-collar jets there consequently inherit the full intrinsic cube bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), then [there is a positive
constant C such that, for every response u in the intrinsic Hölder ball of order
m, exponent s and radius L ≥ 0 on the normalized cube, the within-collar Fréchet
derivatives of the one-face reflection of u of every order at most m have
operator norm at most C·L at every cube point, and its order-m within-collar
derivative is s-Hölder with coefficient C·L between any two cube points](goal). -/
theorem exists_leftFaceReflection_cube_jet_control_constant
    (d m : ℕ) (s : ℝ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        (∀ j ≤ m, ∀ x ∈ cube d,
          ‖iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
            (leftCubeCollar d m i) x‖ ≤ C * L) ∧
        (∀ x ∈ cube d, ∀ y ∈ cube d,
          ‖iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
              (leftCubeCollar d m i) x -
            iteratedFDerivWithin ℝ m (leftFaceReflection d m i a u)
              (leftCubeCollar d m i) y‖
            ≤ C * L * ‖x - y‖ ^ s) := by
  obtain ⟨C, hC, hcontrol⟩ := exists_full_intrinsic_jet_bounds d m s
  refine ⟨C, hC, ?_⟩
  intro u L hL hu
  obtain ⟨hbound, hmod⟩ := hcontrol u L hL hu
  constructor
  · intro j hj x hx
    rw [leftFaceReflection_withinJet_eq_cube d m j i a ha u
      hu.regularity hj x hx]
    exact hbound j hj x hx
  · intro x hx y hy
    rw [leftFaceReflection_withinJet_eq_cube d m m i a ha u
      hu.regularity le_rfl x hx,
      leftFaceReflection_withinJet_eq_cube d m m i a ha u
      hu.regularity le_rfl y hy]
    exact hmod x hx y hy

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

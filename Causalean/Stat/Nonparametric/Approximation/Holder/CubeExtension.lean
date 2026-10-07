module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Extension
public import Causalean.Stat.Nonparametric.Approximation.Holder.Defs

/-!
# Ambient Hölder-ball bridge for intrinsic cube data

This module translates the extension theorem for intrinsic cube jets into the
standard ambient-jet Hölder-ball vocabulary used by nonparametric models.
-/

public section

namespace Causalean.Stat.Nonparametric.Approximation.Holder

open Causalean.Mathlib.Analysis.Calculus.CubeExtension
open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For a [dimension](hyp:d) and a [smoothness index](hyp:β) that is [positive](hyp:hβ),
[there is a positive constant, depending only on the dimension and the smoothness index, such
that every function in the intrinsic cube Hölder ball of that smoothness with any nonnegative
radius has an ambient function that agrees with it on the cube and belongs to the standard
ambient Hölder ball of the same smoothness on the cube, with radius the constant times the
original radius](goal). -/
theorem exists_holderBallStd_extension (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d (⌈β⌉₊ - 1)
          (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) L u →
        ∃ U : (Fin d → ℝ) → ℝ,
          Set.EqOn U u (cube d) ∧
          Causalean.Stat.Nonparametric.HolderBallStd
            U β (A * L) (cube d) := by
  have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ
  have hcast : ((⌈β⌉₊ - 1 : ℕ) : ℝ) = (⌈β⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
  have hs : 0 < β - ((⌈β⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.ceil_lt_add_one hβ.le]
  have hs1 : β - ((⌈β⌉₊ - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [hcast]
    linarith [Nat.le_ceil β]
  obtain ⟨A, hA, hExt⟩ :=
    exists_global_holder_extension d (⌈β⌉₊ - 1)
      (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) hs hs1
  refine ⟨A, hA, ?_⟩
  intro u L hL hu
  obtain ⟨U, hEq, hSmooth, hBounds, hMod⟩ := hExt u L hL hu
  refine ⟨U, hEq, ?_⟩
  exact ⟨hSmooth.contDiffOn,
    (fun j hj x hx => hBounds j hj x),
    (fun x hx y hy => hMod x y)⟩

end Causalean.Stat.Nonparametric.Approximation.Holder

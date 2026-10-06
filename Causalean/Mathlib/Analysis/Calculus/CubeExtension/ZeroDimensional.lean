module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# Intrinsic cube extension in dimension zero

The cube in a zero-dimensional space is a singleton, so its data already have a
constant global representative with the required uniform bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [any derivative order m](hyp:m) and [any exponent s](hyp:s), [there is a
positive constant A such that, in dimension zero, every response u in the
intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the cube has a
global extension U that agrees with u on the cube, is m times continuously
differentiable, has derivatives of every order at most m bounded in operator
norm by A·L, and whose order-m derivative is s-Hölder with coefficient
A·L](goal). -/
theorem exists_global_holder_extension_zero (m : ℕ) (s : ℝ) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : (Fin 0 → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall 0 m s L u →
        ∃ U : (Fin 0 → ℝ) → ℝ,
          Set.EqOn U u (cube 0) ∧
          ContDiff ℝ m U ∧
          (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j U x‖ ≤ A * L) ∧
          (∀ x y,
            ‖iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y‖
              ≤ A * L * ‖x - y‖ ^ s) := by
  refine ⟨1, by norm_num, ?_⟩
  intro u L hL hu
  let U : (Fin 0 → ℝ) → ℝ := fun _ => u 0
  have hU : U = u := by
    funext x
    exact congrArg u (Subsingleton.elim 0 x)
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact congrFun hU x
  · exact contDiff_const
  · intro j hj x
    by_cases hj0 : j = 0
    · subst j
      have hzero : (0 : Fin 0 → ℝ) ∈ cube 0 := by
        intro i
        exact i.elim0
      have hb := hu.derivBound 0 (Nat.zero_le m) (Fin.elim0) 0 hzero
      simpa [U, coordJetOn, iteratedFDerivWithin_zero_apply,
        iteratedFDeriv_zero_apply] using hb
    · simp [U, iteratedFDeriv_const_of_ne hj0, hL]
  · intro x y
    have hxy : x = y := Subsingleton.elim x y
    subst y
    simp only [sub_self, norm_zero]
    positivity

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

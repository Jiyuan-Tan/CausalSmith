module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.FixedCubeNeighborhood
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoff
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ZeroOrder

/-!
# Controlled extension of intrinsic cube Hölder data

An intrinsic cube Hölder ball admits an ambient representative with uniform
quantitative derivative bounds. The representative agrees with the original
response on the cube; the original response itself need not have valid ambient
boundary derivatives.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [a Hölder
exponent s](hyp:s) with [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1), [there is a
positive constant A such that every response u in the intrinsic Hölder ball of
order m, exponent s and radius L ≥ 0 on the closed normalized cube has an
extension U to the whole space that agrees with u on the cube, is m times
continuously differentiable, has ambient derivatives of every order at most m
bounded in operator norm by A·L everywhere, and whose order-m derivative is
globally s-Hölder with coefficient A·L](goal). The constant depends only on d,
m and s. -/
theorem exists_global_holder_extension (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∃ U : (Fin d → ℝ) → ℝ,
          Set.EqOn U u (cube d) ∧
          ContDiff ℝ m U ∧
          (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j U x‖ ≤ A * L) ∧
          (∀ x y,
            ‖iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y‖
              ≤ A * L * ‖x - y‖ ^ s) := by
  by_cases hm : m = 0
  · subst m
    exact exists_global_holder_extension_order_zero d s hs
  obtain ⟨lo, hi, B, hmargin, hB, hneighborhood⟩ :=
    exists_fixedCubeNeighborhood_holder_constant d m s hs
  obtain ⟨C, hC, hcutoff⟩ :=
    exists_global_holder_cutoff_of_rectBox d m s hs hs1 lo hi hmargin
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro u L hL hu
  obtain ⟨v, hv, hvball⟩ := hneighborhood u L hL hu
  obtain ⟨U, hU, hSmooth, hBounds, hMod⟩ :=
    hcutoff v (B * L) (mul_nonneg hB.le hL) hvball
  refine ⟨U, ?_, hSmooth, ?_, ?_⟩
  · intro x hx
    exact (hU hx).trans (hv hx)
  · intro j hj x
    simpa only [mul_assoc] using hBounds j hj x
  · intro x y
    simpa only [mul_assoc] using hMod x y

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

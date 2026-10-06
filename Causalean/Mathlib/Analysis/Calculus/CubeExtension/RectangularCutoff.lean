module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffModulus

/-!
# Controlled cutoff from a rectangular neighborhood

An intrinsic Hölder ball on a closed box containing the normalized cube in
its interior admits a globally controlled representative agreeing on the cube.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [a Hölder
exponent s](hyp:s) with [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1), if [the box with
corners lo, hi strictly contains the normalized cube in every
coordinate](hyp:hmargin), then [there is a positive constant C such that every
response v in the intrinsic Hölder ball of radius R ≥ 0 on the box has a global
representative U that agrees with v on the cube, is m times continuously
differentiable, has ambient derivatives of every order at most m bounded in
operator norm by C·R everywhere, and whose order-m derivative is globally
s-Hölder with coefficient C·R](goal). -/
theorem exists_global_holder_cutoff_of_rectBox
    (d m : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (rectBox lo hi) m s R v →
        ∃ U : (Fin d → ℝ) → ℝ,
          Set.EqOn U v (cube d) ∧
          ContDiff ℝ m U ∧
          (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j U x‖ ≤ C * R) ∧
          (∀ x y,
            ‖iteratedFDeriv ℝ m U x - iteratedFDeriv ℝ m U y‖
              ≤ C * R * ‖x - y‖ ^ s) := by
  obtain ⟨χ, hχ, hone, hsupp, B, hB, hχbound⟩ :=
    exists_rectangular_smooth_cutoff d m lo hi hmargin
  obtain ⟨C₁, hC₁, hjet⟩ :=
    exists_rectCutoffExtension_jet_constant d m s lo hi hmargin
      χ hχ hsupp B hB.le hχbound
  obtain ⟨C₂, hC₂, hmod⟩ :=
    exists_rectCutoffExtension_modulus_constant d m s hs hs1 lo hi hmargin
      χ hχ hsupp B hB.le hχbound
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro v R hR hv
  refine ⟨rectCutoffExtension lo hi χ v, ?_, ?_, ?_, ?_⟩
  · exact (rectCutoffExtension_contDiff_eqOn_cube d m lo hi hmargin
      χ v hχ hsupp hone hv.regularity).2
  · exact (rectCutoffExtension_contDiff_eqOn_cube d m lo hi hmargin
      χ v hχ hsupp hone hv.regularity).1
  · intro j hj x
    exact (hjet v R hR hv j hj x).trans (mul_le_mul_of_nonneg_right
      (le_max_left C₁ C₂) hR)
  · intro x y
    have hpow : 0 ≤ R * ‖x - y‖ ^ s := by positivity
    calc
      ‖iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) x -
          iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) y‖
          ≤ C₂ * R * ‖x - y‖ ^ s := hmod v R hR hv x y
      _ ≤ max C₁ C₂ * R * ‖x - y‖ ^ s := by
        nlinarith [le_max_right C₁ C₂]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffExteriorJets
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffLocalJets

/-!
# Uniform jet bounds for a localized rectangular response

Coordinatewise intrinsic bounds on a closed box control all ambient jets
of the zero extension obtained from a fixed smooth cutoff.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff

/-- If [the box with corners lo, hi strictly contains the normalized
cube](hyp:hmargin), [χ is smooth](hyp:hχ) [with closed support inside the open
box](hyp:hsupp), and [its ambient derivatives of every order up to m + 1 are
bounded in operator norm by B ≥ 0](hyp:hB,hχbound), then [there is a positive
constant C such that for every response v in the intrinsic Hölder ball of order
m, exponent s and radius R ≥ 0 on the closed box, every ambient derivative of
order at most m of the zero extension of χ·v from the box has operator norm at
most C·R everywhere](goal). -/
theorem exists_rectCutoffExtension_jet_constant (d m : ℕ) (s : ℝ)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i)
    (χ : (Fin d → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    (B : ℝ) (hB : 0 ≤ B)
    (hχbound : ∀ j ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (rectBox lo hi) m s R v →
        ∀ j ≤ m, ∀ x,
          ‖iteratedFDeriv ℝ j (rectCutoffExtension lo hi χ v) x‖ ≤ C * R := by
  obtain ⟨C, hC, hlocal⟩ :=
    exists_rectCutoffExtension_local_jet_constant d m s lo hi hmargin
      χ hχ B hB hχbound
  refine ⟨C, hC, ?_⟩
  intro v R hR hv j hj x
  by_cases hx : x ∈ rectOpenBox lo hi
  · exact hlocal v R hR hv j hj x hx
  · rw [rectCutoffExtension_iteratedFDeriv_eq_zero_of_not_mem hsupp hx j]
    simpa using mul_nonneg hC.le hR

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

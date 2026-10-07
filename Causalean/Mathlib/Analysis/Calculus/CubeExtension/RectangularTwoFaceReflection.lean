module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularUpperFaceReflection

/-!
# Controlled reflection across both faces of one coordinate

Successive lower- and upper-face reflections extend an intrinsic Hölder ball
to a larger rectangular box while preserving its values on the starting box.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [0 < s](hyp:hs) and [the box with corners lo, hi has
positive side lengths](hyp:hbox), then for [derivative order m](hyp:m) and
[coordinate i](hyp:i) [there is a positive constant C such that every response u
in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the box
agrees on the box with a response in the intrinsic Hölder ball of radius C·L on
the box enlarged by collars across both faces of coordinate i (first the left
collar, then the right collar of the resulting box)](goal). The constant depends
only on the box, m, s and i. -/
theorem exists_rectTwoFaceReflection_holder_constant {d : ℕ}
    (lo hi : Fin d → ℝ) (m : ℕ) (s : ℝ)
    (hs : 0 < s)
    (hbox : ∀ j, lo j < hi j) (i : Fin d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        HolderBallOn (rectBox lo hi) m s L u →
        ∃ v : (Fin d → ℝ) → ℝ,
          Set.EqOn v u (rectBox lo hi) ∧
          HolderBallOn
            (rectBox (rectLeftLower lo hi m i)
              (rectRightUpper (rectLeftLower lo hi m i) hi m i))
            m s (C * L) v := by
  let lower := rectLeftLower lo hi m i
  have hlower : ∀ j, lower j < hi j := by
    intro j
    by_cases hji : j = i
    · subst j
      have hp : 0 < hi i - lo i := sub_pos.mpr (hbox i)
      have hw : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) := by
        positivity
      dsimp [lower, rectLeftLower]
      simp only [↓reduceIte]
      linarith [hbox i]
    · simpa [lower, rectLeftLower, hji] using hbox j
  obtain ⟨C₁, hC₁, hleft⟩ :=
    exists_rectLeftFaceReflection_holder_constant lo hi m s hs hbox i
  obtain ⟨C₂, hC₂, hright⟩ :=
    exists_rectRightFaceReflection_holder_constant lower hi m s hs hlower i
  refine ⟨C₂ * C₁, mul_pos hC₂ hC₁, ?_⟩
  intro u L hL hu
  obtain ⟨v, hvagree, hvball⟩ := hleft u L hL hu
  obtain ⟨w, hwagree, hwball⟩ := hright v (C₁ * L)
    (mul_nonneg hC₁.le hL) hvball
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    have hxin : x ∈ rectBox lower hi := by
      intro j
      have hj := hx j
      by_cases hji : j = i
      · subst j
        have hp : 0 < hi i - lo i := sub_pos.mpr (hbox i)
        have hw : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) := by
          positivity
        dsimp [lower, rectLeftLower]
        simp only [↓reduceIte]
        exact ⟨by linarith [hj.1], hj.2⟩
      · simpa [lower, rectLeftLower, hji] using hj
    exact (hwagree hxin).trans (hvagree hx)
  · simpa only [lower, rectRightCollar, mul_assoc] using hwball

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

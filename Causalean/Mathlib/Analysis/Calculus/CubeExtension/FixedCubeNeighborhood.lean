module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularTwoFaceReflection

/-!
# A controlled rectangular neighborhood of the fixed cube

Finite iteration of the two-face reflection theorem enlarges every face of
the normalized cube with one uniform Hölder radius factor.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [a Hölder
exponent s](hyp:s) with [0 < s](hyp:hs), [there are a
closed coordinate box strictly containing the normalized cube in every
coordinate and a positive constant C such that every response in the intrinsic
Hölder ball of radius L ≥ 0 on the cube agrees on the cube with a response in
the intrinsic Hölder ball of radius C·L on that box](goal). The box and the
constant depend only on d, m and s. -/
theorem exists_fixedCubeNeighborhood_holder_constant
    (d m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ (lo hi : Fin d → ℝ) (C : ℝ),
      (∀ i, lo i < -1 ∧ 1 < hi i) ∧ 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∃ v : (Fin d → ℝ) → ℝ,
          Set.EqOn v u (cube d) ∧
          HolderBallOn (rectBox lo hi) m s (C * L) v := by
  let P : Finset (Fin d) → Prop := fun S =>
    ∃ (lo hi : Fin d → ℝ) (C : ℝ),
      (∀ j, lo j ≤ -1 ∧ 1 ≤ hi j) ∧
      (∀ j ∈ S, lo j < -1 ∧ 1 < hi j) ∧ 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∃ v : (Fin d → ℝ) → ℝ,
          Set.EqOn v u (cube d) ∧
          HolderBallOn (rectBox lo hi) m s (C * L) v
  have hbase : P ∅ := by
    refine ⟨fun _ => -1, fun _ => 1, 1, ?_, ?_, by norm_num, ?_⟩
    · intro j; exact ⟨le_refl _, le_refl _⟩
    · simp
    · intro u L hL hu
      refine ⟨u, (fun _ _ => rfl), ?_⟩
      have hcube : rectBox (fun _ : Fin d => -1) (fun _ => 1) = cube d := by
        rfl
      simpa [hcube] using hu
  have hstep : ∀ (i : Fin d) (S : Finset (Fin d)), i ∉ S → P S → P (insert i S) := by
    intro i S hiS hS
    obtain ⟨lo, hi, C, hweak, hstrict, hC, hball⟩ := hS
    have hbox : ∀ j, lo j < hi j := by
      intro j
      have hj := hweak j
      linarith
    obtain ⟨D, hD, hreflect⟩ :=
      exists_rectTwoFaceReflection_holder_constant lo hi m s hs hbox i
    let lo' := rectLeftLower lo hi m i
    let hi' := rectRightUpper lo' hi m i
    refine ⟨lo', hi', D * C, ?_, ?_, mul_pos hD hC, ?_⟩
    · intro j
      have hj := hweak j
      by_cases hji : j = i
      · subst j
        have hw : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) :=
          div_pos (sub_pos.mpr (hbox i)) (by positivity)
        have hlo : lo' i < hi i := by
          dsimp [lo', rectLeftLower]
          simp only [↓reduceIte]
          linarith [hbox i]
        have hw' : 0 < (hi i - lo' i) / (2 * ((m : ℝ) + 1)) :=
          div_pos (sub_pos.mpr hlo) (by positivity)
        dsimp [lo', rectLeftLower] at hw'
        simp only [↓reduceIte] at hw'
        dsimp [lo', hi', rectLeftLower, rectRightUpper]
        simp only [↓reduceIte]
        constructor <;> linarith
      · simpa [lo', hi', rectLeftLower, rectRightUpper, hji] using hj
    · intro j hjS
      rcases Finset.mem_insert.mp hjS with hji | hjS
      · subst j
        have hw : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) :=
          div_pos (sub_pos.mpr (hbox i)) (by positivity)
        have hlo : lo' i < hi i := by
          dsimp [lo', rectLeftLower]
          simp only [↓reduceIte]
          linarith [hbox i]
        have hw' : 0 < (hi i - lo' i) / (2 * ((m : ℝ) + 1)) :=
          div_pos (sub_pos.mpr hlo) (by positivity)
        dsimp [lo', rectLeftLower] at hw'
        simp only [↓reduceIte] at hw'
        dsimp [lo', hi', rectLeftLower, rectRightUpper]
        simp only [↓reduceIte]
        constructor <;> linarith [hweak i]
      · have hj := hstrict j hjS
        have hji : j ≠ i := by
          intro h
          subst j
          exact hiS hjS
        simpa [lo', hi', rectLeftLower, rectRightUpper, hji] using hj
    · intro u L hL hu
      obtain ⟨v, hvagree, hvball⟩ := hball u L hL hu
      obtain ⟨w, hwagree, hwball⟩ := hreflect v (C * L)
        (mul_nonneg hC.le hL) hvball
      refine ⟨w, ?_, ?_⟩
      · intro x hx
        have hxbox : x ∈ rectBox lo hi := by
          intro j
          have hj := hx j
          exact ⟨(hweak j).1.trans hj.1, hj.2.trans (hweak j).2⟩
        exact (hwagree hxbox).trans (hvagree hx)
      · simpa only [lo', hi', mul_assoc] using hwball
  have hall : P Finset.univ :=
    Finset.induction (motive := P) hbase hstep Finset.univ
  obtain ⟨lo, hi, C, _, hstrict, hC, hball⟩ := hall
  exact ⟨lo, hi, C, (fun i => hstrict i (Finset.mem_univ i)), hC, hball⟩

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

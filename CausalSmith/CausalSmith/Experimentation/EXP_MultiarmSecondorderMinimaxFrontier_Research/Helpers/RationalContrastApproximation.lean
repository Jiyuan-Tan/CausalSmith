import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_contrast_risk_continuity
import Mathlib.Data.Rat.Denumerable

/-! Quantitative rational approximation inside the finite-dimensional zero-sum contrast space. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: exists_ratContrast_close
/-- [there are at least two treatment arms](hyp:hK), [the stated side condition holds](hyp:hε), [the stated side condition holds](hyp:hεc), [the exists rat contrast close](goal). -/
lemma exists_ratContrast_close
    (K : ℕ) (c : Contrast ℝ K) (hK : AdmissibleArmCount K)
    (ε : ℝ) (hε : 0 < ε) (hεc : ε < Lc c / 2) :
    ∃ q : RatContrast K,
      contrastDistance c (ratContrastToReal q) ≤ ε := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let k0 : Arm K := ⟨0, hKpos⟩
  let δ : ℝ := ε / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose r hr using fun a : Arm K => exists_rat_near (c a) hδ
  let f : Arm K → ℚ := fun a =>
    if a = k0 then -∑ b ∈ Finset.univ.erase k0, r b else r a
  have hsum : ∑ a, f a = 0 := by
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ k0)]
    have hrest : ∑ a ∈ Finset.univ.erase k0, f a =
        ∑ a ∈ Finset.univ.erase k0, r a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [f, (Finset.mem_erase.mp ha).1]
    rw [hrest]
    simp [f]
  have hc0 : c k0 = -∑ a ∈ Finset.univ.erase k0, c a := by
    have hs := Finset.sum_erase_add Finset.univ c (Finset.mem_univ k0)
    rw [c.sum_zero] at hs
    linarith
  have hrestBound :
      ∑ a ∈ Finset.univ.erase k0, |c a - (r a : ℝ)| ≤ (K : ℝ) * δ := by
    calc
      _ ≤ ∑ _a ∈ Finset.univ.erase k0, δ := by
        apply Finset.sum_le_sum
        intro a _ha
        exact (hr a).le
      _ ≤ (K : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hδ.le
        simpa using Finset.card_le_card (Finset.erase_subset Finset.univ k0)
  have hk0Bound : |c k0 - (f k0 : ℝ)| ≤ (K : ℝ) * δ := by
    calc
      |c k0 - (f k0 : ℝ)| =
          |∑ a ∈ Finset.univ.erase k0, (c a - (r a : ℝ))| := by
        rw [hc0]
        simp only [f, if_pos, Rat.cast_neg, Rat.cast_sum]
        rw [Finset.sum_sub_distrib]
        rw [show -∑ a ∈ Finset.univ.erase k0, c a -
            -(∑ i ∈ Finset.univ.erase k0, (r i : ℝ)) =
            -(∑ a ∈ Finset.univ.erase k0, c a -
              ∑ i ∈ Finset.univ.erase k0, (r i : ℝ)) by ring, abs_neg]
      _ ≤ ∑ a ∈ Finset.univ.erase k0, |c a - (r a : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ (K : ℝ) * δ := hrestBound
  have hL1 : ∑ a, |c a - (f a : ℝ)| ≤ ε := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun a => |c a - (f a : ℝ)|) (Finset.mem_univ k0)]
    have hrestF : ∑ a ∈ Finset.univ.erase k0, |c a - (f a : ℝ)| =
        ∑ a ∈ Finset.univ.erase k0, |c a - (r a : ℝ)| := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [f, (Finset.mem_erase.mp ha).1]
    rw [hrestF]
    calc
      _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := add_le_add hrestBound hk0Bound
      _ = ε := by dsimp [δ]; field_simp; norm_num
  have hfne : f ≠ 0 := by
    intro hf
    have hLc_le : Lc c ≤ ε := by
      unfold Lc at *
      simpa [hf] using hL1
    linarith
  let q : RatContrast K := ⟨f, hfne, hsum⟩
  refine ⟨q, ?_⟩
  unfold contrastDistance
  change (∑ a, |c a - (f a : ℝ)|) / 2 ≤ ε
  linarith [hL1, hε]

-- @node: coordinate_le_two_contrastDistance
/-- [the coordinate is at most two contrast distance](goal). -/
lemma coordinate_le_two_contrastDistance
    (c c' : Contrast ℝ K) (a : Arm K) :
    |c a - c' a| ≤ 2 * contrastDistance c c' := by
  unfold contrastDistance
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun b _ => abs_nonneg (c b - c' b)) (Finset.mem_univ a)
  rw [show 2 * ((∑ a, |c a - c' a|) / 2) =
      ∑ a, |c a - c' a| by ring]
  exact h

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

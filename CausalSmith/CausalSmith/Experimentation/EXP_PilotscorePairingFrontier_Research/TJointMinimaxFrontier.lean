module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TSelectorUpper
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TArbitraryPairingConverse
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceNormalization
public import Mathlib.Data.Real.Pointwise

/-! # Joint pilot-and-main minimax frontier -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped Pointwise

-- @node: risk_nonnegative
lemma risk_nonnegative {d m N : ℕ} (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (D : Design m N d) : 0 ≤ risk P g D := by
  unfold risk
  apply integral_nonneg
  intro w
  unfold pairLoss
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  · positivity

noncomputable def excessVarianceRisk (d m N : ℕ) (L β cX CX cg Cg : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧
    v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧
      r = (N : ℝ) * realVariance
        (experimentLaw (m := m) (N := N) P
          (fun w => pairedCoinLaw (D (designInput w)))) (pairedEstimator N) -
          efficiencyBound P}}

-- @node: excess_variance_eq_four_minimax
lemma excess_variance_eq_four_minimax (d m N : ℕ) (L β cX CX cg Cg : ℝ)
    (hm : 1 ≤ m) (hN : Even N) (hN2 : 2 ≤ N) :
    excessVarianceRisk d m N L β cX CX cg Cg =
      4 * minimaxRisk d m N L β cX CX cg Cg := by
  let S (D : Design m N d) : Set ℝ :=
    {r | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D}
  let T (D : Design m N d) : Set ℝ :=
    {r | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧
      r = (N : ℝ) * realVariance
        (experimentLaw (m := m) (N := N) P
          (fun w => pairedCoinLaw (D (designInput w)))) (pairedEstimator N) -
          efficiencyBound P}
  have hsets (D : Design m N d) (hD : MatchingDesignClass D) :
      T D = (4 : ℝ) • S D := by
    ext r
    constructor
    · rintro ⟨P, g, hP, rfl⟩
      refine Set.mem_smul_set.mpr ⟨risk P g D, ⟨P, g, hP, rfl⟩, ?_⟩
      have hv := (variance_normalization P g D hP hD hm hN hN2).2
      dsimp only [smul_eq_mul]
      linarith
    · intro hr
      obtain ⟨v, ⟨P, g, hP, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hr
      refine ⟨P, g, hP, ?_⟩
      have hv := (variance_normalization P g D hP hD hm hN hN2).2
      dsimp only [smul_eq_mul]
      linarith
  have houter :
      {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (T D)} =
        (4 : ℝ) • {v : ℝ | ∃ D : Design m N d,
          MatchingDesignClass D ∧ v = sSup (S D)} := by
    ext v
    constructor
    · rintro ⟨D, hD, rfl⟩
      refine Set.mem_smul_set.mpr ⟨sSup (S D), ⟨D, hD, rfl⟩, ?_⟩
      rw [hsets D hD, Real.sSup_smul_of_nonneg (by norm_num)]
    · intro hv
      obtain ⟨u, ⟨D, hD, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hv
      refine ⟨D, hD, ?_⟩
      rw [hsets D hD, Real.sSup_smul_of_nonneg (by norm_num)]
  change sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (T D)} =
    4 * sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (S D)}
  rw [houter, Real.sInf_smul_of_nonneg (by norm_num)]
  rfl

-- @node: thm:joint-minimax-frontier
theorem joint_minimax_frontier (d : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) (hL : 1 / 2 < L) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ m N : ℕ, 1 ≤ m → Even N → 2 ≤ N →
        c * jointFrontier d m N β ≤ minimaxRisk d m N L β cX CX cg Cg ∧
        minimaxRisk d m N L β cX CX cg Cg ≤ C * jointFrontier d m N β ∧
        excessVarianceRisk d m N L β cX CX cg Cg =
          4 * minimaxRisk d m N L β cX CX cg Cg := by
  obtain ⟨c, hc, hlow⟩ := arbitrary_pairing_converse d β L cX CX cg Cg hpars hL
  obtain ⟨C₀, hC₀, hsel⟩ := selector_upper d β L cX CX cg Cg hpars
  refine ⟨c, max C₀ (c + 1), hc, ?_, ?_⟩
  · have h : c + 1 ≤ max C₀ (c + 1) := le_max_right _ _
    linarith
  · intro m N hm hN hN2
    have hphi : 0 ≤ jointFrontier d m N β := by
      unfold jointFrontier
      positivity
    have hLo := (hlow m N hm hN hN2).2
    have hSel := hsel m N hm hN hN2
    let D : Design m N d := selectorDesign (d := d) (m := m) (N := N) β hN hN2
    let S : Set ℝ :=
      {r | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D}
    have hsup : sSup S ≤ C₀ * jointFrontier d m N β := by
      by_cases hne : S.Nonempty
      · apply csSup_le hne
        rintro r ⟨P, g, hP, rfl⟩
        exact hSel.2 P g hP
      · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        rw [he, Real.sSup_empty]
        exact mul_nonneg (le_of_lt hC₀) hphi
    have hbelow : BddBelow
        {v : ℝ | ∃ D' : Design m N d, MatchingDesignClass D' ∧
          v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
            RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D'}} := by
      refine ⟨0, ?_⟩
      rintro v ⟨D', hD', rfl⟩
      let T : Set ℝ :=
        {r | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
          RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D'}
      change 0 ≤ sSup T
      by_cases hba : BddAbove T
      · by_cases hne : T.Nonempty
        · obtain ⟨r, hr⟩ := hne
          obtain ⟨P, g, hP, rfl⟩ := hr
          exact (risk_nonnegative P g D').trans
            (le_csSup hba ⟨P, g, hP, rfl⟩)
        · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
          rw [he, Real.sSup_empty]
      · rw [Real.sSup_of_not_bddAbove hba]
    have hHi : minimaxRisk d m N L β cX CX cg Cg ≤
        C₀ * jointFrontier d m N β := by
      apply le_trans ?_ hsup
      unfold minimaxRisk
      apply csInf_le hbelow
      exact ⟨D, hSel.1, rfl⟩
    refine ⟨hLo, ?_, excess_variance_eq_four_minimax d m N L β cX CX cg Cg hm hN hN2⟩
    exact hHi.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ (c + 1)) hphi)

end CausalSmith.Experimentation.PilotscorePairingFrontier

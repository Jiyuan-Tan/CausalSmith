module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.LocalizedConverse
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TRegularDensityHypercube
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TSelectorUpper

/-! # Converse against arbitrary pilot-dependent matching rules -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

-- @node: frontier_rate_comparison
lemma frontier_rate_comparison {B G H : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) :
    (1 / 2 : ℝ) * min G (B + H) ≤ max B (min G H) := by
  by_cases h : G ≤ B + H
  · rw [min_eq_left h]
    by_cases hHG : H ≤ G
    · rw [min_eq_right hHG]
      have hmaxB : B ≤ max B H := le_max_left _ _
      have hmaxH : H ≤ max B H := le_max_right _ _
      linarith
    · rw [min_eq_left (le_of_not_ge hHG)]
      exact le_trans (by linarith : (1 / 2 : ℝ) * G ≤ G) (le_max_right _ _)
  · rw [min_eq_right (le_of_not_ge h)]
    have hHG : H ≤ G := by linarith
    rw [min_eq_right hHG]
    have hmaxB : B ≤ max B H := le_max_left _ _
    have hmaxH : H ≤ max B H := le_max_right _ _
    linarith

private lemma combine_risk_witnesses {d m N : ℕ} {L β cX CX cg Cg a B G H : ℝ}
    {D : Design m N d}
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hfloor : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧ a * B ≤ risk P g (m := m) (N := N) D)
    (hlocal : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧
        a * min G H ≤ risk P g (m := m) (N := N) D) :
    ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧
        (a / 2) * min G (B + H) ≤ risk P g (m := m) (N := N) D := by
  have hcmp := frontier_rate_comparison hB hG (H := H)
  have hscaled : a * ((1 / 2 : ℝ) * min G (B + H)) ≤
      a * max B (min G H) := mul_le_mul_of_nonneg_left hcmp ha
  by_cases h : B ≤ min G H
  · obtain ⟨P, g, hg, hrisk⟩ := hlocal
    refine ⟨P, g, hg, ?_⟩
    rw [max_eq_right h] at hscaled
    exact (by nlinarith : (a / 2) * min G (B + H) ≤ a * min G H).trans hrisk
  · obtain ⟨P, g, hg, hrisk⟩ := hfloor
    refine ⟨P, g, hg, ?_⟩
    rw [max_eq_left (le_of_not_ge h)] at hscaled
    exact (by nlinarith : (a / 2) * min G (B + H) ≤ a * B).trans hrisk

private lemma oracle_floor_witness (d m N : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg)
    (hnonempty : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg)
    (hN : Even N) (hN2 : 2 ≤ N) (D : Design m N d)
    (hD : MatchingDesignClass D) :
    ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧
        (1 / (3 * Cg ^ 2)) * (N : ℝ) ^ (-2 : ℝ) ≤ risk P g D := by
  obtain ⟨c, C, hc, hC, hcpos, hcC, horacle⟩ :=
    oracle_spacing (d := d) (β := β) (L := L) (cX := cX) (CX := CX)
      (cg := cg) (Cg := Cg) hnonempty hpars
  obtain ⟨P, g, hmodel, hlower⟩ := (horacle N hN hN2).1
  refine ⟨P, g, hmodel, ?_⟩
  rw [← hc]
  exact hlower.trans ((horacle N hN hN2).2.2 m D hD P g hmodel)

private lemma risk_le_holder_envelope (d m N : ℕ) (L β cX CX cg Cg : ℝ)
    (hN : 1 ≤ N) (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (D : Design m N d) (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    risk P g D ≤ (1 / 2 : ℝ) * (L * (d : ℝ) ^ (β / 2)) ^ 2 := by
  let C : ℝ := L * (d : ℝ) ^ (β / 2)
  let R : ℝ := (1 / 2 : ℝ) * C ^ 2
  have hdom := latentTwoWaveLaw_designDomain_ae (m := m) (N := N) P g hmodel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnonneg : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      0 ≤ pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ) := by
    filter_upwards [] with w
    unfold pairLoss
    exact div_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hNpos.le
  have hbound : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ) ≤ R := by
    filter_upwards [hdom] with w hw
    have hC : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg hmodel.parameters.2.2.2.1.le
        (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    have hterm (i : Fin N) :
        (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2 ≤ C ^ 2 := by
      have habs := holder_score_cube_oscillation g hmodel.parameters.2.2.2.1.le
        hmodel.parameters.2.1.le hmodel.holder_score
        (w.1.2 i).1 (w.1.2 ((D (designInput w)).val i)).1
        (hw.2.1 i) (hw.2.1 ((D (designInput w)).val i))
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 habs
    have hsum :
        ∑ i : Fin N,
            (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2 ≤
          (N : ℝ) * C ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin N, C ^ 2 := Finset.sum_le_sum fun i _ => hterm i
        _ = (N : ℝ) * C ^ 2 := by simp
    dsimp [R]
    unfold pairLoss
    apply (div_le_iff₀ hNpos).2
    nlinarith
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
    unfold latentTwoWaveLaw
    infer_instance
  unfold risk
  simpa [R, C] using integral_mono_of_nonneg hnonneg (integrable_const R) hbound

private lemma minimaxRisk_lower_of_design_witnesses (d m N : ℕ)
    (L β cX CX cg Cg a U : ℝ)
    (hdesign : ∃ D : Design m N d, MatchingDesignClass D)
    (hupper : ∀ D : Design m N d, MatchingDesignClass D →
      ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg → risk P g D ≤ U)
    (hlower : ∀ D : Design m N d, MatchingDesignClass D →
      ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg ∧ a ≤ risk P g D) :
    a ≤ minimaxRisk d m N L β cX CX cg Cg := by
  unfold minimaxRisk
  apply le_csInf
  · obtain ⟨D, hD⟩ := hdesign
    exact ⟨sSup {r : ℝ | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D}, D, hD, rfl⟩
  · rintro v ⟨D, hD, rfl⟩
    let S : Set ℝ := {r : ℝ | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D}
    have hSbounded : BddAbove S := by
      refine ⟨U, ?_⟩
      rintro r ⟨P, g, hmodel, rfl⟩
      exact hupper D hD P g hmodel
    obtain ⟨P, g, hmodel, hrisk⟩ := hlower D hD
    exact hrisk.trans (le_csSup hSbounded ⟨P, g, hmodel, rfl⟩)

-- @node: thm:arbitrary-pairing-converse
theorem arbitrary_pairing_converse (d : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) (hL : 1 / 2 < L) :
    ∃ c : ℝ, 0 < c ∧
      ∀ m N : ℕ, 1 ≤ m → Even N → 2 ≤ N →
        (∀ D : Design m N d, MatchingDesignClass D →
          ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
            RegularScoreModel P g L β cX CX cg Cg ∧
            c * jointFrontier d m N β ≤ risk P g D) ∧
        c * jointFrontier d m N β ≤
          minimaxRisk d m N L β cX CX cg Cg := by
  obtain ⟨h0, c0, c1, C1, C2, κ, ε, A, Bconst,
    hh0, hc0, hc1, hC1, hC2, hκ, hε, hA, hBconst, hfam⟩ :=
      (regular_density_hypercube d β L cX CX cg Cg hpars).2 hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hpars.1
  have hdN : 0 < d := Nat.zero_lt_of_lt hpars.1
  have hβ : 0 < β := hpars.2.1
  obtain ⟨cmesh, hcmesh, hmesh⟩ :=
    exists_reciprocal_mesh_for_joint_rate d β h0 C2 hdN hβ hh0 hC2
  let abase : ℝ := c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8
  let alocal : ℝ := abase * cmesh
  let afloor : ℝ := 1 / (3 * Cg ^ 2)
  let a : ℝ := min afloor alocal
  have habase : 0 < abase := by dsimp [abase]; positivity
  have halocal : 0 < alocal := mul_pos habase hcmesh
  have hafloor : 0 < afloor := by
    dsimp [afloor]
    have hCg : 0 < Cg := lt_trans (by norm_num) hpars.2.2.2.2.2.2.2.2.2
    exact div_pos zero_lt_one (mul_pos (by norm_num) (sq_pos_of_pos hCg))
  have ha : 0 < a := lt_min hafloor halocal
  refine ⟨a / 2, div_pos ha (by norm_num), ?_⟩
  intro m N hm hNeven hN2
  have hN1 : 1 ≤ N := by omega
  let G : ℝ := (N : ℝ) ^ (-2 * β / d)
  let H : ℝ := (m : ℝ) ^ (-2 * β / (2 * β + d))
  let B : ℝ := (N : ℝ) ^ (-2 : ℝ)
  have hG : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hB : 0 ≤ B := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hlower (D : Design m N d) (hD : MatchingDesignClass D) :
      ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg ∧
          (a / 2) * min G (B + H) ≤ risk P g D := by
    obtain ⟨q, hq, hqh0, hocc, hpilot, hrate⟩ := hmesh m N hm hN1
    have hfamq := (hfam q hq hqh0).2
    obtain ⟨Plocal, glocal, hmodellocal, hrisklocal⟩ :=
      hypercube_localized_risk_witness hfamq hc0 hc1 hC2
        (by positivity : 0 < (q : ℝ)⁻¹) hm hN1 hocc hpilot D hD
    have hlocal : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg ∧
          a * min G H ≤ risk P g D := by
      refine ⟨Plocal, glocal, hmodellocal, ?_⟩
      have hale : a ≤ alocal := min_le_right _ _
      calc
        a * min G H ≤ alocal * min G H :=
          mul_le_mul_of_nonneg_right hale (by positivity)
        _ = abase * (cmesh * min G H) := by ring
        _ ≤ abase * ((q : ℝ)⁻¹) ^ (2 * β) :=
          mul_le_mul_of_nonneg_left hrate habase.le
        _ ≤ risk Plocal glocal D := by simpa [abase] using hrisklocal
    have hnonempty : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg := by
      obtain ⟨P, g, hg, -⟩ := hlocal
      exact ⟨P, g, hg⟩
    have hfloor0 := oracle_floor_witness d m N β L cX CX cg Cg hpars
      hnonempty hNeven hN2 D hD
    have hfloor : ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg ∧ a * B ≤ risk P g D := by
      obtain ⟨P, g, hg, hr⟩ := hfloor0
      refine ⟨P, g, hg, ?_⟩
      exact (mul_le_mul_of_nonneg_right (min_le_left afloor alocal) hB).trans
        (by simpa [afloor, B] using hr)
    exact combine_risk_witnesses (a := a) (B := B) (G := G) (H := H)
      ha.le hB hG hfloor hlocal
  have hdesign : ∃ D : Design m N d, MatchingDesignClass D :=
    ⟨selectorDesign β hNeven hN2,
      selectorDesign_matchingDesignClass m d N β hNeven hN2⟩
  have hupper : ∀ D : Design m N d, MatchingDesignClass D →
      ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg →
          risk P g D ≤ (1 / 2 : ℝ) * (L * (d : ℝ) ^ (β / 2)) ^ 2 := by
    intro D hD P g hmodel
    exact risk_le_holder_envelope d m N L β cX CX cg Cg hN1 P g D hmodel
  constructor
  · intro D hD
    simpa [jointFrontier, G, H, B] using hlower D hD
  · apply minimaxRisk_lower_of_design_witnesses d m N L β cX CX cg Cg
      (a / 2 * min G (B + H))
      ((1 / 2 : ℝ) * (L * (d : ℝ) ^ (β / 2)) ^ 2)
      hdesign hupper hlower

end CausalSmith.Experimentation.PilotscorePairingFrontier

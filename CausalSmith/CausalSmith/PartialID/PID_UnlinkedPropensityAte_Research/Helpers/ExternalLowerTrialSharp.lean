module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialPair
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawCoverage

/-! Point identification of the Bernoulli trial submodels at a Dirac score. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_armProb {ε : ℝ} (hOverlap : Overlap ε) (a : ArmSpace) :
    armProb a (trialCenterScore hOverlap) = 1 / 2 := by
  cases a <;> simp [armProb, trialCenterScore] <;> ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_armCellMass {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J) :
    armCellMass (Measure.dirac (trialCenterScore hOverlap)) g a r =
      if g (trialCenterScore hOverlap) = r then 1 / 2 else 0 := by
  classical
  unfold armCellMass
  rw [setIntegral_dirac]
  simp [cell, trialCenter_armProb]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_armCellScoreLaw {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass (Measure.dirac (trialCenterScore hOverlap)) g a r) :
    armCellScoreLaw (Measure.dirac (trialCenterScore hOverlap)) inferInstance
      g hg a r hq = Measure.dirac (trialCenterScore hOverlap) := by
  classical
  have hr : g (trialCenterScore hOverlap) = r := by
    by_contra h
    rw [trialCenter_armCellMass, if_neg h] at hq
    exact (lt_irrefl 0) hq
  unfold armCellScoreLaw
  rw [trialCenter_armCellMass, if_pos hr,
    dirac_withDensity, Measure.restrict_smul, restrict_dirac]
  simp [cell, hr, trialCenter_armProb, smul_smul]
  rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_smul]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_armCellWeightLaw {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass (Measure.dirac (trialCenterScore hOverlap)) g a r) :
    armCellWeightLaw (Measure.dirac (trialCenterScore hOverlap)) inferInstance
      g hg a r hq = Measure.dirac (2 : ℝ) := by
  unfold armCellWeightLaw
  rw [trialCenter_armCellScoreLaw g hOverlap hg a r hq]
  rw [Measure.map_dirac' (measurable_inverseArmProb a)]
  simp [trialCenter_armProb]

/-- Given [the stated mathematical inputs and assumptions](hyp:c,u,hu0,hu1), this result [establishes the stated mathematical conclusion](goal). -/
lemma quantile_dirac_interior (c u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    Causalean.Stat.quantile (Measure.dirac c) u = c := by
  apply le_antisymm
  · apply Causalean.Stat.quantile_le_of_le_cdf hu0
    rw [ProbabilityTheory.cdf_eq_real]
    simpa [Measure.real] using hu1.le
  · have hq := Causalean.Stat.le_cdf_quantile (μ := Measure.dirac c) hu1
    rw [ProbabilityTheory.cdf_eq_real] at hq
    by_contra h
    have hlt : Causalean.Stat.quantile (Measure.dirac c) u < c := lt_of_not_ge h
    have hc : c ∉ Iic (Causalean.Stat.quantile (Measure.dirac c) u) := not_le.mpr hlt
    simp [Measure.real, hc] at hq
    exact (not_le_of_gt hu0) hq

/-- Given [the stated mathematical inputs and assumptions](hyp:Y,c), this result [establishes the stated mathematical conclusion](goal). -/
lemma quantileProduct_endpoints_dirac (Y : Measure ℝ) (c : ℝ) :
    (∫ u in (0 : ℝ)..1,
      Causalean.Stat.quantile Y u * Causalean.Stat.quantile (Measure.dirac c) (1 - u)) =
    (∫ u in (0 : ℝ)..1,
      Causalean.Stat.quantile Y u * Causalean.Stat.quantile (Measure.dirac c) u) := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro u hu
  dsimp
  rw [quantile_dirac_interior c (1 - u) (by linarith [hu.2]) (by linarith [hu.1]),
    quantile_dirac_interior c u hu.1 hu.2]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,Prel,hMass,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_muLower_eq_muUpper {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses (Measure.dirac (trialCenterScore hOverlap)) g Prel)
    (a : ArmSpace) :
    muLower (Measure.dirac (trialCenterScore hOverlap)) g Prel hMass a =
      muUpper (Measure.dirac (trialCenterScore hOverlap)) g Prel hMass a := by
  unfold muLower muUpper
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with hq
  · rw [trialCenter_armCellWeightLaw g hOverlap hMass.2.2.1 a r hq]
    rw [quantileProduct_endpoints_dirac]
  · rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,Prel,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_sharpATELength_eq_zero {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses (Measure.dirac (trialCenterScore hOverlap)) g Prel) :
    sharpATELength (Measure.dirac (trialCenterScore hOverlap)) g Prel hMass = 0 := by
  unfold sharpATELength
  rw [trialCenter_muLower_eq_muUpper g hOverlap Prel hMass true,
    trialCenter_muLower_eq_muUpper g hOverlap Prel hMass false]
  ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte

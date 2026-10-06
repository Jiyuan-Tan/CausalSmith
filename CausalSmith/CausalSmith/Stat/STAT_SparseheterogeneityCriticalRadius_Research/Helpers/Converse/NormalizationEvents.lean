module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.GammaCalibration

/-! Deterministic good event for the normalized shared-design target. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set

noncomputable def selectedRawMassTotal (n : ℕ) (rho : ℝ)
    (theta : Fin (n - 1) → LatentCell) : ℝ :=
  rawMassTotal n (dualDegree n rho) converseKappa theta

noncomputable def selectedAlignedScoreTotal (n : ℕ) (rho : ℝ) (h : Bool)
    (theta : Fin (n - 1) → LatentCell) : ℝ :=
  (if h then 1 else -1) *
    rawSignedScoreTotal n (dualDegree n rho) converseKappa theta

noncomputable def selectedLatentPrior (n : ℕ) (rho : ℝ) (h : Bool) :
    Measure (Fin (n - 1) → LatentCell) :=
  latentProductPrior n (dualInterval n rho) (dualDegree n rho)
    (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h)

def normalizationGood (n : ℕ) (rho : ℝ) (h : Bool)
    (theta : Fin (n - 1) → LatentCell) : Prop :=
  |selectedRawMassTotal n rho theta - selectedExpectedRawMass n rho| ≤
      selectedExpectedRawMass n rho / 8 ∧
  |selectedGamma n rho * selectedAlignedScoreTotal n rho h theta -
      selectedGamma n rho * selectedExpectedAlignedScore n rho| ≤
    converseC2 * selectedExpectedRawMass n rho / (4 * Hrho n rho)

lemma normalizationGood_rawMass_pos {n : ℕ} {rho : ℝ} {h : Bool}
    {theta : Fin (n - 1) → LatentCell} (hn : 3 ≤ n)
    (hgood : normalizationGood n rho h theta) :
    0 < selectedRawMassTotal n rho theta := by
  have hmass := (selectedExpectedRawMass_mem_Icc n rho hn).1
  have hdev := (abs_le.mp hgood.1).1
  nlinarith

lemma normalizationGood_ratio_close {n : ℕ} {rho : ℝ} {h : Bool}
    {theta : Fin (n - 1) → LatentCell} (hn : 3 ≤ n)
    (hgood : normalizationGood n rho h theta) :
    |selectedGamma n rho * selectedAlignedScoreTotal n rho h theta /
        selectedRawMassTotal n rho theta - 4 * converseC2 / Hrho n rho| ≤
      converseC2 / Hrho n rho := by
  have hmass := selectedExpectedRawMass_mem_Icc n rho hn
  have hSpos := normalizationGood_rawMass_pos hn hgood
  have hESpos : 0 < selectedExpectedRawMass n rho :=
    lt_of_lt_of_le zero_lt_one hmass.1
  have hEVpos := selectedExpectedAlignedScore_pos n rho hn
  have hHpos : 0 < Hrho n rho :=
    lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  have hcpos : 0 < converseC2 := by
    unfold converseC2
    norm_num
  have hSlower :
      7 * selectedExpectedRawMass n rho / 8 ≤
        selectedRawMassTotal n rho theta := by
    have hdev := (abs_le.mp hgood.1).1
    nlinarith
  have hratio :
      selectedExpectedRawMass n rho / selectedRawMassTotal n rho theta ≤
        (8 : ℝ) / 7 := by
    rw [div_le_iff₀ hSpos]
    nlinarith
  have hscore :
      |selectedGamma n rho *
          (selectedAlignedScoreTotal n rho h theta -
            selectedExpectedAlignedScore n rho)| ≤
        converseC2 * selectedExpectedRawMass n rho / (4 * Hrho n rho) := by
    rw [mul_sub]
    exact hgood.2
  have hraw :
      |selectedExpectedRawMass n rho - selectedRawMassTotal n rho theta| ≤
        selectedExpectedRawMass n rho / 8 := by
    simpa [abs_sub_comm] using hgood.1
  have hid := ratio_sub_calibrated_center
    (S := selectedRawMassTotal n rho theta)
    (V := selectedAlignedScoreTotal n rho h theta)
    (ES := selectedExpectedRawMass n rho)
    (EV := selectedExpectedAlignedScore n rho)
    (gamma := selectedGamma n rho) (c := converseC2) (H := Hrho n rho)
    hSpos.ne' hESpos.ne' hEVpos.ne' hHpos.ne' (by rfl)
  rw [hid]
  calc
    |selectedGamma n rho *
          (selectedAlignedScoreTotal n rho h theta -
            selectedExpectedAlignedScore n rho) /
          selectedRawMassTotal n rho theta +
        4 * converseC2 / Hrho n rho *
          ((selectedExpectedRawMass n rho -
              selectedRawMassTotal n rho theta) /
            selectedRawMassTotal n rho theta)|
        ≤ |selectedGamma n rho *
              (selectedAlignedScoreTotal n rho h theta -
                selectedExpectedAlignedScore n rho) /
              selectedRawMassTotal n rho theta| +
            |4 * converseC2 / Hrho n rho *
              ((selectedExpectedRawMass n rho -
                  selectedRawMassTotal n rho theta) /
                selectedRawMassTotal n rho theta)| := abs_add_le _ _
    _ = |selectedGamma n rho *
              (selectedAlignedScoreTotal n rho h theta -
                selectedExpectedAlignedScore n rho)| /
            selectedRawMassTotal n rho theta +
          (4 * converseC2 / Hrho n rho) *
            (|selectedExpectedRawMass n rho -
                selectedRawMassTotal n rho theta| /
              selectedRawMassTotal n rho theta) := by
          rw [abs_div, abs_of_pos hSpos]
          congr 1
          rw [abs_mul, abs_div,
            abs_of_pos (mul_pos (by norm_num) hcpos), abs_of_pos hHpos, abs_div,
            abs_of_pos hSpos]
    _ ≤ (converseC2 * selectedExpectedRawMass n rho /
            (4 * Hrho n rho)) / selectedRawMassTotal n rho theta +
          (4 * converseC2 / Hrho n rho) *
            ((selectedExpectedRawMass n rho / 8) /
              selectedRawMassTotal n rho theta) := by
          gcongr
    _ = (converseC2 / Hrho n rho) *
          (selectedExpectedRawMass n rho /
            selectedRawMassTotal n rho theta) * (3 / 4 : ℝ) := by
          field_simp
          ring
    _ ≤ (converseC2 / Hrho n rho) * ((8 : ℝ) / 7) * (3 / 4 : ℝ) := by
          gcongr
    _ ≤ converseC2 / Hrho n rho := by
          have : 0 ≤ converseC2 / Hrho n rho :=
            (div_pos hcpos hHpos).le
          nlinarith

lemma normalizationGood_ratio_lower {n : ℕ} {rho : ℝ} {h : Bool}
    {theta : Fin (n - 1) → LatentCell} (hn : 3 ≤ n)
    (hgood : normalizationGood n rho h theta) :
    3 * converseC2 / Hrho n rho ≤
      selectedGamma n rho * selectedAlignedScoreTotal n rho h theta /
        selectedRawMassTotal n rho theta := by
  have hclose := normalizationGood_ratio_close hn hgood
  have hlower := (abs_le.mp hclose).1
  calc
    3 * converseC2 / Hrho n rho =
        4 * converseC2 / Hrho n rho - converseC2 / Hrho n rho := by ring
    _ ≤ selectedGamma n rho * selectedAlignedScoreTotal n rho h theta /
          selectedRawMassTotal n rho theta := by linarith

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

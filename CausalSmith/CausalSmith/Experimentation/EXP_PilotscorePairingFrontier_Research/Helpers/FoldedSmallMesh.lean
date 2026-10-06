module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedModelConstruction

/-! # Uniform small-mesh power thresholds -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma exists_rpow_le_threshold {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h -> h ≤ h0 -> h ^ p ≤ c := by
  refine ⟨c ^ (1 / p), Real.rpow_pos_of_pos hc _, ?_⟩
  intro h hh hle
  calc
    h ^ p ≤ (c ^ (1 / p)) ^ p := Real.rpow_le_rpow hh.le hle hp.le
    _ = c := by
      rw [← Real.rpow_mul hc.le]
      convert Real.rpow_one c using 2
      field_simp

/-- A common positive threshold controls every power appearing in the folded
parameter, density-error, and small-amplitude conditions. -/
lemma exists_folded_power_threshold {beta kappa eps delta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hkappa : 0 < kappa) (heps0 : 0 ≤ eps)
    (hdelta : 24 * eps < delta) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h -> h ≤ h0 ->
      h ≤ 1 / 24 ∧
      h ^ (1 - beta) ≤ kappa / 4 ∧
      h ^ (1 - beta) ≤ (delta - 24 * eps) * kappa / 4 ∧
      h ^ beta ≤ 1 / (12 * kappa * (1 + eps)) := by
  have hp : 0 < 1 - beta := by linarith
  have hcscale : 0 < kappa / 4 := by positivity
  have hcerror : 0 < (delta - 24 * eps) * kappa / 4 := by positivity
  have hceps : 0 < 1 / (12 * kappa * (1 + eps)) := by positivity
  obtain ⟨hs, hs0, hsmallS⟩ := exists_rpow_le_threshold hp hcscale
  obtain ⟨he, he0, hsmallE⟩ := exists_rpow_le_threshold hp hcerror
  obtain ⟨ha, ha0, hsmallA⟩ := exists_rpow_le_threshold hbeta0 hceps
  let h0 := min (1 / 24) (min hs (min he ha))
  have h0pos : 0 < h0 := by
    dsimp [h0]
    exact lt_min (by norm_num) (lt_min hs0 (lt_min he0 ha0))
  refine ⟨h0, h0pos, ?_⟩
  intro h hh hh0
  have h24 : h ≤ 1 / 24 := hh0.trans (min_le_left _ _)
  have hsle : h ≤ hs := hh0.trans <|
    (min_le_right _ _).trans (min_le_left _ _)
  have hele : h ≤ he := hh0.trans <|
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hale : h ≤ ha := hh0.trans <|
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨h24, hsmallS h hh hsle, hsmallE h hh hele, hsmallA h hh hale⟩

lemma folded_analytic_bounds_of_power_bounds
    {h beta kappa eps delta : ℝ}
    (hh : 0 < h) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hkappa : 0 < kappa) (heps0 : 0 ≤ eps)
    (hscalePow : h ^ (1 - beta) ≤ kappa / 4)
    (herrorPow : h ^ (1 - beta) ≤ (delta - 24 * eps) * kappa / 4)
    (hampPow : h ^ beta ≤ 1 / (12 * kappa * (1 + eps))) :
    4 ≤ kappa * h ^ beta / h ∧
    kappa * h ^ beta * (1 + eps) ≤ 1 / 12 ∧
    4 * h / (kappa * h ^ beta) + 24 * eps ≤ delta := by
  have hp : 0 < h ^ (1 - beta) := Real.rpow_pos_of_pos hh _
  have hb : 0 < h ^ beta := Real.rpow_pos_of_pos hh _
  have he1 : 0 < 1 + eps := by linarith
  have hid : h ^ beta / h = 1 / h ^ (1 - beta) := by
    calc
      h ^ beta / h = h ^ beta / h ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = h ^ (beta - 1) := (Real.rpow_sub hh beta 1).symm
      _ = h ^ (-(1 - beta)) := by congr 1 <;> ring
      _ = (h ^ (1 - beta))⁻¹ := Real.rpow_neg hh.le _
      _ = 1 / h ^ (1 - beta) := by rw [one_div]
  have hid' : h / h ^ beta = h ^ (1 - beta) := by
    calc
      h / h ^ beta = h ^ (1 : ℝ) / h ^ beta := by rw [Real.rpow_one]
      _ = h ^ (1 - beta) := (Real.rpow_sub hh 1 beta).symm
  constructor
  · calc
      4 ≤ kappa / h ^ (1 - beta) := (le_div_iff₀ hp).2 (by nlinarith)
      _ = kappa * (h ^ beta / h) := by rw [hid]; ring
      _ = kappa * h ^ beta / h := by ring
  constructor
  · calc
      kappa * h ^ beta * (1 + eps) ≤
          kappa * (1 / (12 * kappa * (1 + eps))) * (1 + eps) := by
        gcongr
      _ = 1 / 12 := by field_simp
  · calc
      4 * h / (kappa * h ^ beta) + 24 * eps =
          (4 / kappa) * (h / h ^ beta) + 24 * eps := by field_simp
      _ = (4 / kappa) * h ^ (1 - beta) + 24 * eps := by rw [hid']
      _ ≤ (4 / kappa) * ((delta - 24 * eps) * kappa / 4) +
          24 * eps := by
        gcongr
      _ = delta := by field_simp; ring

end CausalSmith.Experimentation.PilotscorePairingFrontier

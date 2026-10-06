module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestCalibrationConstants
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Bandwidth comparisons for the honest calibration

These are the bias and inverse-retention comparisons in equation (8) of the
honest-interval proof. They retain the bandwidth cap and all three regimes.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The bandwidth exponent is positive. -/
-- @node: bandwidthExponent_pos
lemma bandwidthExponent_pos (c : ClassConstants) : 0 < bandwidthExponent c := by
  unfold bandwidthExponent
  split_ifs <;> apply inv_pos.mpr <;> linarith [c.beta_pos, c.kappa_pos]

/-- The capped bandwidth is the minimum of the cap and the power bandwidth. -/
-- @node: bandwidth_eq_min_power
lemma bandwidth_eq_min_power (c : ClassConstants) (n : ℕ) :
    bandwidth c n = min (c.x0 / 2) ((n : ℝ) ^ (-bandwidthExponent c)) := by
  unfold bandwidth bandwidthExponent
  split_ifs <;> simp only [one_div]

/-- Positive sample sizes give a positive admissible bandwidth. -/
-- @node: bandwidth_pos_and_le_cap
lemma bandwidth_pos_and_le_cap (c : ClassConstants) {n : ℕ} (hn : 0 < n) :
    0 < bandwidth c n ∧ bandwidth c n ≤ c.x0 / 2 := by
  rw [bandwidth_eq_min_power]
  exact ⟨lt_min (by linarith [c.x0_pos])
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _), min_le_left _ _⟩

/-- The supercritical risk exponent lies strictly between zero and one. -/
-- @node: riskExponent_pos_lt_one
lemma riskExponent_pos_lt_one (c : ClassConstants) (hk : 1 < c.kappa) :
    0 < riskExponent c ∧ riskExponent c < 1 := by
  unfold riskExponent
  have hd : 0 < 2 * c.beta + c.kappa + 1 := by linarith [c.beta_pos]
  constructor
  · exact div_pos (by linarith [c.beta_pos]) hd
  · exact (div_lt_one hd).2 (by linarith)

/-- The exponent in the extinction tail is positive in both bandwidth regimes. -/
-- @node: extinctionPower_pos
lemma extinctionPower_pos (c : ClassConstants) :
    0 < 1 - bandwidthExponent c * c.kappa := by
  unfold bandwidthExponent
  split_ifs with hk
  · have hd : 0 < 2 * c.beta + 2 := by linarith [c.beta_pos]
    have h : c.kappa / (2 * c.beta + 2) < 1 :=
      (div_lt_one hd).2 (by linarith [c.beta_pos])
    rw [mul_comm, ← div_eq_mul_inv]
    linarith
  · have hd : 0 < 2 * c.beta + c.kappa + 1 := by
      linarith [c.beta_pos, c.kappa_pos]
    have h : c.kappa / (2 * c.beta + c.kappa + 1) < 1 :=
      (div_lt_one hd).2 (by linarith [c.beta_pos])
    rw [mul_comm, ← div_eq_mul_inv]
    linarith

/-- At sample sizes at least three, the logarithm exceeds one. -/
-- @node: one_le_log_sampleSize
lemma one_le_log_sampleSize {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3
  linarith [Real.log_three_gt_d9]

/-- The capped bias power is bounded by the declared squared-risk rate. -/
-- @node: bandwidth_biasPower_le_riskScale
lemma bandwidth_biasPower_le_riskScale (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n) :
    (bandwidth c n) ^ (2 * c.beta + 2) ≤ riskScale c n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb := (bandwidth_pos_and_le_cap c (show 0 < n by omega)).1
  have hband : bandwidth c n ≤ (n : ℝ) ^ (-bandwidthExponent c) := by
    rw [bandwidth_eq_min_power]
    exact min_le_right _ _
  have hmono := Real.rpow_le_rpow hb.le hband
    (show 0 ≤ 2 * c.beta + 2 by linarith [c.beta_pos])
  rw [← Real.rpow_mul hn0.le] at hmono
  unfold bandwidthExponent at hmono
  unfold riskScale
  split_ifs with hlt heq
  · rw [if_pos hlt.le] at hmono
    have hd : 2 * c.beta + 2 ≠ 0 := ne_of_gt (by linarith [c.beta_pos])
    simpa only [neg_mul, inv_mul_cancel₀ hd, Real.rpow_neg_one] using hmono
  · rw [if_pos (by linarith : c.kappa ≤ 1)] at hmono
    have hd : 2 * c.beta + 2 ≠ 0 := ne_of_gt (by linarith [c.beta_pos])
    have hpow : (bandwidth c n) ^ (2 * c.beta + 2) ≤ (n : ℝ)⁻¹ := by
      simpa only [neg_mul, inv_mul_cancel₀ hd, Real.rpow_neg_one] using hmono
    exact hpow.trans ((le_div_iff₀ hn0).2 (by
      rw [inv_mul_cancel₀ hn0.ne']
      exact one_le_log_sampleSize hn))
  · have hk : ¬c.kappa ≤ 1 := by intro hle; exact heq (le_antisymm hle (le_of_not_gt hlt))
    rw [if_neg hk] at hmono
    convert hmono using 1 <;> congr 1 <;> simp only [div_eq_mul_inv] <;> ring

/-- Off the cap, the supercritical inverse-retention term equals the rate. -/
-- @node: supercritical_power_variance_eq_rate
lemma supercritical_power_variance_eq_rate (c : ClassConstants) {n : ℕ}
    (hn : 0 < n) (hk : 1 < c.kappa) :
    (n : ℝ)⁻¹ * ((n : ℝ) ^ (-bandwidthExponent c)) ^ (1 - c.kappa) =
      riskScale c n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_mul hn0.le, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
  simp only [riskScale, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk),
    bandwidthExponent, if_neg (not_le.mpr hk)]
  congr 1
  have hd : 2 * c.beta + c.kappa + 1 ≠ 0 := ne_of_gt (by
    linarith [c.beta_pos])
  field_simp
  <;> ring

/-- In the subcritical regime the inverse-retention comparison is an equality. -/
-- @node: subcritical_varianceRate_eq
lemma subcritical_varianceRate_eq (c : ClassConstants) (hk : c.kappa < 1) (n : ℕ) :
    (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) =
      varianceRateEnvelope c * riskScale c n := by
  simp only [varianceFactor, varianceRateEnvelope, riskScale, if_pos hk, mul_one, one_mul]

/-- The critical logarithmic variance term obeys the declared envelope,
including when the bandwidth cap is active. -/
-- @node: critical_varianceFactor_le_log_envelope
lemma critical_varianceFactor_le_log_envelope (c : ClassConstants) {n : ℕ}
    (hn : 3 ≤ n) (hk : c.kappa = 1) :
    varianceFactor c (bandwidth c n) ≤ varianceRateEnvelope c * Real.log n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hh : 0 < c.x0 / 2 := by linarith [c.x0_pos]
  have hh1 : c.x0 / 2 ≤ 1 := by linarith [c.x0_le]
  have hlcap : 0 ≤ Real.log (1 / (c.x0 / 2)) :=
    Real.log_nonneg ((one_le_div₀ hh).2 hh1)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hln : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have ha := bandwidthExponent_pos c
  have hterm : 1 + Real.log (1 / (c.x0 / 2)) ≤
      ((1 + Real.log (1 / (c.x0 / 2))) / Real.log 3) * Real.log n := by
    have hm := mul_le_mul_of_nonneg_left hln
      (div_nonneg (by linarith : 0 ≤ 1 + Real.log (1 / (c.x0 / 2))) hl3.le)
    simpa only [div_mul_cancel₀ _ hl3.ne'] using hm
  simp only [varianceFactor, varianceRateEnvelope,
    if_neg (by linarith : ¬c.kappa < 1), if_pos hk]
  rw [bandwidth_eq_min_power]
  rcases le_total (c.x0 / 2) ((n : ℝ) ^ (-bandwidthExponent c)) with hcap | hpower
  · rw [min_eq_left hcap]
    have hapos : 0 ≤ bandwidthExponent c * Real.log n :=
      mul_nonneg ha.le (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_log_sampleSize hn))
    nlinarith
  · rw [min_eq_right hpower, one_div, Real.log_inv,
      Real.log_rpow hn0]
    nlinarith

/-- The critical inverse-retention comparison follows after dividing by the
sample size. -/
-- @node: critical_varianceRate_le
lemma critical_varianceRate_le (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n)
    (hk : c.kappa = 1) :
    (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * riskScale c n := by
  have h := mul_le_mul_of_nonneg_left
    (critical_varianceFactor_le_log_envelope c hn hk)
    (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  simp only [riskScale, if_neg (by linarith : ¬c.kappa < 1), if_pos hk]
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The supercritical variance envelope covers both the capped and power
bandwidths. -/
-- @node: supercritical_varianceRate_le
lemma supercritical_varianceRate_le (c : ClassConstants) {n : ℕ}
    (hn : 3 ≤ n) (hk : 1 < c.kappa) :
    (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * riskScale c n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs := riskExponent_pos_lt_one c hk
  have hr : 0 ≤ riskScale c n := by
    simp only [riskScale, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk)]
    positivity
  have hrate : (n : ℝ)⁻¹ =
      (n : ℝ) ^ (riskExponent c - 1) * riskScale c n := by
    simp only [riskScale, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk)]
    change (n : ℝ)⁻¹ = (n : ℝ) ^ (riskExponent c - 1) *
      (n : ℝ) ^ (-riskExponent c)
    rw [← Real.rpow_add hn0]
    convert (Real.rpow_neg_one (n : ℝ)).symm using 1 <;> congr 1 <;> ring
  have hpow : (n : ℝ) ^ (riskExponent c - 1) ≤ (3 : ℝ) ^ (riskExponent c - 1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by linarith)
  have hcap0 : 0 ≤ (c.x0 / 2) ^ (1 - c.kappa) := Real.rpow_nonneg (by linarith [c.x0_pos]) _
  simp only [varianceFactor, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk)]
  rw [bandwidth_eq_min_power]
  rcases le_total (c.x0 / 2) ((n : ℝ) ^ (-bandwidthExponent c)) with hcap | hpower
  · rw [min_eq_left hcap, hrate]
    calc
      _ = ((c.x0 / 2) ^ (1 - c.kappa) * (n : ℝ) ^ (riskExponent c - 1)) *
          riskScale c n := by ring
      _ ≤ ((c.x0 / 2) ^ (1 - c.kappa) * (3 : ℝ) ^ (riskExponent c - 1)) *
          riskScale c n := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hcap0) hr
      _ ≤ varianceRateEnvelope c * riskScale c n := by
        apply mul_le_mul_of_nonneg_right _ hr
        simp only [varianceRateEnvelope, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk)]
        exact le_max_right _ _
  · rw [min_eq_right hpower, supercritical_power_variance_eq_rate c (by omega) hk]
    have he : 1 ≤ varianceRateEnvelope c := by
      simp only [varianceRateEnvelope, if_neg (not_lt.mpr hk.le), if_neg (ne_of_gt hk)]
      exact le_max_left _ _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he hr

/-- Equation (8)'s variance comparison holds uniformly over all three
endpoint regimes and every allowed sample size. -/
-- @node: bandwidth_varianceRate_le_riskScale
lemma bandwidth_varianceRate_le_riskScale (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * riskScale c n := by
  rcases lt_trichotomy c.kappa 1 with hk | hk | hk
  · exact (subcritical_varianceRate_eq c hk n).le
  · exact critical_varianceRate_le c hn hk
  · exact supercritical_varianceRate_le c hn hk

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

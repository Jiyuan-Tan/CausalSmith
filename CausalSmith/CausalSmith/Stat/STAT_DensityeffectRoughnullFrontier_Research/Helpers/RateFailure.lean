module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RatePilot

/-! Polynomial control of the frozen pilot failure allowance, using the tenth
term of the exponential series as in equation (57). -/

public section
noncomputable section
open Filter
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The pilot ranks are bounded by their unlogged polynomial scales. -/
-- @node: tuned_pilot_polynomial_bounds
lemma tuned_pilot_polynomial_bounds (m : ℕ) (hm : 3 ≤ m) :
    (tunedMx m : ℝ) ≤ (m : ℝ) ^ (10 / 13 : ℝ) ∧
    (tunedMy m : ℝ) ≤ (m : ℝ) ^ (1 / 13 : ℝ) := by
  have hp := pilot_input_mem_Icc m (by omega) (one_le_log_of_three_le m hm)
  constructor
  · exact (dyadicFloor_le _ (pilot_power_bounds m (by omega)
      (one_le_log_of_three_le m hm) (10 / 13) (by norm_num)).1).trans
      (Real.rpow_le_rpow (by positivity) hp.2 (by norm_num))
  · exact (dyadicFloor_le _ (pilot_power_bounds m (by omega)
      (one_le_log_of_three_le m hm) (1 / 13) (by norm_num)).1).trans
      (Real.rpow_le_rpow (by positivity) hp.2 (by norm_num))

/-- A positive exponential is bounded below by its tenth power-series term. -/
-- @node: exp_neg_le_tenth_inverse
lemma exp_neg_le_tenth_inverse (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) ≤ (Nat.factorial 10 : ℝ) / x ^ 10 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 10
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) (by positivity : 0 < x ^ 10)).2
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 10)).1 h
  nlinarith

/-- The treatment-count failure term has the strict smaller exponent in (57). -/
-- @node: tuned_propensity_failure_role_bound
lemma tuned_propensity_failure_role_bound (m : ℕ) (hm : 3 ≤ m) :
    2 * (tunedMx m : ℝ) * Real.exp (-(m : ℝ) / (32 * tunedMx m)) ≤
      (2 * (Nat.factorial 10 : ℝ) * 32 ^ 10) * (m : ℝ) ^ (-20 / 13 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmxpos : (0 : ℝ) < tunedMx m := by
    simp only [tunedMx, dyadicFloor, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hb := (tuned_pilot_polynomial_bounds m hm).1
  have hscale : (m : ℝ) ^ (3 / 13 : ℝ) / 32 ≤ (m : ℝ) / (32 * tunedMx m) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * (tunedMx m : ℝ))).2
    have h := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ (m : ℝ) ^ (3 / 13 : ℝ) by positivity)
    rw [← Real.rpow_add hmpos] at h
    norm_num at h
    nlinarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hscale)
  have ht := exp_neg_le_tenth_inverse ((m : ℝ) ^ (3 / 13 : ℝ) / 32) (by positivity)
  have he' : Real.exp (-(m : ℝ) / (32 * tunedMx m)) ≤
      (Nat.factorial 10 : ℝ) * 32 ^ 10 * (m : ℝ) ^ (-30 / 13 : ℝ) := by
    have hh := he.trans ht
    have hid : (Nat.factorial 10 : ℝ) / ((m : ℝ) ^ (3 / 13 : ℝ) / 32) ^ 10 =
        (Nat.factorial 10 : ℝ) * 32 ^ 10 * (m : ℝ) ^ (-30 / 13 : ℝ) := by
      rw [div_pow, div_div_eq_mul_div, ← Real.rpow_mul_natCast hmpos.le,
        div_eq_mul_inv, ← Real.rpow_neg hmpos.le]
      norm_num
    simpa only [neg_div, hid] using hh
  calc
    _ ≤ 2 * ((m : ℝ) ^ (10 / 13 : ℝ)) *
        ((Nat.factorial 10 : ℝ) * 32 ^ 10 * (m : ℝ) ^ (-30 / 13 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)) he'
        (Real.exp_nonneg _) (by positivity)
    _ = (2 * (Nat.factorial 10 : ℝ) * 32 ^ 10) *
        ((m : ℝ) ^ (10 / 13 : ℝ) * (m : ℝ) ^ (-30 / 13 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hmpos]; norm_num

/-- The complete pilot failure allowance has a strict polynomial margin over the frontier. -/
-- @node: tuned_zeta_role_rate_bound
lemma tuned_zeta_role_rate_bound (m : ℕ) (hm : 3 ≤ m) :
    zetaAllow m (tunedMx m) (tunedMy m) ≤
      (2 * (Nat.factorial 10 : ℝ) * 32 ^ 10 + 6) * (m : ℝ) ^ (-20 / 13 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hx : (tunedMx m : ℝ) ≤ m := by exact_mod_cast (tuned_rank_compatibility m hm).1
  have hy : (tunedMy m : ℝ) ≤ m := by
    exact (tuned_pilot_polynomial_bounds m hm).2.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hmone (by norm_num : (1 / 13 : ℝ) ≤ 1))
  have hxy := mul_le_mul hx hy (by positivity) (by positivity)
  have hx2 : (tunedMx m : ℝ) ≤ (m : ℝ) ^ 2 := hx.trans (by nlinarith)
  have hcoeff : 4 * (tunedMx m : ℝ) * tunedMy m + 2 * tunedMx m ≤ 6 * (m : ℝ) ^ 2 := by
    nlinarith
  have hterm := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (m : ℝ) ^ (-30 : ℤ) by positivity)
  have hid : 6 * (m : ℝ) ^ 2 * (m : ℝ) ^ (-30 : ℤ) =
      6 * (m : ℝ) ^ (-28 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, mul_assoc, ← Real.rpow_add hmpos]
    norm_num
  rw [hid] at hterm
  have hpower := Real.rpow_le_rpow_of_exponent_le hmone
    (by norm_num : (-28 : ℝ) ≤ -20 / 13)
  have htail := hterm.trans (mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 6))
  have hfirst := tuned_propensity_failure_role_bound m hm
  rw [zetaAllow, if_neg (by omega : ¬m < 3)]
  nlinarith

/-- Pilot failure also has the observation-size frontier rate. -/
-- @node: tuned_zeta_frontier_rate_bound
lemma tuned_zeta_frontier_rate_bound (n : ℕ) (hn : 3 ≤ roleSize n) :
    zetaAllow (roleSize n) (tunedMx (roleSize n)) (tunedMy (roleSize n)) ≤
      ((2 * (Nat.factorial 10 : ℝ) * 32 ^ 10 + 6) * (26 : ℝ) ^ (16 / 29 : ℝ)) *
        frontierRate n := by
  have hp := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ roleSize n by exact_mod_cast (by omega : 1 ≤ roleSize n))
    (by norm_num : (-20 / 13 : ℝ) ≤ -16 / 29)
  have hs := roleSize_rpow_le_sampleSize_rpow n (by omega) (-16 / 29) (by norm_num)
  have hs' : (roleSize n : ℝ) ^ (-16 / 29 : ℝ) ≤
      (26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n := by
    simpa only [neg_div, neg_neg, frontierRate] using hs
  exact (tuned_zeta_role_rate_bound _ hn).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp.trans hs')
      (show 0 ≤ 2 * (Nat.factorial 10 : ℝ) * 32 ^ 10 + 6 by positivity))

/-- The public pilot guards are eventually satisfied, without testing pilot errors. -/
-- @node: reportingBranch_eventually
lemma reportingBranch_eventually : ∀ᶠ n : ℕ in atTop, reportingBranch n := by
  have ht (C a : ℝ) (ha : 0 < a) :
      Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-a)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop |>.const_mul C
  have hh := (ht ((2 : ℝ) ^ 16 * ((2 : ℝ) ^ (1 / 10 : ℝ) + 4)) (11 / 145)
    (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hz := (ht (2 * (Nat.factorial 10 : ℝ) * 32 ^ 10 + 6) (20 / 13)
    (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have hm : ∀ᶠ m : ℕ in atTop,
      3 ≤ m ∧ hAllow (2 ^ 16) m (tunedMx m) (tunedMy m) ≤ 1 ∧
        zetaAllow m (tunedMx m) (tunedMy m) ≤ 1 / 100 := by
    filter_upwards [eventually_ge_atTop 3, tuned_hAllow_eventually_le_bias_power, hh, hz]
      with m hm hbound hsmall hzsmall
    exact ⟨hm, hbound.trans (by simpa only [neg_div] using hsmall.le),
      (tuned_zeta_role_rate_bound m hm).trans (by simpa only [neg_div] using hzsmall.le)⟩
  exact roleSize_tendsto_atTop.eventually hm

end CausalSmith.Stat.DensityEffectRoughNull

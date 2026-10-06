module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateBias
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateTrace
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Pilot allowance rates and the positive exponent margins used in (51)--(52).
Downward rounding changes constants only; logarithmic powers are absorbed by
strict polynomial margins, without changing the frozen tuning.
-/

public section
noncomputable section
open Filter
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Inverse powers of a downward rounded rank lose at most the corresponding power of two. -/
-- @node: dyadicFloor_rpow_neg_le
lemma dyadicFloor_rpow_neg_le (z a : ℝ) (hz : 0 < z) (ha : 0 ≤ a) :
    (dyadicFloor z : ℝ) ^ (-a) ≤ (2 : ℝ) ^ a * z ^ (-a) := by
  have hh : z / 2 ≤ (dyadicFloor z : ℝ) := by
    linarith [lt_two_mul_dyadicFloor z]
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < z / 2) hh (neg_nonpos.mpr ha)
  rw [Real.div_rpow hz.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm] at h
  exact h

/-- The covariate inverse-rank bias is bounded by the common pilot scale. -/
-- @node: tunedMx_inverse_tenth_le
lemma tunedMx_inverse_tenth_le (m : ℕ) (hm : 3 ≤ m) :
    (tunedMx m : ℝ) ^ (-1 / 10 : ℝ) ≤
      (2 : ℝ) ^ (1 / 10 : ℝ) * ((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ) := by
  have hp := pilot_input_mem_Icc m (by omega) (one_le_log_of_three_le m hm)
  have h := dyadicFloor_rpow_neg_le (((m : ℝ) / Real.log m) ^ (10 / 13 : ℝ))
    (1 / 10) (Real.rpow_pos_of_pos (by linarith [hp.1]) _) (by norm_num)
  rw [← Real.rpow_mul (by linarith [hp.1] : 0 ≤ (m : ℝ) / Real.log m)] at h
  norm_num at h
  simpa only [tunedMx, neg_div] using h

/-- The outcome inverse-rank bias is bounded by the same pilot scale. -/
-- @node: tunedMy_inverse_le
lemma tunedMy_inverse_le (m : ℕ) (hm : 3 ≤ m) :
    (tunedMy m : ℝ)⁻¹ ≤
      2 * ((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ) := by
  have hp := pilot_input_mem_Icc m (by omega) (one_le_log_of_three_le m hm)
  have h := dyadicFloor_rpow_neg_le (((m : ℝ) / Real.log m) ^ (1 / 13 : ℝ))
    1 (Real.rpow_pos_of_pos (by linarith [hp.1]) _) (by norm_num)
  rw [← Real.rpow_mul (by linarith [hp.1] : 0 ≤ (m : ℝ) / Real.log m)] at h
  norm_num at h
  simpa only [tunedMy, Real.rpow_neg_one, neg_div] using h

/-- The product of the two rounded pilot ranks has the unrounded eleven-thirteenths bound. -/
-- @node: tuned_pilot_product_le
lemma tuned_pilot_product_le (m : ℕ) (hm : 3 ≤ m) :
    (tunedMx m : ℝ) * (tunedMy m : ℝ) ≤
      ((m : ℝ) / Real.log m) ^ (11 / 13 : ℝ) := by
  have hp := pilot_input_mem_Icc m (by omega) (one_le_log_of_three_le m hm)
  have hx := dyadicFloor_le _ (pilot_power_bounds m (by omega)
    (one_le_log_of_three_le m hm) (10 / 13) (by norm_num)).1
  have hy := dyadicFloor_le _ (pilot_power_bounds m (by omega)
    (one_le_log_of_three_le m hm) (1 / 13) (by norm_num)).1
  have h := mul_le_mul hx hy (by positivity) (by positivity)
  rw [← Real.rpow_add (by linarith [hp.1] : 0 < (m : ℝ) / Real.log m)] at h
  norm_num at h
  exact h

/-- The stochastic pilot variance is at most the square of the common pilot scale. -/
-- @node: tuned_pilot_variance_le
lemma tuned_pilot_variance_le (m : ℕ) (hm : 3 ≤ m) :
    (tunedMx m : ℝ) * tunedMy m * Real.log m / m ≤
      (((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ)) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogpos : 0 < Real.log m := by linarith [one_le_log_of_three_le m hm]
  have hs : 0 < (m : ℝ) / Real.log m := div_pos hmpos hlogpos
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (tuned_pilot_product_le m hm) hlogpos.le) hmpos.le
  have he : ((m : ℝ) / Real.log m) ^ (11 / 13 : ℝ) * Real.log m / m =
      (((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hs.le]
    have hi : Real.log m / (m : ℝ) = ((m : ℝ) / Real.log m) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, inv_div]
    rw [mul_div_assoc, hi, ← Real.rpow_add hs]
    norm_num
  exact h.trans_eq he

/-- The full frozen pilot allowance is bounded by a fixed multiple of the common scale. -/
-- @node: tuned_hAllow_le_pilot_scale
lemma tuned_hAllow_le_pilot_scale (m : ℕ) (hm : 3 ≤ m) :
    hAllow (2 ^ 16) m (tunedMx m) (tunedMy m) ≤
      (2 : ℝ) ^ 16 * ((2 : ℝ) ^ (1 / 10 : ℝ) + 4) *
        ((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ) := by
  let a := ((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ)
  have hp := pilot_input_mem_Icc m (by omega) (one_le_log_of_three_le m hm)
  have ha : 0 ≤ a := by positivity
  have haone : a ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hp.1
      (by norm_num : (-1 / 13 : ℝ) ≤ 0)
  have hv := tuned_pilot_variance_le m hm
  have hs : Real.sqrt ((tunedMx m : ℝ) * tunedMy m * Real.log m / m) ≤ a :=
    Real.sqrt_le_iff.mpr ⟨ha, hv⟩
  have hx := tunedMx_inverse_tenth_le m hm
  have hy := tunedMy_inverse_le m hm
  have ha2 : a ^ 2 ≤ a := by nlinarith
  rw [hAllow, if_neg (by omega : ¬m < 3)]
  change (2 : ℝ) ^ 16 * _ ≤ _
  rw [mul_assoc ((2 : ℝ) ^ 16) ((2 : ℝ) ^ (1 / 10 : ℝ) + 4)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _ ≤ ((2 : ℝ) ^ (1 / 10 : ℝ) + 4) * a
  change _ ≤ (2 : ℝ) ^ (1 / 10 : ℝ) * a at hx
  change _ ≤ 2 * a at hy
  change _ ≤ a ^ 2 at hv
  nlinarith

/-- Every positive polynomial margin eventually absorbs any fixed logarithmic power. -/
-- @node: log_rpow_eventually_le_rpow
lemma log_rpow_eventually_le_rpow (d e : ℝ) (he : 0 < e) :
    ∀ᶠ m : ℕ in atTop, (Real.log m) ^ d ≤ (m : ℝ) ^ e := by
  have h := (isLittleO_log_rpow_rpow_atTop d he).bound (by norm_num : (0 : ℝ) < 1)
  have hn := h.filter_mono (show Filter.map (fun m : ℕ => (m : ℝ)) atTop ≤ atTop from
    tendsto_natCast_atTop_atTop)
  filter_upwards [hn, eventually_ge_atTop 3] with m hm hthree
  change ‖(Real.log (m : ℝ)) ^ d‖ ≤ 1 * ‖(m : ℝ) ^ e‖ at hm
  have hl : 0 ≤ Real.log (m : ℝ) := by linarith [one_le_log_of_three_le m hthree]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) e),
    abs_of_nonneg (Real.rpow_nonneg hl d),
    one_mul] using hm

/-- The unrounded pilot scale eventually has the exponent required by the third-order bias. -/
-- @node: pilot_scale_eventually_le_bias_power
lemma pilot_scale_eventually_le_bias_power :
    ∀ᶠ m : ℕ in atTop,
      ((m : ℝ) / Real.log m) ^ (-1 / 13 : ℝ) ≤ (m : ℝ) ^ (-11 / 145 : ℝ) := by
  filter_upwards [log_rpow_eventually_le_rpow (1 / 13) (2 / 1885) (by norm_num),
    eventually_ge_atTop 3] with m hlog hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlpos : 0 < Real.log m := by linarith [one_le_log_of_three_le m hm]
  rw [Real.div_rpow hmpos.le hlpos.le, neg_div, Real.rpow_neg hlpos.le, div_inv_eq_mul]
  have h := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (m : ℝ) ^ (-(1 / 13 : ℝ)) by positivity)
  rw [← Real.rpow_add hmpos] at h
  norm_num at h
  simpa only [neg_div] using h

/-- The actual frozen pilot allowance eventually satisfies a polynomial bias rate. -/
-- @node: tuned_hAllow_eventually_le_bias_power
lemma tuned_hAllow_eventually_le_bias_power :
    ∀ᶠ m : ℕ in atTop,
      hAllow (2 ^ 16) m (tunedMx m) (tunedMy m) ≤
        ((2 : ℝ) ^ 16 * ((2 : ℝ) ^ (1 / 10 : ℝ) + 4)) *
          (m : ℝ) ^ (-11 / 145 : ℝ) := by
  filter_upwards [pilot_scale_eventually_le_bias_power, eventually_ge_atTop 3] with m hs hm
  exact (tuned_hAllow_le_pilot_scale m hm).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

/-- A pilot allowance with the exponent from (52) gives the sharp norm bias rate. -/
-- @node: tuned_bias_role_rate_of_pilot_bound
lemma tuned_bias_role_rate_of_pilot_bound (n : ℕ) (hn : 3 ≤ roleSize n)
    (D : ℝ)
    (hh : hAllow (2 ^ 16) (roleSize n) (tunedMx (roleSize n)) (tunedMy (roleSize n)) ≤
      D * (roleSize n : ℝ) ^ (-11 / 145 : ℝ)) :
    tunedB n ≤ ((2 : ℝ) ^ 24 * (3 + D ^ 4 + (2 : ℝ) ^ (1 / 5 : ℝ) * D)) *
      (roleSize n : ℝ) ^ (-8 / 29 : ℝ) := by
  let m := roleSize n
  let h := hAllow (2 ^ 16) m (tunedMx m) (tunedMy m)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < roleSize n)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ roleSize n)
  have hnonneg : 0 ≤ h := by
    dsimp [h]
    rw [hAllow, if_neg (show ¬m < 3 by omega)]
    positivity
  have h4 := pow_le_pow_left₀ hnonneg hh 4
  have h4' : h ^ 4 ≤ D ^ 4 * (m : ℝ) ^ (-8 / 29 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hmpos.le] at h4
    have hp : (m : ℝ) ^ ((-11 / 145 : ℝ) * (4 : ℕ)) ≤ (m : ℝ) ^ (-8 / 29 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
    exact h4.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hc := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (m : ℝ) ^ (-1 / 5 : ℝ) by positivity)
  have hc' : h * (m : ℝ) ^ (-1 / 5 : ℝ) ≤ D * (m : ℝ) ^ (-8 / 29 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hmpos,
      show (-11 / 145 : ℝ) + (-1 / 5 : ℝ) = -8 / 29 by norm_num] at hc
    exact hc
  have hb := tunedB_role_bias_components n hn
  change tunedB n ≤ (2 : ℝ) ^ 24 *
    (3 * (m : ℝ) ^ (-8 / 29 : ℝ) + h ^ 4 +
      (2 : ℝ) ^ (1 / 5 : ℝ) * h * (m : ℝ) ^ (-1 / 5 : ℝ)) at hb
  have hcross := mul_le_mul_of_nonneg_left hc'
    (show 0 ≤ (2 : ℝ) ^ (1 / 5 : ℝ) by positivity)
  have hsum : 3 * (m : ℝ) ^ (-8 / 29 : ℝ) + h ^ 4 +
      (2 : ℝ) ^ (1 / 5 : ℝ) * h * (m : ℝ) ^ (-1 / 5 : ℝ) ≤
      (3 + D ^ 4 + (2 : ℝ) ^ (1 / 5 : ℝ) * D) * (m : ℝ) ^ (-8 / 29 : ℝ) := by
    nlinarith
  exact hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hsum (show 0 ≤ (2 : ℝ) ^ 24 by positivity))

/-- Complete role sizes tend to infinity with the total sample size. -/
-- @node: roleSize_tendsto_atTop
lemma roleSize_tendsto_atTop : Tendsto roleSize atTop atTop :=
  Nat.tendsto_div_const_atTop (by norm_num : (13 : ℕ) ≠ 0)

/-- Equation (51) holds eventually for the frozen bias allowance, with a fixed public constant. -/
-- @node: tunedB_eventually_role_rate_bound
lemma tunedB_eventually_role_rate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      tunedB n ≤ C * (roleSize n : ℝ) ^ (-8 / 29 : ℝ) := by
  let D : ℝ := (2 : ℝ) ^ 16 * ((2 : ℝ) ^ (1 / 10 : ℝ) + 4)
  refine ⟨(2 : ℝ) ^ 24 * (3 + D ^ 4 + (2 : ℝ) ^ (1 / 5 : ℝ) * D), by positivity, ?_⟩
  filter_upwards [roleSize_tendsto_atTop.eventually tuned_hAllow_eventually_le_bias_power,
    roleSize_tendsto_atTop.eventually (eventually_ge_atTop 3)] with n hh hn
  exact tuned_bias_role_rate_of_pilot_bound n hn D hh

/-- The squared bias allowance attains the role-size energy rate in (58). -/
-- @node: tunedB_sq_eventually_role_rate_bound
lemma tunedB_sq_eventually_role_rate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (tunedB n) ^ 2 ≤ C * (roleSize n : ℝ) ^ (-16 / 29 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := tunedB_eventually_role_rate_bound
  refine ⟨C ^ 2, by positivity, ?_⟩
  filter_upwards [hb, roleSize_tendsto_atTop.eventually (eventually_ge_atTop 3)] with n hn hm
  have hnonneg : 0 ≤ tunedB n := by
    rw [tunedB, BAllow, if_neg (show roleSize n ≠ 0 by omega)]
    have hh : 0 ≤ hAllow (2 ^ 16) (roleSize n)
        (tunedMx (roleSize n)) (tunedMy (roleSize n)) := by
      rw [hAllow, if_neg (by omega : ¬roleSize n < 3)]
      positivity
    positivity
  have h := pow_le_pow_left₀ hnonneg hn 2
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ roleSize n)] at h
  norm_num at h
  simpa only [neg_div] using h

/-- Conversion from complete roles to observations preserves the squared bias rate. -/
-- @node: tunedB_sq_eventually_frontier_rate_bound
lemma tunedB_sq_eventually_frontier_rate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (tunedB n) ^ 2 ≤ C * frontierRate n := by
  obtain ⟨C, hC, hb⟩ := tunedB_sq_eventually_role_rate_bound
  refine ⟨C * (26 : ℝ) ^ (16 / 29 : ℝ), by positivity, ?_⟩
  filter_upwards [hb, roleSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hm
  have hs := roleSize_rpow_le_sampleSize_rpow n hm (-16 / 29) (by norm_num)
  have hs' : (roleSize n : ℝ) ^ (-16 / 29 : ℝ) ≤
      (26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n := by
    simpa only [neg_div, neg_neg, frontierRate] using hs
  exact hn.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs' hC.le)

/-- The inversion budget in (58) has the sharp rate; only pilot failure is still to be added. -/
-- @node: tuned_inversion_budget_eventually_frontier_rate_bound
lemma tuned_inversion_budget_eventually_frontier_rate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      4 * ((aci (tunedB n) (tunedW n)) ^ 2 +
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) ≤
          C * frontierRate n := by
  obtain ⟨CB, hCB, hb⟩ := tunedB_sq_eventually_frontier_rate_bound
  let R : ℝ := (26 : ℝ) ^ (16 / 29 : ℝ)
  let CW : ℝ := (2 : ℝ) ^ 24 * 1025 * R
  let CV : ℝ := (2 : ℝ) ^ 36 * R
  refine ⟨120 * CB + 500 * CW + 1600 * R + 20 * CV, by positivity, ?_⟩
  filter_upwards [hb, roleSize_tendsto_atTop.eventually (eventually_ge_atTop 3)] with n hB hn
  have hW := tunedW_frontier_rate_bound n hn
  have hJ := tunedJ_frontier_rate_bound n (by omega)
  have hV := tunedV_sqrt_frontier_rate_bound n hn
  have hWnonneg : 0 ≤ tunedW n := by
    rw [tunedW, WAllow, if_neg (show roleSize n ≠ 0 by omega)]
    positivity
  have hi := inversion_budget_le_components (tunedB n) (tunedW n) (tunedV n)
    (tunedJ (roleSize n)) hWnonneg
  change tunedW n ≤ CW * frontierRate n at hW
  change (tunedJ (roleSize n) : ℝ) ^ (-2 : ℤ) ≤ R * frontierRate n at hJ
  change Real.sqrt (tunedV n) ≤ CV * frontierRate n at hV
  exact hi.trans (by nlinarith)

end CausalSmith.Stat.DensityEffectRoughNull

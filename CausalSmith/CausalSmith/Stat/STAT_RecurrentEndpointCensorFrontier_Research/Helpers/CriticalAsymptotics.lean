module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestBandwidthRates
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Critical bandwidth limits

Equation (1) of the critical studentization roadmap: the bandwidth cap becomes
inactive, its logarithm has the exact critical coefficient, and the risk-set
and optional-variation remainders have vanishing deterministic scales.
-/

public section

open Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical bandwidth coefficient is positive and strictly below one half. -/
-- @node: criticalCoefficient_pos_lt_half
lemma criticalCoefficient_pos_lt_half (c : ClassConstants) :
    0 < criticalCoefficient c ∧ criticalCoefficient c < 1 / 2 := by
  have hd : 0 < 2 * c.beta + 2 := by linarith [c.beta_pos]
  constructor
  · exact inv_pos.mpr hd
  · change (2 * c.beta + 2)⁻¹ < 1 / 2
    rw [inv_eq_one_div, div_lt_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)]
    linarith [c.beta_pos]

/-- At exponent one, the declared bandwidth exponent is the critical coefficient. -/
-- @node: bandwidthExponent_eq_criticalCoefficient
lemma bandwidthExponent_eq_criticalCoefficient (c : ClassConstants) (hk : c.kappa = 1) :
    bandwidthExponent c = criticalCoefficient c := by
  simp [bandwidthExponent, criticalCoefficient, hk]

/-- The power bandwidth tends to zero, so the positive cap eventually stops binding. -/
-- @node: critical_bandwidth_eventually_eq_power
lemma critical_bandwidth_eventually_eq_power (c : ClassConstants) (hk : c.kappa = 1) :
    ∀ᶠ n : ℕ in atTop, bandwidth c n = (n : ℝ) ^ (-criticalCoefficient c) := by
  have hp := (tendsto_rpow_neg_atTop (criticalCoefficient_pos_lt_half c).1).comp
    tendsto_natCast_atTop_atTop
  have hc : 0 < c.x0 / 2 := by linarith [c.x0_pos]
  filter_upwards [hp.eventually (gt_mem_nhds hc)] with n hn
  change (n : ℝ) ^ (-criticalCoefficient c) < c.x0 / 2 at hn
  rw [bandwidth_eq_min_power, bandwidthExponent_eq_criticalCoefficient c hk,
    min_eq_right hn.le]

/-- The logarithm of the inverse critical bandwidth is eventually exactly q log n. -/
-- @node: critical_bandwidth_eventually_log
lemma critical_bandwidth_eventually_log (c : ClassConstants) (hk : c.kappa = 1) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (1 / bandwidth c n) = criticalCoefficient c * Real.log n := by
  filter_upwards [critical_bandwidth_eventually_eq_power c hk,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [hn, one_div, Real.log_inv, Real.log_rpow hn0]
  ring

/-- The product n h² is eventually a positive power with exponent 1 - 2q. -/
-- @node: critical_bandwidth_eventually_sample_square
lemma critical_bandwidth_eventually_sample_square (c : ClassConstants) (hk : c.kappa = 1) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * bandwidth c n ^ 2 = (n : ℝ) ^ (1 - 2 * criticalCoefficient c) := by
  filter_upwards [critical_bandwidth_eventually_eq_power c hk,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  nth_rw 1 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn0]
  congr 1
  ring

/-- The log divided by n h² vanishes; this controls the stopped variance remainder. -/
-- @node: critical_log_div_sample_bandwidth_square_tendsto_zero
lemma critical_log_div_sample_bandwidth_square_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => Real.log n / ((n : ℝ) * bandwidth c n ^ 2))
      atTop (nhds 0) := by
  have hr : 0 < 1 - 2 * criticalCoefficient c := by
    linarith [(criticalCoefficient_pos_lt_half c).2]
  have h := ((isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [critical_bandwidth_eventually_sample_square c hk] with n hn
  simp only [Function.comp_apply, hn]

/-- Equivalently, n h² / log n diverges, as required by roadmap equation (1). -/
-- @node: critical_sample_bandwidth_square_div_log_tendsto_atTop
lemma critical_sample_bandwidth_square_div_log_tendsto_atTop
    (c : ClassConstants) (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * bandwidth c n ^ 2 / Real.log n)
      atTop atTop := by
  have h := critical_log_div_sample_bandwidth_square_tendsto_zero c hk
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < Real.log n / ((n : ℝ) * bandwidth c n ^ 2) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn0 : 0 < n := by omega
    exact div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_log_sampleSize hn))
      (mul_pos (by exact_mod_cast hn0) (sq_pos_of_pos (bandwidth_pos_and_le_cap c hn0).1))
  have hgt := tendsto_nhdsWithin_iff.mpr ⟨h, hp⟩
  convert tendsto_inv_nhdsGT_zero.comp hgt using 1
  ext n
  simp [Function.comp_def]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

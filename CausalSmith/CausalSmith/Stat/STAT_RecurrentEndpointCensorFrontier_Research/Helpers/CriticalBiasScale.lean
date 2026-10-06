module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalAsymptotics

/-!
# Negligible continuation bias at the critical scale

Roadmap equation (24): the critical bandwidth's bias power is eventually
n to the power minus one half. Multiplication by the critical normalization
leaves an inverse square root logarithm, which vanishes uniformly over laws.
-/

public section

open Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical bias power has the exact eventual square-root sample rate. -/
-- @node: critical_bandwidth_eventually_bias_power
lemma critical_bandwidth_eventually_bias_power (c : ClassConstants) (hk : c.kappa = 1) :
    ∀ᶠ n : ℕ in atTop,
      bandwidth c n ^ (c.beta + 1) = (Real.sqrt (n : ℝ))⁻¹ := by
  filter_upwards [critical_bandwidth_eventually_eq_power c hk,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd : 2 * c.beta + 2 ≠ 0 := ne_of_gt (by linarith [c.beta_pos])
  have hexp : -criticalCoefficient c * (c.beta + 1) = -(1 / 2 : ℝ) := by
    have hid : (2 * c.beta + 2) * criticalCoefficient c = 1 := mul_inv_cancel₀ hd
    nlinarith
  rw [hn, ← Real.rpow_mul hn0.le, hexp, Real.rpow_neg hn0.le,
    ← Real.sqrt_eq_rpow]

/-- Critical normalization turns the bias power into an inverse square root logarithm. -/
-- @node: critical_bandwidth_eventually_normalized_bias_power
lemma critical_bandwidth_eventually_normalized_bias_power
    (c : ClassConstants) (hk : c.kappa = 1) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n : ℝ) / Real.log n) * bandwidth c n ^ (c.beta + 1) =
        (Real.sqrt (Real.log n))⁻¹ := by
  filter_upwards [critical_bandwidth_eventually_bias_power c hk,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  rw [hn, Real.sqrt_div hn0.le]
  field_simp

/-- The deterministic normalized critical bias envelope vanishes. -/
-- @node: critical_normalized_bias_power_tendsto_zero
lemma critical_normalized_bias_power_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ =>
      Real.sqrt ((n : ℝ) / Real.log n) * bandwidth c n ^ (c.beta + 1))
      atTop (nhds 0) := by
  have h := (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).inv_tendsto_atTop
  apply h.congr'
  filter_upwards [critical_bandwidth_eventually_normalized_bias_power c hk] with n hn
  change (Real.sqrt (Real.log n))⁻¹ = _
  exact hn.symm

/-- The continuation-bias theorem makes each arm's bias negligible along arbitrary
triangular model sequences, without a new moment or regularity assumption. -/
-- @node: critical_continuation_bias_triangular_tendsto_zero
lemma critical_continuation_bias_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / Real.log n) *
      |truncatedMean c (Pseq n) a (bandwidth c n) - armMean (Pseq n) a|)
      atTop (nhds 0) := by
  obtain ⟨B, hB, hbias⟩ := continuation_bias c
  have hlim := (critical_normalized_bias_power_tendsto_zero c hk).mul_const B
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))) _ (by simpa only [zero_mul] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hb := hbias (Pseq n) (hP n) a (bandwidth c n) hh.1 hh.2
  have h := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg ((n : ℝ) / Real.log n))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

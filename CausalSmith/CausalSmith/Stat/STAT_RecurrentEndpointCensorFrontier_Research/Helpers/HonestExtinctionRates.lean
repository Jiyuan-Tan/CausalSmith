module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestBandwidthRates
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestIntervalGeometry

/-! # Finite-range extinction calibration and cap release

The finite pre-envelope bounds extinction before the cap-release index.
After that index the bandwidth and extinction exponent have exact power forms.
These are the discrete and algebraic parts of equation (9) in the calibration.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The cap-release index is an allowed sample size. -/
-- @node: capReleaseIndex_ge_three
lemma capReleaseIndex_ge_three (c : ClassConstants) : 3 ≤ capReleaseIndex c := by
  exact le_max_left _ _

/-- The real cap threshold is below the integer release index. -/
-- @node: capReleaseIndex_ge_threshold
lemma capReleaseIndex_ge_threshold (c : ClassConstants) :
    (c.x0 / 2) ^ (-(bandwidthExponent c)⁻¹) ≤ (capReleaseIndex c : ℝ) := by
  exact (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right 3 (Nat.ceil ((c.x0 / 2) ^
      (-(bandwidthExponent c)⁻¹)))))

/-- The bandwidth cap is inactive at and beyond its release index. -/
-- @node: bandwidth_eq_power_after_capRelease
lemma bandwidth_eq_power_after_capRelease (c : ClassConstants) {n : ℕ}
    (hn : capReleaseIndex c ≤ n) :
    bandwidth c n = (n : ℝ) ^ (-bandwidthExponent c) := by
  have hn3 := (capReleaseIndex_ge_three c).trans hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hh : 0 < c.x0 / 2 := by linarith [c.x0_pos]
  have ha := bandwidthExponent_pos c
  have hthreshold : (c.x0 / 2) ^ (-(bandwidthExponent c)⁻¹) ≤ (n : ℝ) :=
    (capReleaseIndex_ge_threshold c).trans (by exact_mod_cast hn)
  have hpower := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hh _) hthreshold (neg_nonpos.mpr ha.le)
  have hcancel : (-(bandwidthExponent c)⁻¹) * (-bandwidthExponent c) = 1 := by
    rw [neg_mul_neg, inv_mul_cancel₀ ha.ne']
  rw [← Real.rpow_mul hh.le, hcancel, Real.rpow_one] at hpower
  rw [bandwidth_eq_min_power, min_eq_right hpower]

/-- The extinction argument is the declared positive power of sample size
once the bandwidth cap has released. -/
-- @node: extinction_argument_eq_power_after_capRelease
lemma extinction_argument_eq_power_after_capRelease (c : ClassConstants) {n : ℕ}
    (hn : capReleaseIndex c ≤ n) :
    (n : ℝ) * (bandwidth c n) ^ c.kappa =
      (n : ℝ) ^ (1 - bandwidthExponent c * c.kappa) := by
  have hn3 := (capReleaseIndex_ge_three c).trans hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [bandwidth_eq_power_after_capRelease c hn, ← Real.rpow_mul hn0.le]
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-bandwidthExponent c * c.kappa) := by
      rw [Real.rpow_one]
    _ = (n : ℝ) ^ (1 - bandwidthExponent c * c.kappa) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

/-- The set defining the pre-envelope is a finite image of sample sizes. -/
-- @node: extinctionPreEnvelope_set_finite
lemma extinctionPreEnvelope_set_finite (c : ClassConstants) :
    Set.Finite {x : ℝ | ∃ n ∈ Finset.Ico 3 (capReleaseIndex c),
      x = Real.exp (-(extinctionExponent c * n *
        (bandwidth c n) ^ c.kappa)) / riskScale c n} := by
  let f : ℕ → ℝ := fun n => Real.exp (-(extinctionExponent c * n *
    (bandwidth c n) ^ c.kappa)) / riskScale c n
  have heq : {x : ℝ | ∃ n ∈ Finset.Ico 3 (capReleaseIndex c), x = f n} =
      f '' (↑(Finset.Ico 3 (capReleaseIndex c)) : Set ℕ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
  change Set.Finite {x : ℝ | ∃ n ∈ Finset.Ico 3 (capReleaseIndex c), x = f n}
  rw [heq]
  exact (Finset.finite_toSet _).image f

/-- Each sample size before cap release is controlled by the finite
pre-envelope, without an asymptotic estimate. -/
-- @node: extinction_le_preEnvelope_mul_rate
lemma extinction_le_preEnvelope_mul_rate (c : ClassConstants) {n : ℕ}
    (hn : 3 ≤ n) (hpre : n < capReleaseIndex c) :
    Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) ≤
      extinctionPreEnvelope c * riskScale c n := by
  have hmem : Real.exp (-(extinctionExponent c * n *
      (bandwidth c n) ^ c.kappa)) / riskScale c n ∈
      {x : ℝ | ∃ m ∈ Finset.Ico 3 (capReleaseIndex c),
        x = Real.exp (-(extinctionExponent c * m *
          (bandwidth c m) ^ c.kappa)) / riskScale c m} :=
    ⟨n, Finset.mem_Ico.mpr ⟨hn, hpre⟩, rfl⟩
  have hsup := le_csSup (extinctionPreEnvelope_set_finite c).bddAbove hmem
  exact (div_le_iff₀ (riskScale_pos c hn)).mp hsup

/-- A logarithmic tangent bound controls the power-exponential tail beyond
its mode, and at its mode controls the entire positive half-line. -/
-- @node: power_exp_le_at_or_after_mode
lemma power_exp_le_at_or_after_mode {x z q δ C : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hC : 0 < C)
    (hmode : q ≤ C * δ * z ^ δ)
    (hside : z ≤ x ∨ q = C * δ * z ^ δ) :
    x ^ q * Real.exp (-(C * x ^ δ)) ≤
      z ^ q * Real.exp (-(C * z ^ δ)) := by
  have hxp := Real.rpow_pos_of_pos hx δ
  have hzp := Real.rpow_pos_of_pos hz δ
  have ht := Real.log_le_sub_one_of_pos (div_pos hxp hzp)
  rw [Real.log_div hxp.ne' hzp.ne', Real.log_rpow hx, Real.log_rpow hz] at ht
  have ht' := (le_div_iff₀ hzp).mp (show
      δ * (Real.log x - Real.log z) + 1 ≤ x ^ δ / z ^ δ by linarith)
  have htC := mul_le_mul_of_nonneg_left ht' hC.le
  have hlog : q * (Real.log x - Real.log z) ≤
      C * δ * z ^ δ * (Real.log x - Real.log z) := by
    rcases hside with hzx | heq
    · exact mul_le_mul_of_nonneg_right hmode (sub_nonneg.mpr
        (Real.log_le_log hz hzx))
    · rw [heq]
  have hexp : Real.log x * q - C * x ^ δ ≤ Real.log z * q - C * z ^ δ := by
    nlinarith only [htC, hlog]
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hz,
    ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [sub_eq_add_neg] using hexp)

/-- The maximum of the starting point and the analytic mode bounds every
power-exponential value to the right of the starting point. -/
-- @node: power_exp_le_max_mode
lemma power_exp_le_max_mode {x N q δ C : ℝ}
    (hN : 0 < N) (hx : N ≤ x) (hq : 0 < q) (hδ : 0 < δ) (hC : 0 < C) :
    x ^ q * Real.exp (-(C * x ^ δ)) ≤
      (max N ((q / (C * δ)) ^ (1 / δ))) ^ q *
        Real.exp (-(C * (max N ((q / (C * δ)) ^ (1 / δ))) ^ δ)) := by
  have hp : 0 < q / (C * δ) := div_pos hq (mul_pos hC hδ)
  have hpeak : 0 < (q / (C * δ)) ^ (1 / δ) := Real.rpow_pos_of_pos hp _
  have heq : C * δ * ((q / (C * δ)) ^ (1 / δ)) ^ δ = q := by
    rw [one_div, Real.rpow_inv_rpow hp.le hδ.ne']
    exact mul_div_cancel₀ q (mul_pos hC hδ).ne'
  rcases le_total ((q / (C * δ)) ^ (1 / δ)) N with hn | hn
  · rw [max_eq_left hn]
    apply power_exp_le_at_or_after_mode (hN.trans_le hx) hN hC _ (Or.inl hx)
    calc
      q = C * δ * ((q / (C * δ)) ^ (1 / δ)) ^ δ := heq.symm
      _ ≤ C * δ * N ^ δ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hpeak.le hn hδ.le) (mul_pos hC hδ).le
  · rw [max_eq_right hn]
    exact power_exp_le_at_or_after_mode (hN.trans_le hx) hpeak hC
      heq.ge (Or.inr heq.symm)

/-- The extinction exponent is strictly positive under overlap, endpoint
retention, and the death envelope. -/
-- @node: extinctionExponent_pos
lemma extinctionExponent_pos (c : ClassConstants) : 0 < extinctionExponent c := by
  unfold extinctionExponent
  exact div_pos (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _))
    (by norm_num)

/-- Off the critical regime the squared-risk rate is a single negative
power, with the same exponent used by the extinction tail envelope. -/
-- @node: noncritical_riskScale_eq_neg_power
lemma noncritical_riskScale_eq_neg_power (c : ClassConstants) (hk : c.kappa ≠ 1)
    (n : ℕ) :
    riskScale c n = (n : ℝ) ^ (-(if c.kappa > 1 then riskExponent c else 1)) := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · simp only [riskScale, if_pos hlt, if_neg (not_lt.mpr hlt.le), Real.rpow_neg_one]
  · simp only [riskScale, if_neg (not_lt.mpr hgt.le), if_neg hk, if_pos hgt,
      riskExponent]

/-- Beyond cap release, the analytic tail coefficient controls extinction
in both noncritical regimes. -/
-- @node: noncritical_extinction_le_tailEnvelope_mul_rate
lemma noncritical_extinction_le_tailEnvelope_mul_rate (c : ClassConstants)
    (hk : c.kappa ≠ 1) {n : ℕ} (hn : capReleaseIndex c ≤ n) :
    Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) ≤
      extinctionTailEnvelope c * riskScale c n := by
  let q : ℝ := if c.kappa > 1 then riskExponent c else 1
  let δ : ℝ := 1 - bandwidthExponent c * c.kappa
  have hq : 0 < q := by
    dsimp [q]
    split_ifs with hkgt
    · exact (riskExponent_pos_lt_one c hkgt).1
    · norm_num
  have hN : 0 < (capReleaseIndex c : ℝ) := by
    exact_mod_cast (show 0 < capReleaseIndex c by
      have := capReleaseIndex_ge_three c
      omega)
  have hn0 : 0 < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hmax := power_exp_le_max_mode (x := (n : ℝ)) hN (by exact_mod_cast hn) hq
    (extinctionPower_pos c) (extinctionExponent_pos c)
  change (n : ℝ) ^ q * Real.exp (-(extinctionExponent c * (n : ℝ) ^ δ)) ≤
    (max (capReleaseIndex c : ℝ)
      ((q / (extinctionExponent c * δ)) ^ (1 / δ))) ^ q *
    Real.exp (-(extinctionExponent c * (max (capReleaseIndex c : ℝ)
      ((q / (extinctionExponent c * δ)) ^ (1 / δ))) ^ δ)) at hmax
  have hprod : (n : ℝ) ^ q * (n : ℝ) ^ (-q) = 1 := by
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
  have hm := mul_le_mul_of_nonneg_right hmax
    (Real.rpow_pos_of_pos hn0 (-q)).le
  rw [mul_assoc, mul_left_comm, hprod, mul_one] at hm
  rw [noncritical_riskScale_eq_neg_power c hk, extinctionTailEnvelope, if_neg hk]
  rw [show extinctionExponent c * n * (bandwidth c n) ^ c.kappa =
      extinctionExponent c * (n : ℝ) ^ δ by
    rw [mul_assoc, extinction_argument_eq_power_after_capRelease c hn]]
  exact hm

/-- At the critical endpoint, division by log three converts the power
maximum into the logarithmic risk rate. -/
-- @node: critical_extinction_le_tailEnvelope_mul_rate
lemma critical_extinction_le_tailEnvelope_mul_rate (c : ClassConstants)
    (hk : c.kappa = 1) {n : ℕ} (hn : capReleaseIndex c ≤ n) :
    Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) ≤
      extinctionTailEnvelope c * riskScale c n := by
  let δ : ℝ := 1 - bandwidthExponent c * c.kappa
  let z : ℝ := max (capReleaseIndex c : ℝ)
    ((1 / (extinctionExponent c * δ)) ^ (1 / δ))
  have hN : 0 < (capReleaseIndex c : ℝ) := by
    exact_mod_cast (show 0 < capReleaseIndex c by
      have := capReleaseIndex_ge_three c
      omega)
  have hn0 : 0 < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hn3 := (capReleaseIndex_ge_three c).trans hn
  have hmax := power_exp_le_max_mode (x := (n : ℝ)) hN (by exact_mod_cast hn)
    (by norm_num : (0 : ℝ) < 1) (extinctionPower_pos c) (extinctionExponent_pos c)
  simp only [Real.rpow_one] at hmax
  change (n : ℝ) * Real.exp (-(extinctionExponent c * (n : ℝ) ^ δ)) ≤
    z * Real.exp (-(extinctionExponent c * z ^ δ)) at hmax
  have hz : 0 ≤ z := hN.le.trans (le_max_left _ _)
  have hlog : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hfactor : 1 ≤ Real.log (n : ℝ) / Real.log 3 :=
    (one_le_div₀ hl3).2 hlog
  have ht : 0 ≤ z * Real.exp (-(extinctionExponent c * z ^ δ)) :=
    mul_nonneg hz (Real.exp_pos _).le
  have hm : z * Real.exp (-(extinctionExponent c * z ^ δ)) ≤
      (z * Real.exp (-(extinctionExponent c * z ^ δ)) / Real.log 3) *
        Real.log (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hfactor ht
    simpa only [mul_one, one_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm
  have htotal : Real.exp (-(extinctionExponent c * (n : ℝ) ^ δ)) ≤
      ((z * Real.exp (-(extinctionExponent c * z ^ δ)) / Real.log 3) *
        Real.log (n : ℝ)) / (n : ℝ) := by
    apply (le_div_iff₀ hn0).2
    calc
      _ = (n : ℝ) * Real.exp (-(extinctionExponent c * (n : ℝ) ^ δ)) := mul_comm _ _
      _ ≤ _ := hmax.trans hm
  rw [show extinctionExponent c * n * (bandwidth c n) ^ c.kappa =
      extinctionExponent c * (n : ℝ) ^ δ by
    rw [mul_assoc, extinction_argument_eq_power_after_capRelease c hn]]
  simp only [extinctionTailEnvelope, riskScale, if_pos hk,
    if_neg (by linarith : ¬c.kappa < 1), if_neg (by linarith : ¬c.kappa > 1)]
  simpa only [z, δ, div_eq_mul_inv, mul_assoc] using htotal

/-- Equation (9) holds at every allowed sample size, using the finite
pre-envelope before release and the analytic maximum thereafter. -/
-- @node: bandwidth_extinction_le_envelope_mul_riskScale
lemma bandwidth_extinction_le_envelope_mul_riskScale (c : ClassConstants)
    {n : ℕ} (hn : 3 ≤ n) :
    Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) ≤
      max (extinctionPreEnvelope c) (extinctionTailEnvelope c) * riskScale c n := by
  by_cases hpre : n < capReleaseIndex c
  · exact (extinction_le_preEnvelope_mul_rate c hn hpre).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (riskScale_pos c hn).le)
  · have hrelease : capReleaseIndex c ≤ n := le_of_not_gt hpre
    have ht : Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) ≤
        extinctionTailEnvelope c * riskScale c n := by
      by_cases hk : c.kappa = 1
      · exact critical_extinction_le_tailEnvelope_mul_rate c hk hrelease
      · exact noncritical_extinction_le_tailEnvelope_mul_rate c hk hrelease
    exact ht.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (riskScale_pos c hn).le)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

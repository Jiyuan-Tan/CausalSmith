module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic

/-! Quantitative comparison of the inverse scales at the second frontier elbow. -/
public section
noncomputable section
open Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The public logarithmic sample size is at least one for nonzero samples. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: logScale_one_le
lemma logScale_one_le (n : ℕ) (hn : 1 ≤ n) : 1 ≤ logScale n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ logScale n := Real.log_le_log (Real.exp_pos 1)
      (le_mul_of_one_le_right (Real.exp_pos 1).le hn')

/-- At the second elbow the inverse square-root power is the reciprocal square root. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: secondElbow_inverse_sqrt
lemma secondElbow_inverse_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (logScale n)^(-1/2 : ℝ) = (Real.sqrt (logScale n))⁻¹ := by
  have hL : 0 ≤ logScale n := (by norm_num : (0 : ℝ) ≤ 1).trans (logScale_one_le n hn)
  rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg hL,
    ← Real.sqrt_eq_rpow]

/-- The polynomial inverse scale at the second elbow is a fixed constant over log(en). [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: polynomialScale_at_secondElbow
lemma polynomialScale_at_secondElbow (n : ℕ) (hn : 1 ≤ n) :
    polynomialScale ((logScale n)^(-1/2 : ℝ)) n =
      Real.log (Real.exp 1 + 1) / logScale n := by
  have hL : 0 < logScale n := lt_of_lt_of_le zero_lt_one (logScale_one_le n hn)
  have hsq : ((logScale n)^(-1/2 : ℝ))^2 * logScale n = 1 := by
    rw [secondElbow_inverse_sqrt n hn, inv_pow, Real.sq_sqrt hL.le,
      inv_mul_cancel₀ hL.ne']
  simp only [polynomialScale, hsq]

/-- The logarithm of log(en) is negligible compared with log(en). [This is the stated conclusion](goal). -/
-- @node: log_logScale_div_tendsto_zero
lemma log_logScale_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (logScale n) / logScale n) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL

/-- At the second elbow the Fourier logarithm is comparable to log(en). [Under the stated conditions](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: secondElbow_log_bounds
lemma secondElbow_log_bounds (beta kappa : ℝ)
    (hd : 0 ≤ effDim beta kappa) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
      logScale n / 4 ≤ Real.log (Real.exp 1 +
        n * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa) ∧
      Real.log (Real.exp 1 +
        n * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa) ≤ 4 * logScale n := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (effDim beta kappa / 2) * (Real.log (logScale n) / logScale n) < 1/2 :=
    (tendsto_const_nhds.mul log_logScale_div_tendsto_zero).eventually
      (gt_mem_nhds (by norm_num))
  have hLtop : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1
    (hsmall.and (hLtop.eventually_ge_atTop 4))
  refine ⟨max n0 1, le_max_right _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hsmalln, hL4⟩ := hn0 n ((le_max_left _ _).trans hn)
  have hL : 0 < logScale n := by linarith
  have hpow : 0 < ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa := by positivity
  have hlogn : Real.log (n : ℝ) = logScale n - 1 := by
    rw [logScale, Real.log_mul (Real.exp_pos 1).ne' hnpos.ne', Real.log_exp]
    ring
  have hlogpow : Real.log (((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa) =
      -(effDim beta kappa / 2) * Real.log (logScale n) := by
    rw [Real.log_rpow (by positivity), Real.log_rpow hL]
    ring
  have hsmall' : (effDim beta kappa / 2) * Real.log (logScale n) < logScale n / 2 := by
    have h := (mul_lt_mul_of_pos_right hsmalln hL)
    field_simp at h
    nlinarith
  constructor
  · have hmono := Real.log_le_log (mul_pos hnpos hpow)
      (le_add_of_nonneg_left (Real.exp_pos 1).le :
        (n : ℝ) * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa ≤ _)
    rw [Real.log_mul hnpos.ne' hpow.ne', hlogn, hlogpow] at hmono
    linarith
  · have hsig : (logScale n)^(-1/2 : ℝ) ≤ 1 := by
      rw [secondElbow_inverse_sqrt n hn1]
      apply inv_le_one_of_one_le₀
      exact (Real.sqrt_le_sqrt (logScale_one_le n hn1)).trans_eq' (by norm_num)
    have hp1 : ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa ≤ 1 :=
      Real.rpow_le_one (by positivity) hsig hd
    have harg : Real.exp 1 + (n : ℝ) * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa ≤
        2 * (Real.exp 1 * n) := by
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hm := mul_le_mul_of_nonneg_left hp1 hnpos.le
      nlinarith
    have hmono := Real.log_le_log (by positivity : 0 < Real.exp 1 +
      (n : ℝ) * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa) harg
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), ← logScale] at hmono
    have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
    linarith

/-- Both inverse scales agree up to fixed constants at the second elbow. [Under the stated conditions](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: secondElbow_comparison
lemma secondElbow_comparison (beta kappa : ℝ) (hd : 0 ≤ effDim beta kappa) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0,
      fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤
        C * polynomialScale ((logScale n)^(-1/2 : ℝ)) n ∧
      polynomialScale ((logScale n)^(-1/2 : ℝ)) n ≤
        C * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n := by
  let a := Real.log (Real.exp 1 + 1)
  have ha : 0 < a := Real.log_pos (by linarith [Real.exp_pos (1 : ℝ)])
  let C := max (2/a) (2*a)
  have hCa : 2/a ≤ C := le_max_left _ _
  have haC : 2*a ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 2*a) haC
  obtain ⟨n0, hn01, hbounds⟩ := secondElbow_log_bounds beta kappa hd
  refine ⟨C, hC, n0, ?_⟩
  intro n hn
  have hn1 := hn01.trans hn
  have hL : 0 < logScale n := lt_of_lt_of_le zero_lt_one (logScale_one_le n hn1)
  let D := Real.log (Real.exp 1 +
    n * ((logScale n)^(-1/2 : ℝ)) ^ effDim beta kappa)
  obtain ⟨hDlo, hDhi⟩ := hbounds n hn
  change logScale n / 4 ≤ D at hDlo
  change D ≤ 4 * logScale n at hDhi
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hDlo
  have hsL := Real.sqrt_nonneg (logScale n)
  have hsD := Real.sqrt_nonneg D
  have hsLpos := Real.sqrt_pos.mpr hL
  have hsDpos := Real.sqrt_pos.mpr hD
  have hsLsq := Real.sq_sqrt hL.le
  have hsDsq := Real.sq_sqrt hD.le
  have hrootlo : Real.sqrt (logScale n) / 2 ≤ Real.sqrt D := by nlinarith
  have hroothi : Real.sqrt D ≤ 2 * Real.sqrt (logScale n) := by nlinarith
  have hprodlo : logScale n / 2 ≤ Real.sqrt (logScale n) * Real.sqrt D := by
    nlinarith [mul_le_mul_of_nonneg_left hrootlo hsL]
  have hprodhi : Real.sqrt (logScale n) * Real.sqrt D ≤ 2 * logScale n := by
    nlinarith [mul_le_mul_of_nonneg_left hroothi hsL]
  have hprodpos : 0 < Real.sqrt (logScale n) * Real.sqrt D := mul_pos hsLpos hsDpos
  have hF : fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n =
      1 / (Real.sqrt (logScale n) * Real.sqrt D) := by
    change (logScale n)^(-1/2 : ℝ) / Real.sqrt D = _
    calc
      _ = (Real.sqrt (logScale n))⁻¹ / Real.sqrt D :=
        congrArg (fun x : ℝ => x / Real.sqrt D) (secondElbow_inverse_sqrt n hn1)
      _ = _ := by field_simp
  have hFlo : 1 / (2 * logScale n) ≤
      fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n := by
    rw [hF]
    exact one_div_le_one_div_of_le hprodpos hprodhi
  have hFhi : fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤
      2 / logScale n := by
    rw [hF]
    apply (div_le_div_iff₀ hprodpos hL).mpr
    nlinarith
  rw [polynomialScale_at_secondElbow n hn1]
  change fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤ C * (a / logScale n) ∧
    a / logScale n ≤ C * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n
  constructor
  · apply hFhi.trans
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hL).mpr
    exact (div_le_iff₀ ha).mp hCa
  · calc
      a / logScale n ≤ C * (1 / (2 * logScale n)) := by
        apply (div_le_iff₀ hL).mpr
        have heq : C * (1 / (2 * logScale n)) * logScale n = C/2 := by field_simp
        rw [heq]
        linarith
      _ ≤ C * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n :=
        mul_le_mul_of_nonneg_left hFlo hC.le

end CausalSmith.Stat.NoisydoseWeakdesignTransition

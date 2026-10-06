module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.FrontierElbows

/-! Fixed positive noise selects the compact-support branch and its iterated-logarithm order. -/
public section
noncomputable section
open Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The public sample logarithm diverges. [This is the stated conclusion](goal). -/
-- @node: logScale_tendsto_atTop
lemma logScale_tendsto_atTop : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))

/-- Every fixed positive noise eventually exceeds both branch cutoffs. [Under the stated conditions](hyp:hd,hs). [This is the stated conclusion](goal). -/
-- @node: fixedNoise_frontierScale_eq
lemma fixedNoise_frontierScale_eq (beta kappa sigma : ℝ)
    (hd : 0 < effDim beta kappa) (hs : 0 < sigma) :
    ∀ᶠ n : ℕ in atTop, frontierScale beta kappa sigma n = polynomialScale sigma n := by
  have hD : Tendsto (fun n : ℕ => directScale beta kappa n) atTop (𝓝 0) := by
    simpa only [directScale, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hd)).comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun n : ℕ => (logScale n)^(-1/2 : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
      logScale_tendsto_atTop using 1 <;> norm_num [Function.comp_def]
  filter_upwards [hD.eventually (gt_mem_nhds hs), hE.eventually (gt_mem_nhds hs)] with n hnD hnE
  simp only [frontierScale, if_neg (not_le.mpr hnD), if_neg (not_le.mpr hnE)]

/-- The compact-support scale is bounded above and below by the iterated-logarithm scale. [Under the stated conditions](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: fixedNoise_polynomialScale_bounds
lemma fixedNoise_polynomialScale_bounds (sigma : ℝ) (hs : 0 < sigma) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log (Real.log n) / Real.log n ∧
      (1/4 : ℝ) * (Real.log (Real.log n) / Real.log n) ≤ polynomialScale sigma n ∧
      polynomialScale sigma n ≤ 2 * (Real.log (Real.log n) / Real.log n) := by
  have hx : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hxx := Real.tendsto_log_atTop.comp hx
  filter_upwards [eventually_ge_atTop (1 : ℕ), hx.eventually_ge_atTop 1,
    hxx.eventually_ge_atTop 0,
    hxx.eventually_ge_atTop (-2 * Real.log (sigma^2)),
    hxx.eventually_ge_atTop (Real.log (Real.exp 1 + 2*sigma^2))] with n hn hx1 hlog0 hlo hhi
  simp only [Function.comp_def] at hlog0 hlo hhi
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hL : logScale n = 1 + Real.log n := by
    rw [logScale, Real.log_mul (Real.exp_pos 1).ne' hnpos.ne', Real.log_exp]
  have hxpos : 0 < Real.log (n : ℝ) := by linarith
  have hLpos : 0 < logScale n := by rw [hL]; linarith
  have hs2 : 0 < sigma^2 := sq_pos_of_pos hs
  have hargpos : 0 < Real.exp 1 + sigma^2 * logScale n := by positivity
  have hloglo : Real.log (Real.log n) / 2 ≤
      Real.log (Real.exp 1 + sigma^2 * logScale n) := by
    have hm := Real.log_le_log (mul_pos hs2 hxpos)
      (show sigma^2 * Real.log n ≤ Real.exp 1 + sigma^2 * logScale n by
        rw [hL]; nlinarith [Real.exp_pos 1])
    rw [Real.log_mul hs2.ne' hxpos.ne'] at hm
    linarith
  have hloghi : Real.log (Real.exp 1 + sigma^2 * logScale n) ≤
      2 * Real.log (Real.log n) := by
    have hm := Real.log_le_log hargpos
      (show Real.exp 1 + sigma^2 * logScale n ≤
        (Real.exp 1 + 2*sigma^2) * Real.log n by
        rw [hL]; nlinarith [Real.exp_pos 1])
    rw [Real.log_mul (by positivity) hxpos.ne'] at hm
    linarith
  refine ⟨div_nonneg hlog0 hxpos.le, ?_, ?_⟩
  · change _ ≤ Real.log (Real.exp 1 + sigma^2 * logScale n) / logScale n
    apply (le_div_iff₀ hLpos).mpr
    rw [hL]
    have heq : (1/4 : ℝ) * (Real.log (Real.log n) / Real.log n) *
        (1 + Real.log n) = Real.log (Real.log n) / 4 +
        (Real.log (Real.log n) / Real.log n) / 4 := by field_simp; ring
    rw [heq]
    rw [hL] at hloglo
    have hdiv : Real.log (Real.log n) / Real.log n ≤ Real.log (Real.log n) :=
      (div_le_iff₀ hxpos).mpr (le_mul_of_one_le_right hlog0 hx1)
    linarith
  · change Real.log (Real.exp 1 + sigma^2 * logScale n) / logScale n ≤ _
    apply (div_le_iff₀ hLpos).mpr
    have hdiv0 := div_nonneg hlog0 hxpos.le
    have heq : 2 * (Real.log (Real.log n) / Real.log n) * logScale n =
        2 * Real.log (Real.log n) + 2 * (Real.log (Real.log n) / Real.log n) := by
      rw [hL]; field_simp; ring
    rw [heq]
    linarith

/-- Taking the fixed smoothness power preserves the two-sided scale comparison. [Under the stated conditions](hyp:hb,hd,hs). [This is the stated conclusion](goal). -/
-- @node: fixedNoise_frontierRate_bounds
lemma fixedNoise_frontierRate_bounds (beta kappa sigma : ℝ)
    (hb : 0 ≤ beta) (hd : 0 < effDim beta kappa) (hs : 0 < sigma) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ (Real.log (Real.log n) / Real.log n)^beta ∧
      (1/4 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta ≤
        frontierRate beta kappa sigma n ∧
      frontierRate beta kappa sigma n ≤
        (2 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta := by
  filter_upwards [fixedNoise_frontierScale_eq beta kappa sigma hd hs,
    fixedNoise_polynomialScale_bounds sigma hs] with n hbranch hbounds
  rw [frontierRate, hbranch]
  obtain ⟨ht, hlo, hhi⟩ := hbounds
  refine ⟨Real.rpow_nonneg ht _, ?_, ?_⟩
  · have hp := Real.rpow_le_rpow (mul_nonneg (by norm_num) ht) hlo hb
    rwa [Real.mul_rpow (by norm_num) ht] at hp
  · have hp := Real.rpow_le_rpow ((mul_nonneg (by norm_num) ht).trans hlo) hhi hb
    rwa [Real.mul_rpow (by norm_num) ht] at hp

end CausalSmith.Stat.NoisydoseWeakdesignTransition

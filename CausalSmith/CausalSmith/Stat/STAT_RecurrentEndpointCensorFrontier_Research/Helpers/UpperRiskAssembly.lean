module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionSecondMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceFiniteRisk

/-! # Assembly of the finite-sample arm risk

Projection cannot increase error for an arm mean in its allowed range. The
exact error decomposition and the proved recurrence, death, and extinction
bounds give the full stochastic envelope, retaining the actual squared bias.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every model-class arm mean lies in the estimator's projection interval. -/
-- @node: armMean_mem_projectionRange
lemma armMean_mem_projectionRange (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) : armMean P a ∈ Icc (0 : ℝ) c.lambdaMax := by
  have hf := modelClass_target_intervalIntegrable c P hP a
  have hl : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ survival P a t * P.lam a t ∧ survival P a t * P.lam a t ≤ c.lambdaMax := by
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht
    have hb := hP.recurrenceBounds a t ht
    have hlam : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hb.1
    exact ⟨mul_nonneg (Real.exp_pos _).le hlam,
      (mul_le_mul_of_nonneg_right hs.2 hlam).trans (by simpa using hb.2)⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun t ht => (hp t ht).1)
  · have hi := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (by norm_num) hf (intervalIntegrable_const) (fun t ht => (hp t ht).2)
    simpa [armMean] using hi

/-- Clipping to the arm range decreases squared error about a target in it. -/
-- @node: projectArm_sq_error_le
lemma projectArm_sq_error_le (c : ClassConstants) (x m : ℝ)
    (hm : m ∈ Icc (0 : ℝ) c.lambdaMax) :
    (projectArm c x - m) ^ 2 ≤ (x - m) ^ 2 := by
  unfold projectArm
  by_cases hx : x ≤ 0
  · rw [min_eq_right (hx.trans (hm.1.trans hm.2)), max_eq_left hx]
    nlinarith [sq_nonneg x, mul_nonneg (neg_nonneg.mpr hx) hm.1]
  · by_cases hxl : c.lambdaMax ≤ x
    · rw [min_eq_left hxl, max_eq_right (hm.1.trans hm.2)]
      nlinarith [sq_nonneg (x - c.lambdaMax),
        mul_nonneg (sub_nonneg.mpr hxl) (sub_nonneg.mpr hm.2)]
    · rw [min_eq_right (le_of_not_ge hxl), max_eq_right (le_of_not_ge hx)]

/-- The decomposition and extinction support bound control the projected
squared error pathwise, without a covariance assertion. -/
-- @node: muHatAt_sq_error_le_components_ae
lemma muHatAt_sq_error_le_components_ae (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    {h : ℝ} (hh : 0 < h) (hhcap : h ≤ c.x0 / 2) :
    ∀ᵐ s ∂sampleLaw P n, (muHatAt c h a s - armMean P a) ^ 2 ≤
      2 * (truncatedMean c P a h - armMean P a) ^ 2 +
      6 * recurrenceError c P a s h ^ 2 + 6 * deathError c P a s h ^ 2 +
      6 * ({s : Fin n → ObsHistory | riskSet a s (1 - h) = 0}).indicator
        (fun _ => (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2) s := by
  have hd := (exact_error_decomposition c P hP.iid hP.randomAssignment
    hP.poissonRecurrence hP.deathHazard hP.recurrenceDeathIndependence
    hP.independentCensoring hP.deathBounds hP.assignmentLaw).1 n hn
  filter_upwards [hd, extinctionError_sq_le_endpointIndicator_ae c P hP a n hh]
    with s hs he
  have hid := hs a h hh.le hhcap
  have hclip := projectArm_sq_error_le c (muTildeAt c h a s) (armMean P a)
    (armMean_mem_projectionRange c P hP a)
  change (muHatAt c h a s - armMean P a) ^ 2 ≤ _ at hclip
  have hthree : (recurrenceError c P a s h - deathError c P a s h -
      extinctionError c P a s h) ^ 2 ≤
      3 * (recurrenceError c P a s h ^ 2 + deathError c P a s h ^ 2 +
        extinctionError c P a s h ^ 2) := by
    nlinarith [sq_nonneg (recurrenceError c P a s h + deathError c P a s h),
      sq_nonneg (recurrenceError c P a s h + extinctionError c P a s h),
      sq_nonneg (deathError c P a s h - extinctionError c P a s h)]
  have htwo : (muTildeAt c h a s - armMean P a) ^ 2 ≤
      2 * (muTildeAt c h a s - truncatedMean c P a h) ^ 2 +
        2 * (truncatedMean c P a h - armMean P a) ^ 2 := by
    nlinarith [sq_nonneg (muTildeAt c h a s - truncatedMean c P a h -
      (truncatedMean c P a h - armMean P a))]
  rw [hid] at htwo
  nlinarith

/-- The full finite-sample stochastic risk envelope, leaving only the
actual deterministic bias to be bounded by the Taylor-envelope calculation. -/
-- @node: upper_risk_with_actual_bias
lemma upper_risk_with_actual_bias (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    {h : ℝ} (hh : 0 < h) (hhcap : h ≤ c.x0 / 2) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c h a) (armMean P a) ≤
      2 * (truncatedMean c P a h - armMean P a) ^ 2 +
      (12 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
        (c.lambdaMax * Real.exp c.dMax +
          c.lambdaMax ^ 2 * c.dMax * Real.exp (3 * c.dMax))) *
            (n : ℝ)⁻¹ * varianceFactor c h +
      (6 * weightEnvelope c ^ 2 * c.lambdaMax ^ 2 * Real.exp (2 * c.dMax)) *
        Real.exp (-(c.pMin * c.gMin * Real.exp (-c.dMax) / 2 * n * h ^ c.kappa)) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hhx : h ≤ c.x0 := by linarith [c.x0_pos]
  have hh1 : h ≤ 1 := by linarith [c.x0_le]
  have hn0 : 0 < n := by omega
  let E := {s : Fin n → ObsHistory | riskSet a s (1 - h) = 0}
  let B := (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2
  have hE : MeasurableSet E := measurableSet_endpointRiskZero a h
  have hR := (recurrenceError_secondMoment_eq_exposure_energy c P hP a n hh hh1).1
  have hD := deathError_sq_integrable c P hP a n hh.le hh1
  have hI : Integrable (E.indicator (fun _ => B)) (sampleLaw P n) :=
    (integrable_const B).indicator hE
  have hi := (((integrable_const (2 * (truncatedMean c P a h - armMean P a) ^ 2)).add
    (hR.const_mul 6)).add (hD.const_mul 6)).add (hI.const_mul 6)
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s : Fin n → ObsHistory =>
      sq_nonneg (muHatAt c h a s - armMean P a)))
    hi (muHatAt_sq_error_le_components_ae c P hP a n hn hh hhcap)
  simp only [Pi.add_apply] at hbound
  have h0 := integrable_const (μ := sampleLaw P n)
    (2 * (truncatedMean c P a h - armMean P a) ^ 2)
  have hs3 := integral_add ((h0.add (hR.const_mul 6)).add (hD.const_mul 6))
    (hI.const_mul 6)
  have hs2 := integral_add (h0.add (hR.const_mul 6)) (hD.const_mul 6)
  have hs1 := integral_add h0 (hR.const_mul 6)
  simp only [Pi.add_apply] at hs3 hs2 hs1
  rw [hs3, hs2, hs1, integral_const, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_indicator_const B hE] at hbound
  simp only [probReal_univ, smul_eq_mul, one_mul] at hbound
  have hr := recurrenceError_secondMoment_le_explicit c P hP a hn0 hh hhx
  have hd := deathError_secondMoment_le_explicit c P hP a hn0 hh hhx
  have he := mul_le_mul_of_nonneg_right
    (endpointRiskZero_probability_le_explicit c P hP a n hh hhcap)
    (sq_nonneg (weightEnvelope c * c.lambdaMax * Real.exp c.dMax))
  have hB : B = weightEnvelope c ^ 2 * c.lambdaMax ^ 2 * Real.exp (2 * c.dMax) := by
    dsimp [B]
    rw [mul_pow, mul_pow, pow_two (Real.exp c.dMax), ← Real.exp_add]
    rw [show c.dMax + c.dMax = 2 * c.dMax by ring]
  rw [hB] at hbound
  change (sampleLaw P n).real E * B ≤ _ * B at he
  rw [hB] at he
  let loss := ∫ s : Fin n → ObsHistory,
    (muHatAt c h a s - armMean P a) ^ 2 ∂sampleLaw P n
  change loss ≤ _ at hbound
  change loss ≤ _
  simp only [div_eq_mul_inv] at hr hd ⊢
  ring_nf at hr hd he hbound ⊢
  linarith only [hbound, hr, hd, he]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

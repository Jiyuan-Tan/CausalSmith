module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ProjectionInactivity

/-!
# Projection inactivity in the positive-retention benchmark

Roadmap (13), (31): bounded measurable hazards suffice for strict interior
arm means. The raw C/n risk bound then gives consistency by Markov's
inequality and makes both arm projections inactive with probability tending
to one. No endpoint Holder condition or influence expansion is assumed.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The lower death-hazard envelope gives an exponential upper bound on survival. -/
-- @node: positiveRetention_survival_le_exp_neg_dMin_mul
lemma positiveRetention_survival_le_exp_neg_dMin_mul (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hBounds : DeathBounds c P)
    (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    survival P a t ≤ Real.exp (-c.dMin * t) := by
  have hi : IntervalIntegrable (P.hazard a) volume 0 t :=
    (hDeath.1 a).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl ht.2)
  have hb := intervalIntegral.integral_mono_on ht.1 intervalIntegrable_const hi
    (fun u hu => (hBounds a u ⟨hu.1, hu.2.trans ht.2⟩).1)
  have hc : c.dMin * t ≤ ∫ u in (0 : ℝ)..t, P.hazard a u := by
    simpa [mul_comm] using hb
  exact Real.exp_le_exp.mpr (by change -(∫ u in (0 : ℝ)..t, P.hazard a u) ≤ _; linarith)

/-- Under the benchmark hazard bounds the target lies strictly inside the
projection range, even when the recurrence hazard is merely measurable. -/
-- @node: positiveRetention_armMean_mem_projectionInterior
lemma positiveRetention_armMean_mem_projectionInterior (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (a : Arm) : armMean P a ∈ Ioo (0 : ℝ) c.lambdaMax := by
  have hf : IntervalIntegrable (fun t => survival P a t * P.lam a t) volume 0 1 := by
    simpa [continuationWeight] using weightedTarget_intervalIntegrable c P hPoisson
      hDeath hDeathBounds a (h := 0) (by norm_num) (by norm_num) (by norm_num)
  have hlow := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) (intervalIntegrable_const (c := Real.exp (-c.dMax) * c.lambdaMin)) hf
    (fun t ht => mul_le_mul (survival_bounds_of_deathBounds c P hDeathBounds a ht).1
      (hRecurBounds a t ht).1 c.lambdaMin_pos.le (Real.exp_pos _).le)
  have hlow' : Real.exp (-c.dMax) * c.lambdaMin ≤ armMean P a := by
    simpa [armMean] using hlow
  let g : ℝ → ℝ := fun t => Real.exp (-c.dMin * t) * c.lambdaMax
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hupper := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) hf (hg.intervalIntegrable 0 1)
    (fun t ht => mul_le_mul (positiveRetention_survival_le_exp_neg_dMin_mul c P
      hDeath hDeathBounds a ht) (hRecurBounds a t ht).2
      (c.lambdaMin_pos.le.trans (hRecurBounds a t ht).1) (Real.exp_pos _).le)
  have hglt : (∫ t in (0 : ℝ)..1, g t) < c.lambdaMax := by
    have hs := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := g) (g := fun _ => c.lambdaMax) (by norm_num) hg.continuousOn
      continuousOn_const (fun t ht => ?_) (show ∃ t ∈ Icc (0 : ℝ) 1, g t < c.lambdaMax from ?_)
    · simpa using hs
    · dsimp [g]
      have he : Real.exp (-c.dMin * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg c.dMin_pos.le ht.1.le])
      simpa using mul_le_mul_of_nonneg_right he (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
    · refine ⟨1, by norm_num, ?_⟩
      have he : Real.exp (-c.dMin * 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith [c.dMin_pos])
      simpa [g] using mul_lt_mul_of_pos_right he (c.lambdaMin_pos.trans c.lambdaMin_lt)
  exact ⟨(mul_pos (Real.exp_pos _) c.lambdaMin_pos).trans_le hlow', hupper.trans_lt hglt⟩

/-- Markov's inequality bounds an absolute tail directly by its second moment. -/
-- @node: positiveRetention_probability_le_secondMoment
lemma positiveRetention_probability_le_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hi : Integrable (fun x => X x ^ 2) μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε < |X x|} ≤ (∫ x, X x ^ 2 ∂μ) / ε ^ 2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg (X x))) hi (ε ^ 2)
  have hsub : {x | ε < |X x|} ⊆ {x | ε ^ 2 ≤ X x ^ 2} := by
    intro x hx
    change ε < |X x| at hx
    change ε ^ 2 ≤ X x ^ 2
    nlinarith [sq_abs (X x)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness)) (sq_nonneg ε)).trans hm

/-- The actual raw ordinary arm estimator is consistent under the benchmark
assumptions by its derived C/n second moment. -/
-- @node: positiveRetention_ordinaryMuTilde_probability_tendsto_zero
lemma positiveRetention_ordinaryMuTilde_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |ordinaryMuTilde a s - armMean P a|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  obtain ⟨C, hC, hb⟩ := positiveRetention_ordinaryMuTilde_sqRisk_le c P hIid
    hRandom hAssignment hOverlap hPoisson hDeath hRecurDeath hCensor
    hRecurBounds hDeathBounds hHorizon
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ) / ε ^ 2) atTop (nhds 0) := by
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C).div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (positiveRetention_probability_le_secondMoment (sampleLaw P n)
    (fun s => ordinaryMuTilde a s - armMean P a) (hb n hn a).1 hε).trans
      (div_le_div_of_nonneg_right (hb n hn a).2 (sq_nonneg ε))

/-- Both ordinary arm projections are inactive with probability tending to one
under the benchmark assumptions, without smoothness or endpoint tail premises. -/
-- @node: positiveRetention_projectionActivity_probability_tendsto_zero
lemma positiveRetention_projectionActivity_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ordinaryEstimator c s ≠ ordinaryMuTilde true s - ordinaryMuTilde false s})
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let δ := fun a => min (armMean P a) (c.lambdaMax - armMean P a)
  have hm a := positiveRetention_armMean_mem_projectionInterior c P hPoisson
    hDeath hRecurBounds hDeathBounds a
  have hδ (a : Arm) : 0 < δ a := lt_min (hm a).1 (sub_pos.mpr (hm a).2)
  have hc a := positiveRetention_ordinaryMuTilde_probability_tendsto_zero c P hIid
    hRandom hAssignment hOverlap hPoisson hDeath hRecurDeath hCensor
    hRecurBounds hDeathBounds hHorizon a (half_pos (hδ a))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using (hc true).add (hc false))
  apply Eventually.of_forall
  intro n
  have hsub : {s : Fin n → ObsHistory |
      ordinaryEstimator c s ≠ ordinaryMuTilde true s - ordinaryMuTilde false s} ⊆
      {s | δ true / 2 < |ordinaryMuTilde true s - armMean P true|} ∪
      {s | δ false / 2 < |ordinaryMuTilde false s - armMean P false|} := by
    intro s hs
    by_contra hnot
    have hb := not_or.mp hnot
    have h₁ : |ordinaryMuTilde true s - armMean P true| < δ true :=
      (le_of_not_gt hb.1).trans_lt (half_lt_self (hδ true))
    have h₀ : |ordinaryMuTilde false s - armMean P false| < δ false :=
      (le_of_not_gt hb.2).trans_lt (half_lt_self (hδ false))
    apply hs
    unfold ordinaryEstimator ordinaryMuHat
    rw [projectArm_eq_self_of_abs_sub_lt_boundaryDistance c (hm true) h₁,
      projectArm_eq_self_of_abs_sub_lt_boundaryDistance c (hm false) h₀]
  exact (measureReal_mono hsub (by finiteness)).trans (measureReal_union_le _ _)

/-- Projection changes the root-n ordinary contrast by a term tending to
zero in probability, because the change vanishes whenever projection is inactive. -/
-- @node: positiveRetention_projectionDifference_rootn_probability_tendsto_zero
lemma positiveRetention_projectionDifference_rootn_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryEstimator c s -
        (ordinaryMuTilde true s - ordinaryMuTilde false s))|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (positiveRetention_projectionActivity_probability_tendsto_zero c P hIid
      hRandom hAssignment hOverlap hPoisson hDeath hRecurDeath hCensor
      hRecurBounds hDeathBounds hHorizon)
  apply Eventually.of_forall
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs heq
  change ε < |Real.sqrt n * (ordinaryEstimator c s -
    (ordinaryMuTilde true s - ordinaryMuTilde false s))| at hs
  rw [heq, sub_self, mul_zero, abs_zero] at hs
  exact (not_lt_of_ge hε.le) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

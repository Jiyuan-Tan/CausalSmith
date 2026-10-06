module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ProjectionInactivity

/-!
# Uniform interior margin for critical projection

Roadmap (25): hazard envelopes give law-independent interior margins for the
arm means. The continued estimator is consequently unaffected by projection
when its two raw arm errors are smaller than this fixed margin.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The lower hazard envelope gives an exponential upper bound on survival
at every time on the study horizon. -/
-- @node: survival_le_exp_lower_hazard
lemma survival_le_exp_lower_hazard (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    survival P a t ≤ Real.exp (-c.dMin * t) := by
  have hi : IntervalIntegrable (P.hazard a) volume 0 t :=
    (hP.deathHazard.1 a).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl ht.2)
  have hb := intervalIntegral.integral_mono_on ht.1
    (intervalIntegrable_const (c := c.dMin)) hi
    (fun u hu => (hP.deathBounds a u ⟨hu.1, hu.2.trans ht.2⟩).1)
  have hl : c.dMin * t ≤ ∫ u in (0 : ℝ)..t, P.hazard a u := by
    simpa [mul_comm] using hb
  unfold survival
  exact Real.exp_le_exp.mpr (by linarith)

/-- Arm means are bounded by fixed positive lower and strictly interior upper
envelopes. The exponential integral is the upper envelope in roadmap (25). -/
-- @node: armMean_uniform_hazard_envelopes
lemma armMean_uniform_hazard_envelopes (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    c.lambdaMin * Real.exp (-c.dMax) ≤ armMean P a ∧
    armMean P a ≤ c.lambdaMax *
      (∫ t in (0 : ℝ)..1, Real.exp (-c.dMin * t)) := by
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-c.dMin * t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  constructor
  · have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_const (c := c.lambdaMin * Real.exp (-c.dMax)))
      (hP.armMean_integrand_intervalIntegrable a) ?_
    · simpa [armMean] using hb
    intro t ht
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ht).1
    have hl := (hP.recurrenceBounds a t ht).1
    calc
      c.lambdaMin * Real.exp (-c.dMax) = Real.exp (-c.dMax) * c.lambdaMin := mul_comm _ _
      _ ≤ survival P a t * P.lam a t :=
        mul_le_mul hs hl c.lambdaMin_pos.le (Real.exp_pos _).le
  · have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hP.armMean_integrand_intervalIntegrable a) (he.const_mul c.lambdaMax) ?_
    · simpa [armMean, intervalIntegral.integral_const_mul] using hb
    intro t ht
    have hl := hP.recurrenceBounds a t ht
    calc
      survival P a t * P.lam a t ≤ Real.exp (-c.dMin * t) * c.lambdaMax :=
        mul_le_mul (survival_le_exp_lower_hazard c P hP a ht) hl.2
          (c.lambdaMin_pos.le.trans hl.1) (Real.exp_pos _).le
      _ = _ := mul_comm _ _

/-- A single positive margin works for both arms and every model law, as
needed for projection along arbitrary triangular sequences. -/
-- @node: armMean_uniform_projection_margin
lemma armMean_uniform_projection_margin (c : ClassConstants) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      δ ≤ armMean P a ∧ δ ≤ c.lambdaMax - armMean P a := by
  let E : ℝ := ∫ t in (0 : ℝ)..1, Real.exp (-c.dMin * t)
  have hE : E < 1 := by
    have hc : ContinuousOn (fun t : ℝ => Real.exp (-c.dMin * t)) (Icc 0 1) := by
      apply Continuous.continuousOn
      fun_prop
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun t : ℝ => Real.exp (-c.dMin * t)) (g := fun _ : ℝ => 1)
      (by norm_num) hc continuousOn_const
      (fun t ht => by
        apply Real.exp_le_one_iff.mpr
        simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg c.dMin_pos.le ht.1.le))
      ⟨1, by norm_num, by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos c.dMin_pos)⟩
    simpa [E] using h
  let L := c.lambdaMin * Real.exp (-c.dMax)
  let U := c.lambdaMax * (1 - E)
  have hL : 0 < L := mul_pos c.lambdaMin_pos (Real.exp_pos _)
  have hU : 0 < U := mul_pos (c.lambdaMin_pos.trans c.lambdaMin_lt) (sub_pos.mpr hE)
  refine ⟨min L U, lt_min hL hU, ?_⟩
  intro P hP a
  have hb := armMean_uniform_hazard_envelopes c P hP a
  constructor
  · exact (min_le_left L U).trans hb.1
  · apply (min_le_right L U).trans
    dsimp [U, E]
    linarith [hb.2]

/-- The continued estimator equals its raw contrast on the fixed interior
neighborhood supplied by the hazard bounds. -/
-- @node: observableEstimator_eq_rawContrast_of_uniform_close
lemma observableEstimator_eq_rawContrast_of_uniform_close (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {δ : ℝ}
    (hm : ∀ a : Arm, δ ≤ armMean P a ∧ δ ≤ c.lambdaMax - armMean P a)
    {n : ℕ} (s : Fin n → ObsHistory)
    (he : ∀ a : Arm, |muTildeAt c (bandwidth c n) a s - armMean P a| < δ) :
    observableEstimator c s =
      muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s := by
  have hp (a : Arm) : projectArm c (muTildeAt c (bandwidth c n) a s) =
      muTildeAt c (bandwidth c n) a s := by
    apply projectArm_eq_self_of_abs_sub_lt_boundaryDistance c
      (armMean_mem_projectionInterior c P hP a)
    exact (he a).trans_le (le_min (hm a).1 (hm a).2)
  simp only [observableEstimator, muHatAt, hp]

/-- Projection activity for the continued contrast requires a raw arm error
at least as large as the common interior margin. -/
-- @node: continuedProjectionActivity_subset_uniform_tails
lemma continuedProjectionActivity_subset_uniform_tails (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {δ : ℝ}
    (hm : ∀ a : Arm, δ ≤ armMean P a ∧ δ ≤ c.lambdaMax - armMean P a)
    (n : ℕ) :
    {s : Fin n → ObsHistory | observableEstimator c s ≠
      muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s} ⊆
    {s | δ ≤ |muTildeAt c (bandwidth c n) true s - armMean P true|} ∪
    {s | δ ≤ |muTildeAt c (bandwidth c n) false s - armMean P false|} := by
  intro s hs
  by_cases ht : δ ≤ |muTildeAt c (bandwidth c n) true s - armMean P true|
  · exact Or.inl ht
  by_cases hf : δ ≤ |muTildeAt c (bandwidth c n) false s - armMean P false|
  · exact Or.inr hf
  · apply False.elim
    apply hs
    apply observableEstimator_eq_rawContrast_of_uniform_close c P hP hm s
    intro a
    cases a
    · exact lt_of_not_ge hf
    · exact lt_of_not_ge ht

/-- The union bound controls continued projection activity by the two raw
arm tails at the law-independent margin, without a moment assumption. -/
-- @node: continuedProjectionActivity_probability_le_uniform_tails
lemma continuedProjectionActivity_probability_le_uniform_tails (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {δ : ℝ}
    (hm : ∀ a : Arm, δ ≤ armMean P a ∧ δ ≤ c.lambdaMax - armMean P a)
    (n : ℕ) :
    (sampleLaw P n).real {s : Fin n → ObsHistory | observableEstimator c s ≠
      muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s} ≤
    (sampleLaw P n).real
      {s | δ ≤ |muTildeAt c (bandwidth c n) true s - armMean P true|} +
    (sampleLaw P n).real
      {s | δ ≤ |muTildeAt c (bandwidth c n) false s - armMean P false|} := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  calc
    _ ≤ (sampleLaw P n).real
      ({s | δ ≤ |muTildeAt c (bandwidth c n) true s - armMean P true|} ∪
       {s | δ ≤ |muTildeAt c (bandwidth c n) false s - armMean P false|}) :=
      measureReal_mono
        (continuedProjectionActivity_subset_uniform_tails c P hP hm n) (by finiteness)
    _ ≤ _ := measureReal_union_le _ _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

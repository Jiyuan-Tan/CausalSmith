module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessSecondMoment

/-! # Transport of the death counting-process second moment -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

namespace DeathCP

/-- Every observed arm-specific death has strictly positive exit time almost
surely. -/
lemma sample_arm_death_exit_pos_ae (P : SubjectLaw) (hDeath : DeathHazard P)
    (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ i : Fin n,
      (s i).treatment = a → (s i).deathInd → 0 < (s i).exit := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [Filter.eventually_all]
  intro i
  have hEval : (sampleLaw P n).map (fun s => s i) = observedLaw P := by
    simpa [sampleLaw] using
      (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).map_eq
  have hzero : sampleLaw P n
      {s | (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = 0} = 0 := by
    have h := observed_death_exit_fixed_null P hDeath a 0
    rw [← hEval, Measure.map_apply (measurable_pi_apply i)
      ((measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
        ((measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const).inter
          (measurableSet_eq_fun measurable_obsHistory_exit measurable_const)))] at h
    exact h
  have hne : ∀ᵐ s ∂sampleLaw P n,
      (s i).treatment = a → (s i).deathInd → (s i).exit ≠ 0 :=
    ae_iff.mpr (by simpa only [Classical.not_imp, not_not] using hzero)
  filter_upwards [sample_exit_nonneg P hDeath n, hne] with s hs hne ha hd
  exact lt_of_le_of_ne (hs i) (Ne.symm (hne ha hd))

/-- The paper death error is almost surely the canonical aggregate integral
evaluated on the synthetic observed sample. -/
lemma aggregateIntegral_observedDeathSample_eq_deathError_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (fun s : Fin n → ObsHistory =>
      Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
        (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      (fun s => deathError c P a s h) := by
  filter_upwards [sample_arm_death_exit_pos_ae P hP.deathHazard a n,
    sample_death_exit_no_tie P hP.deathHazard n] with s hpos hties
  apply aggregateIntegral_observedDeathSample_eq_deathError
    c P hP a s hh hh1 hpos
  intro i j hij hai hdi haj hdj
  exact hties i j hij a hai hdi

/-- Capping at one and replacing a pair by its synthetic observed record does
not change its two counting processes when the follow-up coordinate lies in
the study horizon. -/
lemma referenceStoppedSyntheticSample_counts {n : ℕ} (x : Sample n)
    (hfirst0 : ∀ i, 0 ≤ (x i).1) (hfirst1 : ∀ i, (x i).1 ≤ 1)
    (hsecond0 : ∀ i, 0 ≤ (x i).2) (i : Fin n) (u : ℝ) :
    Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i u
        (referenceStoppedSyntheticSample x) =
      Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i u x ∧
    Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i u
        (referenceStoppedSyntheticSample x) =
      Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i u x := by
  unfold referenceStoppedSyntheticSample stoppedSyntheticDeathPair
    Causalean.Stat.RecurrentEvent.CountingProcess.censorCount
    Causalean.Stat.RecurrentEvent.CountingProcess.failureCount
  by_cases hd : (x i).2 < (x i).1
  · have hd1 : (x i).2 ≤ 1 := hd.le.trans (hfirst1 i)
    simp [hd, min_eq_left hd1, min_eq_right hd.le, hsecond0 i]
      <;> split_ifs <;> simp_all <;> linarith
  · have hfd : (x i).1 ≤ (x i).2 := le_of_not_gt hd
    have hfmin : (x i).1 ≤ min (x i).2 1 := le_min hfd (hfirst1 i)
    simp [hd, min_eq_left hfmin, hfirst0 i, hfd,
      not_lt_of_ge (hfirst1 i)]
      <;> split_ifs <;> simp_all <;> linarith

/-- The inclusive at-risk indicator is unchanged by the synthetic stopped
record throughout the unit horizon. -/
lemma referenceStoppedSyntheticSample_riskIndicator {n : ℕ} (x : Sample n)
    (hfirst0 : ∀ i, 0 ≤ (x i).1) (hfirst1 : ∀ i, (x i).1 ≤ 1)
    (hsecond0 : ∀ i, 0 ≤ (x i).2) (i : Fin n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
        (referenceStoppedSyntheticSample x) =
      Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x := by
  unfold referenceStoppedSyntheticSample stoppedSyntheticDeathPair
    Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
  by_cases hd : (x i).2 < (x i).1
  · have hd1 : (x i).2 ≤ 1 := hd.le.trans (hfirst1 i)
    simp [hd, min_eq_left hd1, min_eq_right hd.le, ht0]
      <;> split_ifs <;> simp_all <;> linarith
  · have hfd : (x i).1 ≤ (x i).2 := le_of_not_gt hd
    have hfmin : (x i).1 ≤ min (x i).2 1 := le_min hfd (hfirst1 i)
    simp [hd, min_eq_left hfmin, ht0, not_lt_of_ge (hfirst1 i)]
      <;> split_ifs <;> simp_all <;> linarith

/-- A left-predictable compensated aggregate integral through the unit horizon
is invariant under the synthetic stopped-record map. -/
lemma aggregateIntegral_referenceStoppedSyntheticSample {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (hPred : Causalean.Stat.RecurrentEvent.CountingProcess.LeftPredictable H)
    (x : Sample n) (hfirst0 : ∀ i, 0 ≤ (x i).1)
    (hfirst1 : ∀ i, (x i).1 ≤ 1) (hsecond0 : ∀ i, 0 ≤ (x i).2)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      hazard H u (referenceStoppedSyntheticSample x) =
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      hazard H u x := by
  classical
  have hH (t : ℝ) : H t (referenceStoppedSyntheticSample x) = H t x :=
    hPred t _ _ (fun i v _ =>
      referenceStoppedSyntheticSample_counts x hfirst0 hfirst1 hsecond0 i v)
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
  apply Finset.sum_congr rfl
  intro i _
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral
  have hevent :
      (if (referenceStoppedSyntheticSample x i).2 ≤ u ∧
          (referenceStoppedSyntheticSample x i).2 <
            (referenceStoppedSyntheticSample x i).1 then
        H (referenceStoppedSyntheticSample x i).2
          (referenceStoppedSyntheticSample x) else 0) =
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0 := by
    by_cases hd : (x i).2 < (x i).1
    · have hd1 : (x i).2 ≤ 1 := hd.le.trans (hfirst1 i)
      have hpair : referenceStoppedSyntheticSample x i =
          ((x i).2 + 1, (x i).2) := by
        simp [referenceStoppedSyntheticSample, stoppedSyntheticDeathPair, hd,
          min_eq_left hd1, min_eq_right hd.le]
      rw [hpair]
      simp [hd, hH]
    · have hfd : (x i).1 ≤ (x i).2 := le_of_not_gt hd
      have hfmin : (x i).1 ≤ min (x i).2 1 := le_min hfd (hfirst1 i)
      have hpair : referenceStoppedSyntheticSample x i =
          ((x i).1, (x i).1 + 1) := by
        simp [referenceStoppedSyntheticSample, stoppedSyntheticDeathPair, hd,
          min_eq_left hfmin, not_lt_of_ge (hfirst1 i)]
      rw [hpair]
      simp [hd]
  rw [hevent]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [hH]
  rw [referenceStoppedSyntheticSample_riskIndicator x hfirst0 hfirst1
    hsecond0 i ht.1 (ht.2.trans hu1)]

lemma armDeathFailureTime_le_one (a : Arm) (z : LatentSubject) :
    armDeathFailureTime a z ≤ 1 := by
  unfold armDeathFailureTime
  split_ifs
  · unfold censorHorizon
    split_ifs <;> simp
  · norm_num

/-- Reference product samples have nonnegative coordinates and follow-up at
most one almost surely. -/
lemma referenceSample_regular_ae (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a),
      (∀ i, 0 ≤ (x i).1) ∧ (∀ i, (x i).1 ≤ 1) ∧ (∀ i, 0 ≤ (x i).2) := by
  let failureLaw := armDeathFailureLaw P a
  let deathLaw := referenceDeathLaw P a
  letI : IsProbabilityMeasure failureLaw :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure deathLaw := inferInstance
  have hf0 : ∀ᵐ f ∂failureLaw, 0 ≤ f := by
    exact (mem_ae_iff_prob_eq_one measurableSet_Ici).2
      (armDeathFailureLaw_nonnegativeTimeLaw P a).2
  have hf1 : ∀ᵐ f ∂failureLaw, f ≤ 1 := by
    unfold failureLaw armDeathFailureLaw
    apply (ae_map_iff (measurable_armDeathFailureTime a).aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    exact Filter.Eventually.of_forall (armDeathFailureTime_le_one a)
  have hd0 : ∀ᵐ d ∂deathLaw, 0 ≤ d := by
    exact (mem_ae_iff_prob_eq_one measurableSet_Ici).2
      (referenceDeathLaw_hasCensorHazard hP a).1.2
  have hpair : ∀ᵐ q ∂failureLaw.prod deathLaw,
      0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_le measurable_const measurable_snd)))).2
    filter_upwards [hf0, hf1] with f hf0 hf1
    filter_upwards [hd0] with d hd0
    exact ⟨hf0, hf1, hd0⟩
  have hall : ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      failureLaw deathLaw, ∀ i, 0 ≤ (x i).1 ∧ (x i).1 ≤ 1 ∧ 0 ≤ (x i).2 := by
    rw [Filter.eventually_all]
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod deathLaw) (i := i)) hpair
  filter_upwards [hall] with x hx
  exact ⟨fun i => (hx i).1, fun i => (hx i).2.1, fun i => (hx i).2.2⟩

/-- The observed paper death error has exactly the canonical predictable
quadratic-energy second moment. -/
lemma deathError_secondMoment_eq_predictableEnergy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, (deathError c P a s h) ^ 2 ∂sampleLaw P n) =
    ∫ x : Sample n,
      Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
        (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h) x
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J : Sample n → ℝ :=
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
  have hJ : Measurable J :=
    measurable_deathCPIntegrand_aggregateIntegral c P hP a hh hh1
  have hobs := aggregateIntegral_observedDeathSample_eq_deathError_ae
    c P hP a n hh hh1
  have hreg := referenceSample_regular_ae c P hP a n
  have hobsMeas : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  calc
    _ = ∫ s : Fin n → ObsHistory, (J (observedDeathSample a s)) ^ 2
        ∂sampleLaw P n := by
      apply integral_congr_ae
      filter_upwards [hobs] with s hs
      change (deathError c P a s h) ^ 2 =
        (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
          (referenceDeathHazard P a) (deathCPIntegrand c P a h) (1 - h)
          (observedDeathSample a s)) ^ 2
      exact congrArg (fun z : ℝ => z ^ 2) hs.symm
    _ = ∫ y : Sample n, (J y) ^ 2
        ∂(sampleLaw P n).map (observedDeathSample a) := by
      symm
      exact integral_map hobsMeas.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ y : Sample n, (J y) ^ 2
        ∂μ.map referenceStoppedSyntheticSample := by
      rw [observedDeathSample_map_eq_reference P hP.deathHazard
        hP.randomAssignment hP.independentCensoring a]
    _ = ∫ x : Sample n, (J (referenceStoppedSyntheticSample x)) ^ 2 ∂μ := by
      exact integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hJ.pow_const 2).aestronglyMeasurable
    _ = ∫ x : Sample n, (J x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hreg] with x hx
      exact congrArg (fun z : ℝ => z ^ 2)
        (aggregateIntegral_referenceStoppedSyntheticSample
          (referenceDeathHazard P a) (deathCPIntegrand c P a h)
          (deathCPIntegrand_leftPredictable c P a h) x hx.1 hx.2.1 hx.2.2
          (by linarith) (by linarith))
    _ = _ := deathCPIntegrand_aggregate_isometry c P hP a hh hh1

end DeathCP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

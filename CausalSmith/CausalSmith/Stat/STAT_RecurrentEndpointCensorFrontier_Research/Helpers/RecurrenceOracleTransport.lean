module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceOracleApproximation

/-! # Full-horizon recurrence oracle replacement

Roadmap (17)--(19): transport the conditional Poisson difference energy to
observed risk-fraction energy and apply its subcritical limit. The coefficient
retains the joint dependence of KM and risk sets.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed version of the root-n recurrence coefficient difference. -/
-- @node: observedRecurrenceOracleDifferenceWeight
noncomputable def observedRecurrenceOracleDifferenceWeight (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) : ℝ :=
  Real.sqrt n * (if 0 ≤ t ∧ t ≤ 1 then recurrenceSubjectWeight c 0 a s i t else 0) -
    observedRecurrenceTimeWeight a 1 (fun u => (retention P a u)⁻¹) (s i) t /
      (P.p a * Real.sqrt n)

/-- The observed difference coefficient is jointly measurable. -/
-- @node: measurable_observedRecurrenceOracleDifferenceWeight
@[fun_prop]
lemma measurable_observedRecurrenceOracleDifferenceWeight
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) {n : ℕ} (i : Fin n) :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      observedRecurrenceOracleDifferenceWeight c P a p.1 i p.2) := by
  unfold observedRecurrenceOracleDifferenceWeight
  have hw : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      if 0 ≤ p.2 ∧ p.2 ≤ 1 then recurrenceSubjectWeight c 0 a p.1 i p.2 else 0) := by
    apply Measurable.ite ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
    · exact measurable_recurrenceSubjectWeight_joint c 0 a i
    · exact measurable_const
  exact (measurable_const.mul hw).sub
    (((measurable_observedRecurrenceTimeWeight a 1 _ (measurable_retention P a).inv).comp
      (show Measurable (fun p : (Fin n → ObsHistory) × ℝ => (p.1 i, p.2)) by
        fun_prop)).div_const _)

/-- Exposure replacement preserves the empirical and oracle coefficients together. -/
-- @node: observedRecurrenceOracleDifferenceWeight_eq_exposure
lemma observedRecurrenceOracleDifferenceWeight_eq_exposure
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) (i : Fin n) (t : ℝ) :
    observedRecurrenceOracleDifferenceWeight c P a (fun j => observe (z j)) i t =
      recurrenceOracleDifferenceWeight c P a
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t := by
  unfold observedRecurrenceOracleDifferenceWeight recurrenceOracleDifferenceWeight
    remainingRecurrenceWeight
  rw [recurrenceSubjectWeight_eq_exposureHistory]
  by_cases ha : (z i).treatment = a <;>
    simp [observedRecurrenceTimeWeight, recurrenceExposureHistory, observe, censorHorizon, ha]

/-- Summed observed subject energy cancels to the risk fraction. -/
-- @node: observedRecurrenceOracleDifferenceWeight_sum_sq
lemma observedRecurrenceOracleDifferenceWeight_sum_sq
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∑ i : Fin n, observedRecurrenceOracleDifferenceWeight c P a s i t ^ 2) =
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t *
          invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 := by
  classical
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hroot2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hw (i : Fin n) : observedRecurrenceOracleDifferenceWeight c P a s i t =
      if (s i).treatment = a ∧
          t ≤ (s i).exit then
        Real.sqrt n * deathKMLeft a s t *
          invRisk a s t -
          (retention P a t)⁻¹ / (P.p a * Real.sqrt n) else 0 := by
    simp only [observedRecurrenceOracleDifferenceWeight, 
      if_pos (show 0 ≤ t ∧ t ≤ 1 from ht), recurrenceSubjectWeight,
      observedRecurrenceTimeWeight, ht.2, and_true, continuationWeight]
    split_ifs <;> simp_all <;> ring
  simp_rw [hw, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (riskSet a s t : ℝ) * _ = _
  have hc : (Real.sqrt n * deathKMLeft a s t *
      invRisk a s t -
      (retention P a t)⁻¹ / (P.p a * Real.sqrt n)) ^ 2 =
      (((n : ℝ) * deathKMLeft a s t *
        invRisk a s t -
        1 / (P.p a * retention P a t)) / Real.sqrt n) ^ 2 := by
    congr 1
    have he : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
      apply (div_eq_iff hroot).2
      nlinarith [hroot2]
    simp only [div_eq_mul_inv] at he
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    linear_combination -(deathKMLeft a s t *
      invRisk a s t) * he
  rw [hc, div_pow, hroot2]
  ring


/-- Product-integrability allows the subject energy to be summed before
transporting from exposure histories to the observed iid law. -/
-- @node: recurrenceOracleDifferenceWeight_expected_energy_eq_observed
lemma recurrenceOracleDifferenceWeight_expected_energy_eq_observed
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
    ∫ s : Fin n → ObsHistory, (∫ t, ∑ i : Fin n,
      observedRecurrenceOracleDifferenceWeight c P a s i t ^ 2
      ∂recurrenceIntensity P a) ∂sampleLaw P n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hi := (recurrenceJointExposure_energy_conditions P a n
    (recurrenceOracleDifferenceWeight c P a)
    (measurable_recurrenceOracleDifferenceWeight c P a)
    (recurrenceOracleDifferenceWeight_energy_integrable_prod c P hP hk a hn)).1
  have hs : (∫ e, (∑ i : Fin n, ∫ t,
      recurrenceOracleDifferenceWeight c P a e i t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      ∫ e, (∫ t, ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
    apply integral_congr_ae
    filter_upwards [hi] with e he
    exact (integral_finsetSum Finset.univ (fun i _ => he i)).symm
  rw [hs]
  let F := fun e : Fin n → Arm × (ℝ × ENNReal) =>
    ∫ t, ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a
  let G := fun s : Fin n → ObsHistory =>
    ∫ t, ∑ i : Fin n, observedRecurrenceOracleDifferenceWeight c P a s i t ^ 2
      ∂recurrenceIntensity P a
  have hF : Measurable F :=
    (Finset.measurable_sum _ (fun i _ =>
      (measurable_recurrenceOracleDifferenceWeight c P a i).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hG : Measurable G :=
    (Finset.measurable_sum _ (fun i _ =>
      (measurable_observedRecurrenceOracleDifferenceWeight c P a i).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  change (∫ e, F e ∂_) = ∫ s, G s ∂_
  rw [← hmap, integral_map (show Measurable exposure by fun_prop).aemeasurable
    hF.aestronglyMeasurable, recurrence_sampleLaw_eq_latent_map,
    integral_map (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp [F, G, exposure]
  simp_rw [observedRecurrenceOracleDifferenceWeight_eq_exposure]

/-- Absolute continuity of recurrence intensity identifies conditional
Poisson error energy with the exact observed KM/oracle time energy. -/
-- @node: recurrenceOracleDifferenceWeight_expected_energy_eq_time
lemma recurrenceOracleDifferenceWeight_expected_energy_eq_time
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
    ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      P.lam a t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n := by
  rw [recurrenceOracleDifferenceWeight_expected_energy_eq_observed c P hP hk a hn]
  apply integral_congr_ae
  filter_upwards [] with s
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hP.poissonRecurrence a).1.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [(hP.poissonRecurrence a).2.1,
    ae_restrict_mem measurableSet_Ioc] with t hnonneg ht
  rw [ENNReal.toReal_ofReal hnonneg, smul_eq_mul,
    observedRecurrenceOracleDifferenceWeight_sum_sq c P a hn s ⟨ht.1.le, ht.2⟩]

/-- The full-horizon root-n difference energy vanishes by the sharp
subcritical KM coefficient limit, including the unbounded endpoint oracle. -/
-- @node: recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
lemma recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ e, (∑ i : Fin n, ∫ t,
      recurrenceOracleDifferenceWeight c P a e i t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))
      atTop (nhds 0) := by
  apply (DeathCP.observed_KM_oracle_subcritical_recurrence_time_energy_tendsto_zero
    c P hP hk a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (recurrenceOracleDifferenceWeight_expected_energy_eq_time c P hP hk a
    (by omega)).symm

/-- Conditional Poisson isometry and time-energy transport give an actual
vanishing second moment, rather than a bound for an independent surrogate. -/
-- @node: recurrenceOracleDifferenceScore_latent_secondMoment_tendsto_zero
lemma recurrenceOracleDifferenceScore_latent_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ z : Fin n → LatentSubject,
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent))
      atTop (nhds 0) := by
  apply (recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero c P hP hk a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (recurrenceOracleDifferenceScore_latent_secondMoment c P hP hk a (by omega)).2.symm

/-- Chebyshev closes the full-horizon recurrence oracle replacement under
the actual iid latent sample law in roadmap (17)--(19). -/
-- @node: recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
lemma recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  have hlim := (recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
    c P hP hk a).div_const (ε ^ 2)
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact recurrenceOracleDifferenceScore_probability_le_energy c P hP hk a (by omega) hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

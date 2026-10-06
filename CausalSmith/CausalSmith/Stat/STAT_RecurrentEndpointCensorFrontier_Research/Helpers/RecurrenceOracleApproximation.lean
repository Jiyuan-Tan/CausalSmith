module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceFullMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanRecurrenceEnergy

/-! # Conditional energy of the recurrence oracle approximation

Roadmap (17)--(19): the empirical and oracle recurrence coefficients share
exposure data, so their difference must be treated as one conditional Poisson
score. Product energy gives conditional square integrability and exact latent
moments even for the unbounded endpoint oracle. No independence between KM and
risk is asserted.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The compensated point score of an arbitrary exposure-dependent coefficient. -/
-- @node: recurrenceJointExposureScore
noncomputable def recurrenceJointExposureScore (P : SubjectLaw) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) : ℝ :=
  ∑ i : Fin n, ((∑ k : Fin (r i).1, f e i (((r i).2 k).1)) -
    ∫ t, f e i t ∂recurrenceIntensity P a)

/-- Joint coefficient measurability implies joint compensated-score measurability. -/
-- @node: measurable_recurrenceJointExposureScore
@[fun_prop]
lemma measurable_recurrenceJointExposureScore (P : SubjectLaw) (a : Arm) (n : ℕ)
    [IsFiniteMeasure (recurrenceIntensity P a)]
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2)) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      recurrenceJointExposureScore P a n f p.1 p.2) := by
  classical
  unfold recurrenceJointExposureScore
  apply Finset.measurable_sum
  intro i _
  apply Measurable.sub
  · have hw : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (ℝ × ℝ) =>
        f p.1 i p.2.1) := (hf i).comp (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (ℝ × ℝ) => (p.1, p.2.1)) by fun_prop)
    exact (measurable_recurrence_param_point_sum (fun e x => f e i x.1) hw).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · exact ((hf i).stronglyMeasurable.integral_prod_right'.measurable).comp measurable_fst

/-- Product energy supplies all analytic inputs of conditional Poisson transport
for random coefficients, including coefficients depending on the entire exposure array. -/
-- @node: recurrenceJointExposure_energy_conditions
lemma recurrenceJointExposure_energy_conditions (P : SubjectLaw) (a : Arm) (n : ℕ)
    [IsFiniteMeasure (recurrenceIntensity P a)]
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2))
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    (∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => f e i t ^ 2) (recurrenceIntensity P a)) ∧
    Integrable (fun e => ∑ i : Fin n, ∫ t, f e i t ^ 2 ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : SigmaFinite (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) :=
    IsFiniteMeasure.toSigmaFinite _
  have hi : ∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => f e i t ^ 2) (recurrenceIntensity P a) := by
    filter_upwards [hprod.prod_right_ae] with e he
    intro i
    apply he.mono'
      (((hf i).comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (f e j t)) (Finset.mem_univ i)
  refine ⟨hi, hprod.integral_prod_left.congr ?_⟩
  filter_upwards [hi] with e he
  exact integral_finsetSum Finset.univ (fun i _ => he i)

/-- The actual latent score has exact energy under integrable product exposure
energy. This is the isometry needed for the empirical-minus-oracle coefficient. -/
-- @node: recurrenceJointExposureScore_latent_secondMoment
lemma recurrenceJointExposureScore_latent_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2))
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    Integrable (fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) =
      ∫ e, (∑ i : Fin n, ∫ t, f e i t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  let : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, he⟩ := recurrenceJointExposure_energy_conditions P a n f hf hprod
  exact recurrence_latent_exposure_second_moment_of_integrable_sq P
    hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n f
    (fun e i => (hf i).comp (measurable_const.prodMk measurable_id)) hi
    (measurable_recurrenceJointExposureScore P a n f hf) he

/-- The root-n empirical-minus-oracle recurrence coefficient. The endpoint
oracle is totalized and is allowed to be unbounded near time one. -/
-- @node: recurrenceOracleDifferenceWeight
noncomputable def recurrenceOracleDifferenceWeight (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  Real.sqrt n * remainingRecurrenceWeight c a 0 e i t -
    observedRecurrenceTimeWeight a 1 (fun u => (retention P a u)⁻¹)
      (recurrenceExposureHistory (e i)) t / (P.p a * Real.sqrt n)

/-- The normalized difference coefficient is measurable jointly in exposure and time. -/
-- @node: measurable_recurrenceOracleDifferenceWeight
@[fun_prop]
lemma measurable_recurrenceOracleDifferenceWeight (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      recurrenceOracleDifferenceWeight c P a p.1 i p.2) := by
  unfold recurrenceOracleDifferenceWeight
  exact (measurable_const.mul (measurable_remainingRecurrenceWeight c a 0 i)).sub
    (((measurable_observedRecurrenceTimeWeight a 1 _ (measurable_retention P a).inv).comp
      (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
        (recurrenceExposureHistory (p.1 i), p.2)) by fun_prop)).div_const _)

/-- Actual model assumptions imply product-integrability of the normalized
difference energy. Young's inequality combines the bounded empirical score
with the integrable endpoint oracle; no approximation rate is assumed. -/
-- @node: recurrenceOracleDifferenceWeight_energy_integrable_prod
lemma recurrenceOracleDifferenceWeight_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a)) := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  let : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let Q := (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
        (recurrenceIntensity P a)
  have hemp : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, (Real.sqrt n * remainingRecurrenceWeight c a 0 p.1 i p.2) ^ 2) Q := by
    apply Integrable.of_bound (by fun_prop) ((n : ℝ) * (Real.sqrt n * weightEnvelope c) ^ 2)
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    calc
      _ ≤ ∑ i : Fin n, (Real.sqrt n * weightEnvelope c) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hb : |Real.sqrt n * remainingRecurrenceWeight c a 0 p.1 i p.2| ≤
            Real.sqrt n * weightEnvelope c := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
          exact mul_le_mul_of_nonneg_left
            (remainingRecurrenceWeight_abs_le c a 0 p.1 i p.2) (Real.sqrt_nonneg _)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by simp
  have hor := (observedRecurrence_invRetention_exposure_energy_integrable_prod
    c P hP hk a hn).const_mul ((P.p a * Real.sqrt n)⁻¹ ^ 2)
  have hbound := (hemp.const_mul 2).add (hor.const_mul 2)
  apply hbound.mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [Pi.add_apply]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  dsimp only [recurrenceOracleDifferenceWeight]
  simp only [div_eq_mul_inv, mul_pow]
  nlinarith [sq_nonneg (Real.sqrt n * remainingRecurrenceWeight c a 0 p.1 i p.2 +
    observedRecurrenceTimeWeight a 1 (fun u => (retention P a u)⁻¹)
      (recurrenceExposureHistory (p.1 i)) p.2 * (P.p a * Real.sqrt n)⁻¹)]

/-- The root-n recurrence oracle difference has its exact second moment under
the actual latent sample law, with every analytic condition derived from the model. -/
-- @node: recurrenceOracleDifferenceScore_latent_secondMoment
lemma recurrenceOracleDifferenceScore_latent_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun z : Fin n → LatentSubject =>
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject,
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) =
      ∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  exact recurrenceJointExposureScore_latent_secondMoment c P hP a n
    (recurrenceOracleDifferenceWeight c P a)
    (measurable_recurrenceOracleDifferenceWeight c P a)
    (recurrenceOracleDifferenceWeight_energy_integrable_prod c P hP hk a hn)

/-- At a study-window time, the summed normalized subject error energy is
exactly the risk-fraction energy already controlled by the subcritical KM bound. -/
-- @node: recurrenceOracleDifferenceWeight_sum_sq
lemma recurrenceOracleDifferenceWeight_sum_sq
    (c : ClassConstants) (P : SubjectLaw) (a : Arm) {n : ℕ} (hn : 0 < n)
    (e : Fin n → Arm × (ℝ × ENNReal)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∑ i : Fin n, recurrenceOracleDifferenceWeight c P a e i t ^ 2) =
      ((riskSet a (fun j => recurrenceExposureHistory (e j)) t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t *
          invRisk a (fun j => recurrenceExposureHistory (e j)) t -
          1 / (P.p a * retention P a t)) ^ 2 := by
  classical
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hroot2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hw (i : Fin n) : recurrenceOracleDifferenceWeight c P a e i t =
      if (recurrenceExposureHistory (e i)).treatment = a ∧
          t ≤ (recurrenceExposureHistory (e i)).exit then
        Real.sqrt n * deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t *
          invRisk a (fun j => recurrenceExposureHistory (e j)) t -
          (retention P a t)⁻¹ / (P.p a * Real.sqrt n) else 0 := by
    simp only [recurrenceOracleDifferenceWeight, remainingRecurrenceWeight,
      if_pos (show 0 ≤ t ∧ t ≤ 1 from ht), recurrenceSubjectWeight,
      observedRecurrenceTimeWeight, ht.2, and_true, continuationWeight]
    split_ifs <;> simp_all <;> ring
  simp_rw [hw, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (riskSet a (fun j => recurrenceExposureHistory (e j)) t : ℝ) * _ = _
  have hc : (Real.sqrt n * deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t *
      invRisk a (fun j => recurrenceExposureHistory (e j)) t -
      (retention P a t)⁻¹ / (P.p a * Real.sqrt n)) ^ 2 =
      (((n : ℝ) * deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t *
        invRisk a (fun j => recurrenceExposureHistory (e j)) t -
        1 / (P.p a * retention P a t)) / Real.sqrt n) ^ 2 := by
    congr 1
    have he : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
      apply (div_eq_iff hroot).2
      nlinarith [hroot2]
    simp only [div_eq_mul_inv] at he
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    linear_combination -(deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t *
      invRisk a (fun j => recurrenceExposureHistory (e j)) t) * he
  rw [hc, div_pow, hroot2]
  ring

/-- Chebyshev bounds the actual root-n recurrence difference by its exposure
energy. The remaining rate obligation is the expectation/time transport of
this energy, rather than a bounded-weight isometry at the endpoint. -/
-- @node: recurrenceOracleDifferenceScore_probability_le_energy
lemma recurrenceOracleDifferenceScore_probability_le_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} ≤
      (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) / ε ^ 2 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let F := fun z : Fin n → LatentSubject =>
    recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)
  obtain ⟨hi, he⟩ := recurrenceOracleDifferenceScore_latent_secondMoment c P hP hk a hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun z => sq_nonneg (F z))) hi (ε ^ 2)
  have hsub : {z | ε < |F z|} ⊆ {z | ε ^ 2 ≤ F z ^ 2} := by
    intro z hz
    change ε < |F z| at hz
    change ε ^ 2 ≤ F z ^ 2
    nlinarith [sq_abs (F z)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [← he]
  simpa only [mul_comm, F] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
      (sq_nonneg ε)).trans hm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

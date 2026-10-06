module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSubcriticalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UnboundedRecurrenceTransport

/-!
# Recurrence energy for remaining means

Roadmap (35)--(36): insert a deterministic lower endpoint into the actual
exposure-dependent recurrence coefficient. Conditional Poisson energy survives
this restriction and is dominated by the ordinary full-window energy. All KM
and risk-set dependence remains inside the exposure average.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The remaining-mean recurrence coefficient, with both endpoint cutoffs. -/
-- @node: remainingRecurrenceWeight
noncomputable def remainingRecurrenceWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (u : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  if u ≤ t ∧ t ≤ 1 then
    recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t else 0

/-- The tail coefficient is jointly measurable in exposures and time. -/
-- @node: measurable_remainingRecurrenceWeight
@[fun_prop]
lemma measurable_remainingRecurrenceWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (u : ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      remainingRecurrenceWeight c a u p.1 i p.2) := by
  unfold remainingRecurrenceWeight
  apply Measurable.ite ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const))
  · exact (measurable_recurrenceSubjectWeight_joint c 0 a i).comp
      (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
        ((fun j => recurrenceExposureHistory (p.1 j)), p.2)) by fun_prop)
  · exact measurable_const

/-- Restriction to a remaining interval preserves the continuation envelope. -/
-- @node: remainingRecurrenceWeight_abs_le
lemma remainingRecurrenceWeight_abs_le (c : ClassConstants) (a : Arm)
    {n : ℕ} (u : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    |remainingRecurrenceWeight c a u e i t| ≤ weightEnvelope c := by
  unfold remainingRecurrenceWeight
  split_ifs
  · exact recurrenceSubjectWeight_abs_le_of_nonneg c (by norm_num) a _ i t
  · simp only [abs_zero]
    unfold weightEnvelope continuationNorm
    positivity

/-- The compensated canonical recurrence tail on a fixed exposure array. -/
-- @node: remainingRecurrenceExposureScore
noncomputable def remainingRecurrenceExposureScore (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) (n : ℕ) (u : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) : ℝ :=
  ∑ i : Fin n, ((∑ k : Fin (r i).1,
    remainingRecurrenceWeight c a u e i (((r i).2 k).1)) -
    ∫ t, remainingRecurrenceWeight c a u e i t ∂recurrenceIntensity P a)

/-- The tail score has exactly its conditional Poisson energy. -/
-- @node: remainingRecurrenceExposureScore_conditional_secondMoment
lemma remainingRecurrenceExposureScore_conditional_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (u : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) :
    Integrable (fun r => remainingRecurrenceExposureScore c P a n u e r ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf (recurrenceIntensity P a))) ∧
    (∫ r, remainingRecurrenceExposureScore c P a n u e r ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf (recurrenceIntensity P a))) =
      ∑ i : Fin n, ∫ t, remainingRecurrenceWeight c a u e i t ^ 2
        ∂recurrenceIntensity P a := by
  exact recurrence_canonical_iid_second_moment (recurrenceIntensity P a) n
    (remainingRecurrenceWeight c a u e)
    (fun i => (measurable_remainingRecurrenceWeight c a u i).comp
      (measurable_const.prodMk measurable_id))
    (remainingRecurrenceWeight_abs_le c a u e)

/-- Tail conditional energy is bounded by full-window conditional energy. -/
-- @node: remainingRecurrenceWeight_energy_le_full
lemma remainingRecurrenceWeight_energy_le_full
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (u : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) :
    (∑ i : Fin n, ∫ t, remainingRecurrenceWeight c a u e i t ^ 2
      ∂recurrenceIntensity P a) ≤
    ∑ i : Fin n, ∫ t in (0 : ℝ)..1,
      recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
        P.lam a t := by
  apply Finset.sum_le_sum
  intro i _
  let f := fun t => if t ≤ (1 : ℝ) then
    recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 else 0
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · exact (measurable_recurrenceSubjectWeight c 0 a _ i).pow_const 2
    · exact measurable_const
  have hbound : ∀ t, |f t| ≤ weightEnvelope c ^ 2 := by
    intro t
    dsimp [f]
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (recurrenceSubjectWeight_abs_le_of_nonneg c (by norm_num) a _ i t) 2
    · simpa using sq_nonneg (weightEnvelope c)
  have hi : Integrable f (recurrenceIntensity P a) :=
    Integrable.of_bound hf.aestronglyMeasurable _
      (Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound t))
  have hle : (∫ t, remainingRecurrenceWeight c a u e i t ^ 2
      ∂recurrenceIntensity P a) ≤ ∫ t, f t ∂recurrenceIntensity P a := by
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _)) hi
    filter_upwards [] with t
    unfold remainingRecurrenceWeight f
    by_cases ht : t ≤ 1
    · by_cases hu : u ≤ t
      · simp [ht, hu]
      · simpa [ht, hu] using sq_nonneg
          (recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t)
    · simp [ht]
  exact hle.trans_eq (recurrenceIntensity_integral_truncated P hP.poissonRecurrence a
    (fun t => recurrenceSubjectWeight c 0 a
      (fun j => recurrenceExposureHistory (e j)) i t ^ 2) (by norm_num) le_rfl)

/-- The compensated tail score is measurable jointly in exposure and points. -/
-- @node: measurable_remainingRecurrenceExposureScore
@[fun_prop]
lemma measurable_remainingRecurrenceExposureScore
    (c : ClassConstants) (P : SubjectLaw) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (u : ℝ) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      remainingRecurrenceExposureScore c P a n u p.1 p.2) := by
  classical
  unfold remainingRecurrenceExposureScore
  apply Finset.measurable_sum
  intro i _
  apply Measurable.sub
  · have hw : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (ℝ × ℝ) =>
        remainingRecurrenceWeight c a u p.1 i p.2.1) :=
      (measurable_remainingRecurrenceWeight c a u i).comp
        (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (ℝ × ℝ) =>
          (p.1, p.2.1)) by fun_prop)
    exact (measurable_recurrence_param_point_sum
      (fun e x => remainingRecurrenceWeight c a u e i x.1) hw).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · exact ((measurable_remainingRecurrenceWeight c a u i).stronglyMeasurable.integral_prod_right'.measurable).comp measurable_fst

/-- The restricted energy is integrable over exposures by domination by the
bounded full-window subject energy. -/
-- @node: remainingRecurrenceWeight_energy_integrable
lemma remainingRecurrenceWeight_energy_integrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (u : ℝ)
    (Q : Measure (Fin n → Arm × (ℝ × ENNReal))) [IsFiniteMeasure Q] :
    Integrable (fun e => ∑ i : Fin n, ∫ t, remainingRecurrenceWeight c a u e i t ^ 2
      ∂recurrenceIntensity P a) Q := by
  have hm : Measurable (fun e => ∑ i : Fin n, ∫ t,
      remainingRecurrenceWeight c a u e i t ^ 2 ∂recurrenceIntensity P a) :=
    Finset.measurable_sum _ (fun i _ =>
      ((measurable_remainingRecurrenceWeight c a u i).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (n * (weightEnvelope c ^ 2 * c.lambdaMax))
  filter_upwards [] with e
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _)))]
  exact (remainingRecurrenceWeight_energy_le_full c P hP a n u e).trans
    ((le_abs_self _).trans (by simpa only [sub_zero] using
      (recurrence_integrated_energy_abs_le_of_nonneg c P hP a
        (fun j => recurrenceExposureHistory (e j)) (h := 0) (by norm_num) (by norm_num))))

/-- The actual latent iid recurrence tail has no greater second moment than
the actual ordinary recurrence error. The exposure product law, rather than
independence of estimated coefficients, justifies this comparison. -/
-- @node: remainingRecurrenceExposureScore_latent_secondMoment_le
lemma remainingRecurrenceExposureScore_latent_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) (u : ℝ) :
    Integrable (fun z : Fin n → LatentSubject =>
      remainingRecurrenceExposureScore c P a n u
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, remainingRecurrenceExposureScore c P a n u
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      ∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E := P.latent.map (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))
  letI : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  have hi (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) :
      Integrable (fun t => remainingRecurrenceWeight c a u e i t ^ 2)
        (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      (((measurable_remainingRecurrenceWeight c a u i).comp
        (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
      (weightEnvelope c ^ 2)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, Function.comp_apply, id_eq] using pow_le_pow_left₀ (abs_nonneg _)
      (remainingRecurrenceWeight_abs_le c a u e i t) 2
  have he := remainingRecurrenceWeight_energy_integrable c P hP a n u
    (Measure.pi (fun _ : Fin n => E))
  have ht := recurrence_latent_exposure_second_moment_of_integrable_sq P
    hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n (remainingRecurrenceWeight c a u)
    (fun e i => (measurable_remainingRecurrenceWeight c a u i).comp
      (measurable_const.prodMk measurable_id))
    (Eventually.of_forall hi)
    (measurable_remainingRecurrenceExposureScore c P a n u) he
  refine ⟨ht.1, ?_⟩
  rw [show (∫ z : Fin n → LatentSubject, remainingRecurrenceExposureScore c P a n u
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) = _ from ht.2]
  rw [(recurrenceError_secondMoment_eq_exposure_energy_of_nonneg c P hP a n
    (h := 0) (by norm_num) (by norm_num)).2]
  have hfull : Integrable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      ∑ i : Fin n, ∫ t in (0 : ℝ)..1,
        recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t) (Measure.pi (fun _ : Fin n => E)) := by
    have hmfull : Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
        ∑ i : Fin n, ∫ t in (0 : ℝ)..1,
          recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
            P.lam a t) := by
      apply Finset.measurable_sum
      intro i _
      have hm := (measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i
        (h := 0) (by norm_num) (by norm_num) 2).comp
        (show Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
          fun j => recurrenceExposureHistory (e j)) by fun_prop)
      simpa only [sub_zero, Function.comp_def] using hm
    apply Integrable.of_bound hmfull.aestronglyMeasurable
      (n * (weightEnvelope c ^ 2 * c.lambdaMax))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    simpa only [sub_zero] using recurrence_integrated_energy_abs_le_of_nonneg
      c P hP a (fun j => recurrenceExposureHistory (e j)) (h := 0) (by norm_num) (by norm_num)
  simpa only [sub_zero] using integral_mono he hfull
    (remainingRecurrenceWeight_energy_le_full c P hP a n u)

/-- Subcritical retention gives an explicit inverse-sample-size bound for
any fixed lower endpoint of the actual compensated recurrence tail. -/
-- @node: subcritical_remainingRecurrenceExposureScore_secondMoment_le
lemma subcritical_remainingRecurrenceExposureScore_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    (∫ z : Fin n → LatentSubject, remainingRecurrenceExposureScore c P a n u
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
    (2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
      (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)) / n := by
  exact (remainingRecurrenceExposureScore_latent_secondMoment_le c P hP a n u).2.trans
    (subcritical_recurrenceError_zero_secondMoment_le c P hP hk a hn)

/-- Chebyshev and the derived subcritical energy bound make every fixed
remaining-interval recurrence score vanish in probability under the latent iid
law. No stochastic convergence hypothesis is supplied to this result. -/
-- @node: subcritical_remainingRecurrenceExposureScore_probability_tendsto_zero
lemma subcritical_remainingRecurrenceExposureScore_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real
      {z | ε < |remainingRecurrenceExposureScore c P a n u
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let C := 2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
    (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)
  have hlim : Tendsto (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) atTop (nhds 0) := by
    simp only [div_mul_eq_div_div]
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C).div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  let F := fun z : Fin n → LatentSubject => remainingRecurrenceExposureScore c P a n u
    (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
    (fun j => (z j).recur a)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun z => sq_nonneg (F z)))
    (remainingRecurrenceExposureScore_latent_secondMoment_le c P hP a n u).1 (ε ^ 2)
  have hsub : {z | ε < |F z|} ⊆ {z | ε ^ 2 ≤ F z ^ 2} := by
    intro z hz
    change ε < |F z| at hz
    change ε ^ 2 ≤ F z ^ 2
    nlinarith [sq_abs (F z)]
  have hb := ((mul_le_mul_of_nonneg_left
    (measureReal_mono hsub (by finiteness)) (sq_nonneg ε)).trans hm).trans
    (subcritical_remainingRecurrenceExposureScore_secondMoment_le c P hP hk a
      (by omega : 0 < n) u)
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm, F, C] using hb

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

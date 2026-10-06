module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSecondMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UnboundedRecurrenceTransport

/-!
# Observed deterministic recurrence scores

Roadmap (2), (6), and (24): stable stopping identifies the observed recurrence
score with its latent compensated Poisson score. Conditional energy is averaged
before transport to the observed sample; exposure and the score are not factored.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The deterministic time weight, including assignment, observed exposure,
and the localization horizon. -/
-- @node: observedRecurrenceTimeWeight
noncomputable def observedRecurrenceTimeWeight (a : Arm) (T : ℝ) (w : ℝ → ℝ)
    (o : ObsHistory) (t : ℝ) : ℝ :=
  if o.treatment = a ∧ t ≤ o.exit ∧ t ≤ T then w t else 0

/-- The observed finite recurrence point sum minus its stopped intensity
compensator. The inverse-retention oracle is obtained by choosing its time weight. -/
-- @node: observedRecurrenceScore
noncomputable def observedRecurrenceScore (P : SubjectLaw) (a : Arm) (n : ℕ)
    (T : ℝ) (w : ℝ → ℝ) (s : Fin n → ObsHistory) : ℝ :=
  ∑ i : Fin n,
    ((if (s i).treatment = a then
      (((s i).recur.times.filter (fun t => t ≤ T)).map w).sum else 0) -
      ∫ t, observedRecurrenceTimeWeight a T w (s i) t ∂recurrenceIntensity P a)

/-- The exposure cutoff is measurable jointly with time. -/
@[fun_prop]
-- @node: measurable_observedRecurrenceTimeWeight
lemma measurable_observedRecurrenceTimeWeight (a : Arm) (T : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) :
    Measurable (fun p : ObsHistory × ℝ => observedRecurrenceTimeWeight a T w p.1 p.2) := by
  unfold observedRecurrenceTimeWeight
  apply Measurable.ite
  · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      ((measurableSet_le measurable_snd (by fun_prop)).inter
        (measurableSet_le measurable_snd measurable_const))
  · exact hw.comp measurable_snd
  · exact measurable_const

/-- An observed deterministic score is measurable, without imposing smoothness
of the intensity outside its study window. -/
@[fun_prop]
-- @node: measurable_observedRecurrenceScore
lemma measurable_observedRecurrenceScore (P : SubjectLaw) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (T : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) : Measurable (observedRecurrenceScore P a n T w) := by
  have hpoint : Measurable (fun r : RecurConfig =>
      ((r.times.filter (fun t => t ≤ T)).map w).sum) := by
    have hf : Measurable (fun p : Unit × (ℝ × ℝ) =>
        if p.2.1 ≤ T then w p.2.1 else 0) :=
      ((hw.comp (by fun_prop)).ite
        (measurableSet_le (by fun_prop) measurable_const) measurable_const)
    have hm := measurable_recurrence_param_point_sum
      (fun (_ : Unit) x => if x.1 ≤ T then w x.1 else 0) hf
    simpa only [recurrence_times_filtered_sum, Function.comp_def, id_eq] using
      hm.comp ((measurable_const (a := ())).prodMk measurable_id)
  have hint : Measurable (fun o =>
      ∫ t, observedRecurrenceTimeWeight a T w o t ∂recurrenceIntensity P a) :=
    (measurable_observedRecurrenceTimeWeight a T w hw).stronglyMeasurable.integral_prod_right.measurable
  unfold observedRecurrenceScore
  apply Finset.measurable_sum
  intro i _
  apply Measurable.sub
  · exact (hpoint.comp (by fun_prop)).ite
      (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const
  · exact hint.comp (measurable_pi_apply i)

/-- Stable stopping realizes the observed score as a compensated latent
configuration score. This identity is pointwise, so no martingale gate is assumed. -/
-- @node: observedRecurrenceScore_eq_latent
lemma observedRecurrenceScore_eq_latent (P : SubjectLaw) (a : Arm) (n : ℕ)
    (T : ℝ) (w : ℝ → ℝ) (z : Fin n → LatentSubject) :
    observedRecurrenceScore P a n T w (fun i => observe (z i)) =
      ∑ i : Fin n,
        ((∑ k : Fin ((z i).recur a).1,
          observedRecurrenceTimeWeight a T w
            (recurrenceExposureHistory ((z i).treatment, ((z i).death a, (z i).censor a)))
            ((((z i).recur a).2 k).1)) -
          ∫ t, observedRecurrenceTimeWeight a T w
            (recurrenceExposureHistory ((z i).treatment, ((z i).death a, (z i).censor a))) t
            ∂recurrenceIntensity P a) := by
  classical
  unfold observedRecurrenceScore
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (z i).treatment = a
  · simp only [observe, ha, ↓reduceIte]
    rw [recurrence_stopped_weighted_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      simp [observedRecurrenceTimeWeight, recurrenceExposureHistory, censorHorizon, ha]
  · simp [observe, observedRecurrenceTimeWeight, recurrenceExposureHistory, ha]

/-- Joint measurability of the concrete exposure/configuration score follows
from the parameterized finite point-sum API and measurability of the compensator. -/
-- @node: measurable_observedRecurrenceExposureScore
lemma measurable_observedRecurrenceExposureScore (P : SubjectLaw) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (T : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      ∑ i : Fin n,
        ((∑ k : Fin (p.2 i).1, observedRecurrenceTimeWeight a T w
          (recurrenceExposureHistory (p.1 i)) (((p.2 i).2 k).1)) -
        ∫ t, observedRecurrenceTimeWeight a T w
          (recurrenceExposureHistory (p.1 i)) t ∂recurrenceIntensity P a)) := by
  have hf (i : Fin n) : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (p.1 i)) p.2) := by
    fun_prop
  apply Finset.measurable_sum
  intro i _
  apply Measurable.sub
  · have hm := measurable_recurrence_param_point_sum
      (fun e : Fin n → Arm × (ℝ × ENNReal) => fun x : ℝ × ℝ =>
        observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) x.1)
      ((hf i).comp (measurable_fst.prodMk (by fun_prop)))
    exact hm.comp (measurable_fst.prodMk (by fun_prop))
  · exact (show Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      ∫ t, observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t
        ∂recurrenceIntensity P a) from
      (hf i).stronglyMeasurable.integral_prod_right.measurable).comp measurable_fst

/-- Conditional square-integrability and integrable averaged energy transport
to the actual observed score. These are analytic hypotheses of the general
identity, not assumptions on a frozen paper theorem. -/
-- @node: observedRecurrenceScore_second_moment_of_integrable_energy
lemma observedRecurrenceScore_second_moment_of_integrable_energy
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (T : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w)
    (hi : ∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) (recurrenceIntensity P a))
    (he : Integrable (fun e => ∑ i : Fin n, ∫ t,
        observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (fun s => observedRecurrenceScore P a n T w s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  let f := fun (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) => observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t
  have hf (e) (i : Fin n) : Measurable (f e i) := by
    exact (measurable_observedRecurrenceTimeWeight a T w hw).comp
      (measurable_const.prodMk measurable_id)
  have hm := recurrence_latent_exposure_second_moment_of_integrable_sq
    P hRandom hRD hC hPoisson a n f hf hi
    (measurable_observedRecurrenceExposureScore P a n T w hw) he
  have hs := (measurable_observedRecurrenceScore P a n T w hw).pow_const 2
  have ho : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have hlatent : (fun z : Fin n → LatentSubject =>
      observedRecurrenceScore P a n T w (fun i => observe (z i)) ^ 2) =
      fun z => (∑ i : Fin n,
        ((∑ k : Fin ((z i).recur a).1,
          f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
            ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a)) ^ 2 := by
    funext z
    rw [observedRecurrenceScore_eq_latent]
  constructor
  · rw [recurrence_sampleLaw_eq_latent_map]
    apply (integrable_map_measure hs.aestronglyMeasurable ho.aemeasurable).2
    simpa only [Function.comp_def, hlatent] using hm.1
  · rw [recurrence_sampleLaw_eq_latent_map, integral_map ho.aemeasurable hs.aestronglyMeasurable]
    rw [hlatent]
    exact hm.2

/-- Finite averaged conditional energy also transports exact centering to the
observed score. -/
-- @node: observedRecurrenceScore_mean_zero_of_integrable_energy
lemma observedRecurrenceScore_mean_zero_of_integrable_energy
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ) (T : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w)
    (hi : ∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) (recurrenceIntensity P a))
    (he : Integrable (fun e => ∑ i : Fin n, ∫ t,
        observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (observedRecurrenceScore P a n T w) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ∂sampleLaw P n) = 0 := by
  let f := fun (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) =>
    observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t
  have hf (e) (i : Fin n) : Measurable (f e i) :=
    (measurable_observedRecurrenceTimeWeight a T w hw).comp
      (measurable_const.prodMk measurable_id)
  have hm := recurrence_latent_exposure_mean_zero_of_integrable_sq
    P hRandom hRD hC hPoisson a n f hf hi
    (measurable_observedRecurrenceExposureScore P a n T w hw) he
  have hs := measurable_observedRecurrenceScore P a n T w hw
  have ho : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  constructor
  · rw [recurrence_sampleLaw_eq_latent_map]
    apply (integrable_map_measure hs.aestronglyMeasurable ho.aemeasurable).2
    simpa only [Function.comp_def, observedRecurrenceScore_eq_latent, f] using hm.1
  · rw [recurrence_sampleLaw_eq_latent_map, integral_map ho.aemeasurable hs.aestronglyMeasurable]
    simpa only [observedRecurrenceScore_eq_latent, f] using hm.2

/-- A bound on the deterministic weight only up to the localization horizon
bounds every exposed time score. -/
-- @node: observedRecurrenceTimeWeight_abs_le
lemma observedRecurrenceTimeWeight_abs_le (a : Arm) (T : ℝ) (w : ℝ → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K)
    (o : ObsHistory) (t : ℝ) : |observedRecurrenceTimeWeight a T w o t| ≤ K := by
  unfold observedRecurrenceTimeWeight
  split_ifs with ht
  · exact hb t ht.2.2
  · simpa using hK

/-- Bounded localization discharges both conditional square-integrability and
integrability of the averaged energy, rather than leaving them as score gates. -/
-- @node: observedRecurrenceScore_energy_integrable_of_bound
lemma observedRecurrenceScore_energy_integrable_of_bound
    (P : SubjectLaw) (a : Arm) [IsFiniteMeasure (recurrenceIntensity P a)]
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    (∀ e : Fin n → Arm × (ℝ × ENNReal), ∀ i,
      Integrable (fun t => observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) (recurrenceIntensity P a)) ∧
    Integrable (fun e => ∑ i : Fin n, ∫ t,
        observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hf (i : Fin n) : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (p.1 i)) p.2 ^ 2) := by
    fun_prop
  have hbound (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
      ‖observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t ^ 2‖ ≤ K ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2
      (observedRecurrenceTimeWeight_abs_le a T w hK hb _ t)
  constructor
  · intro e i
    apply Integrable.of_bound
      (((hf i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) (K ^ 2)
    exact Filter.Eventually.of_forall (hbound e i)
  · apply Integrable.of_bound
      (Finset.measurable_sum _ (fun i _ =>
        (hf i).stronglyMeasurable.integral_prod_right.measurable)).aestronglyMeasurable
      ((n : ℝ) * (K ^ 2 * (recurrenceIntensity P a).real univ))
    apply Filter.Eventually.of_forall
    intro e
    calc
      _ ≤ ∑ i : Fin n, ‖∫ t, observedRecurrenceTimeWeight a T w
          (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, K ^ 2 * (recurrenceIntensity P a).real univ :=
        Finset.sum_le_sum (fun i _ => norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall (hbound e i)))
      _ = _ := by simp

/-- The actual observed localized score is centered and has exact conditional
Poisson energy, with every analytic condition derived from localization. -/
-- @node: observedRecurrenceScore_moments_of_bound
lemma observedRecurrenceScore_moments_of_bound
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    Integrable (observedRecurrenceScore P a n T w) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => observedRecurrenceScore P a n T w s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, he⟩ := observedRecurrenceScore_energy_integrable_of_bound P a n T w hw hK hb
  obtain ⟨hm1, hm0⟩ := observedRecurrenceScore_mean_zero_of_integrable_energy
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n T w hw (Filter.Eventually.of_forall hi) he
  obtain ⟨hm2, he2⟩ := observedRecurrenceScore_second_moment_of_integrable_energy
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n T w hw (Filter.Eventually.of_forall hi) he
  exact ⟨hm1, hm0, hm2, he2⟩

/-- The inverse-retention oracle stopped before time one satisfies the observed
moment identity. Positivity and antitonicity of retention supply the bound;
there is no inverse-weight moment assumption. -/
-- @node: observedRecurrenceScore_invRetention_localized_moments
lemma observedRecurrenceScore_invRetention_localized_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Integrable (observedRecurrenceScore P a n T (fun t => (retention P a t)⁻¹))
      (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T (fun t => (retention P a t)⁻¹) s
      ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => observedRecurrenceScore P a n T
      (fun t => (retention P a t)⁻¹) s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T (fun t => (retention P a t)⁻¹) s ^ 2
      ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T
        (fun t => (retention P a t)⁻¹) (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  have hg : 0 < retention P a T := retention_pos_of_modelClass c P hP a T hT0 hT1
  apply observedRecurrenceScore_moments_of_bound c P hP a n T _
    (measurable_retention P a).inv (inv_nonneg.mpr hg.le)
  intro t ht
  change |(retention P a t)⁻¹| ≤ (retention P a T)⁻¹
  rw [abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ retention P a t from measureReal_nonneg))]
  exact (inv_le_inv₀ (hg.trans_le (retention_antitone P a ht)) hg).2
    (retention_antitone P a ht)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceOracleTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanIdentification

/-! # Observed recurrence oracle replacement

Roadmap (17)--(19) and (23): linearity of the joint conditional Poisson score
identifies the observed compensated full-window tail with its oracle. The
unbounded endpoint compensator is integrable almost surely by product energy.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Joint compensated scores preserve linear combinations when the two
conditional intensity integrals exist. -/
-- @node: recurrenceJointExposureScore_linear_combination
lemma recurrenceJointExposureScore_linear_combination (P : SubjectLaw) (a : Arm)
    (n : ℕ) (f g : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) (b d : ℝ)
    (hf : ∀ i, Integrable (f e i) (recurrenceIntensity P a))
    (hg : ∀ i, Integrable (g e i) (recurrenceIntensity P a)) :
    recurrenceJointExposureScore P a n (fun e i t => b * f e i t - d * g e i t) e r =
      b * recurrenceJointExposureScore P a n f e r -
        d * recurrenceJointExposureScore P a n g e r := by
  unfold recurrenceJointExposureScore
  simp_rw [integral_sub ((hf _).const_mul b) ((hg _).const_mul d),
    integral_const_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The full-window oracle coefficient is conditionally integrable under
the actual latent iid law, despite its unbounded endpoint weight. -/
-- @node: recurrence_invRetention_coefficient_latent_ae_integrable
lemma recurrence_invRetention_coefficient_latent_ae_integrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent), ∀ i : Fin n,
      Integrable (fun t => observedRecurrenceTimeWeight a 1
        (fun u => (retention P a u)⁻¹)
        (recurrenceExposureHistory ((z i).treatment, ((z i).death a, (z i).censor a))) t)
        (recurrenceIntensity P a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hi := (observedRecurrenceScore_energy_conditions_of_integrable_prod P a n 1
    (fun t => (retention P a t)⁻¹) (measurable_retention P a).inv
    (observedRecurrence_invRetention_exposure_energy_integrable_prod c P hP hk a hn)).1
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  rw [← hmap] at hi
  have hz := ae_of_ae_map (show Measurable exposure by fun_prop).aemeasurable hi
  filter_upwards [hz] with z hz
  intro i
  have hm := (measurable_observedRecurrenceTimeWeight a 1 _
    (measurable_retention P a).inv).comp
      ((measurable_const (a := recurrenceExposureHistory (exposure z i))).prodMk measurable_id)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 (hz i)).integrable
    (by norm_num)

/-- The normalized observed compensated tail difference is exactly the
latent joint difference score, almost surely. -/
-- @node: remainingMeanRaw_oracle_difference_eq_latent_score_ae
lemma remainingMeanRaw_oracle_difference_eq_latent_score_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      Real.sqrt n * (remainingMeanRaw a (fun j => observe (z j)) 0 -
        remainingMeanDrift P a (fun j => observe (z j)) 0) -
      observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
        (fun j => observe (z j)) / (P.p a * Real.sqrt n) =
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  filter_upwards [recurrence_invRetention_coefficient_latent_ae_integrable c P hP hk a hn]
    with z hz
  rw [remainingMeanRaw_sub_drift_eq_latent_score c P hP a z (by constructor <;> norm_num),
    observedRecurrenceScore_eq_latent]
  symm
  have hemp (i : Fin n) : Integrable
      (remainingRecurrenceWeight c a 0
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound (by fun_prop) (weightEnvelope c)
    filter_upwards [] with t
    exact remainingRecurrenceWeight_abs_le c a 0 _ i t
  simpa only [recurrenceOracleDifferenceWeight, div_eq_mul_inv, mul_comm,
    remainingRecurrenceExposureScore, recurrenceJointExposureScore] using
    recurrenceJointExposureScore_linear_combination P a n
    (remainingRecurrenceWeight c a 0)
    (fun e i t => observedRecurrenceTimeWeight a 1 (fun u => (retention P a u)⁻¹)
      (recurrenceExposureHistory (e i)) t)
    _ (fun j => (z j).recur a) (Real.sqrt n) ((P.p a * Real.sqrt n)⁻¹) hemp hz

/-- The actual observed compensated full-window tail has a negligible
root-n oracle replacement error, with no endpoint boundedness premise. -/
-- @node: remainingMeanRaw_oracle_difference_probability_tendsto_zero
lemma remainingMeanRaw_oracle_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (remainingMeanRaw a s 0 - remainingMeanDrift P a s 0) -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
          (P.p a * Real.sqrt n)|}) atTop (nhds 0) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  apply (recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
    c P hP hk a hε).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      Real.sqrt n * (remainingMeanRaw a s 0 - remainingMeanDrift P a s 0) -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
          (P.p a * Real.sqrt n)) := by
    have hraw := (measurable_remainingMeanRaw_joint a (n := n)).comp
      (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    have hdrift := measurable_remainingMeanDrift P hP.poissonRecurrence a
      (n := n) (u := 0) (by constructor <;> norm_num)
    have hor := measurable_observedRecurrenceScore P a n 1 _ (measurable_retention P a).inv
    exact (measurable_const.mul (hraw.sub hdrift)).sub (hor.div_const _)
  rw [recurrence_sampleLaw_eq_latent_map]
  simp only [measureReal_def]
  rw [Measure.map_apply
    (show Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) by fun_prop)
    (measurableSet_lt measurable_const hm.abs)]
  congr 1
  apply measure_congr
  filter_upwards [remainingMeanRaw_oracle_difference_eq_latent_score_ae c P hP hk a
    (by omega : 0 < n)] with z hz
  apply propext
  change (ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)|) ↔ _
  rw [← hz]
  rfl

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

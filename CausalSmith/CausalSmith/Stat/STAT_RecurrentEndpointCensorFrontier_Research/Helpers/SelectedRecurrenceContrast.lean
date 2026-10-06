module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SelectedArmRecurrenceLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceCanonicalCharFun

/-!
# Selected-arm compensated recurrence scores

The observed contrast depends only on each subject's assigned exposure and
assigned recurrence configuration. Transport its characteristic function to
the iid selected-arm mixture, without factoring marginal arm scores.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- With fixed assignments, subjects use their own finite recurrence intensity.
The characteristic function factors across subjects, not across potential arms. -/
-- @node: recurrence_canonical_independent_charFun
lemma recurrence_canonical_independent_charFun (n : ℕ)
    (ν : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {K : ℝ} (hK : ∀ i t, |f i t| ≤ K) (u : ℝ) :
    (∫ r : Fin n → RecurConfig, Complex.exp (Complex.I *
      (u * ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν i) : ℝ))
      ∂Measure.pi (fun i : Fin n => canonicalRecurrenceLawOf (ν i))) =
      Complex.exp (∑ i : Fin n, ∫ t,
        (Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
          Complex.I * (u * f i t : ℝ)) ∂ν i) := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (canonicalRecurrenceLawOf (ν i)) := by
    unfold canonicalRecurrenceLawOf
    infer_instance
  open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition in
  have hone (i : Fin n) :
      (∫ r : RecurConfig, Complex.exp (Complex.I *
        (u * ((∑ k : Fin r.1, f i ((r.2 k).1)) - ∫ t, f i t ∂ν i) : ℝ))
        ∂canonicalRecurrenceLawOf (ν i)) =
      Complex.exp (∫ t, (Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ)) ∂ν i) := by
    have hi : Integrable (fun x : ℝ × ℝ => f i x.1)
        ((normalizedFiniteMeasure (ν i) (Measure.dirac 0)).prod (Measure.dirac 0)) := by
      apply Integrable.of_bound ((hf i).comp measurable_fst).aestronglyMeasurable K
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using hK i x.1)
    have hc := recurrence_poisson_compensated_charFun
      ((normalizedFiniteMeasure (ν i) (Measure.dirac 0)).prod (Measure.dirac 0))
      (finiteMeasureMass (ν i)) (fun x => f i x.1)
      ((hf i).comp measurable_fst) hi u
    rw [recurrence_normalized_marked_integral (ν i)] at hc
    have he := recurrence_normalized_marked_integral_complex (ν i)
      (fun t => Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ))
    rw [he] at hc
    simpa only [canonicalRecurrenceLawOf,
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMeasureMarkedPoissonLaw,
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMarkedPoissonSampleLaw,
      one_mul] using hc
  have hp (r : Fin n → RecurConfig) :
      Complex.exp (Complex.I *
        (u * ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
          ∫ t, f i t ∂ν i) : ℝ)) =
      ∏ i : Fin n, Complex.exp (Complex.I *
        (u * ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
          ∫ t, f i t ∂ν i) : ℝ)) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [hp]
  rw [integral_fintype_prod_eq_prod (fun i (r : RecurConfig) =>
    Complex.exp (Complex.I * (u * ((∑ k : Fin r.1, f i ((r.2 k).1)) -
      ∫ t, f i t ∂ν i) : ℝ)))]
  simp_rw [hone]
  rw [Complex.exp_sum]

/-- Reading only assigned death/censor coordinates preserves every arm weight. -/
-- @node: recurrenceSubjectWeight_eq_selectedExposureHistory
lemma recurrenceSubjectWeight_eq_selectedExposureHistory (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (z : Fin n → LatentSubject) (i : Fin n) (t : ℝ) :
    recurrenceSubjectWeight c h a (fun j => observe (z j)) i t =
      recurrenceSubjectWeight c h a
        (fun j => recurrenceExposureHistory (selectedArmExposure (z j))) i t := by
  apply recurrenceSubjectWeight_arm_exposure_congr
  · intro j
    rfl
  · intro j hj
    simp only [observe, recurrenceExposureHistory, selectedArmExposure, censorHorizon]
    rfl
  · intro j hj
    simp only [observe, recurrenceExposureHistory, selectedArmExposure, censorHorizon]
    rfl

/-- Off the subject's assignment cell, all recurrence weights vanish. -/
-- @node: recurrenceSubjectWeight_zero_off_assignment
lemma recurrenceSubjectWeight_zero_off_assignment (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n)
    (hi : (s i).treatment ≠ a) (t : ℝ) :
    recurrenceSubjectWeight c h a s i t = 0 := by
  simp [recurrenceSubjectWeight, hi]

/-- The concrete arm score may use the selected recurrence configurations:
nonassigned subjects have zero point scores and zero compensators. -/
-- @node: recurrenceError_eq_selectedConcreteExposureScore
lemma recurrenceError_eq_selectedConcreteExposureScore (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      recurrenceConcreteExposureScore c P a n h
        (fun i => selectedArmExposure (z i))
        (fun i => selectedArmRecurrence (z i)) := by
  classical
  rw [recurrenceError_eq_latent_compensated_scores c P hP a z hh hh1]
  unfold recurrenceConcreteExposureScore
  simp_rw [recurrenceSubjectWeight_eq_selectedExposureHistory]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (z i).treatment = a
  · have hr : selectedArmRecurrence (z i) = (z i).recur a := by
      simp [selectedArmRecurrence, hi]
    exact congrArg (fun r : RecurConfig =>
      (∑ k : Fin r.1, if ((r.2 k).1) ≤ 1 - h then
        recurrenceSubjectWeight c h a
          (fun j => recurrenceExposureHistory (selectedArmExposure (z j))) i
          ((r.2 k).1) else 0) -
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a
        (fun j => recurrenceExposureHistory (selectedArmExposure (z j))) i t * P.lam a t)
      hr.symm
  · have hz (t : ℝ) : recurrenceSubjectWeight c h a
        (fun j => recurrenceExposureHistory (selectedArmExposure (z j))) i t = 0 := by
      apply recurrenceSubjectWeight_zero_off_assignment
      simpa [recurrenceExposureHistory, selectedArmExposure] using hi
    simp only [hz, ite_self, Finset.sum_const_zero, zero_mul,
      intervalIntegral.integral_zero, sub_self]

set_option maxHeartbeats 800000 in
/-- Push the actual signed contrast characteristic function to the iid
selected-arm mixture law. No independence between the two potential arms is used. -/
-- @node: recurrenceContrast_charFun_eq_selected_mixture
lemma recurrenceContrast_charFun_eq_selected_mixture
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    ∃ hν : ∀ a : Arm, IsFiniteMeasure (recurrenceIntensity P a),
      (∫ s : Fin n → ObsHistory, Complex.exp (Complex.I *
        (u * (recurrenceError c P true s h - recurrenceError c P false s h) : ℝ))
        ∂sampleLaw P n) =
      ∫ p : Fin n → (Arm × (ℝ × ENNReal)) × RecurConfig,
        Complex.exp (Complex.I * (u *
          (recurrenceConcreteExposureScore c P true n h (fun i => (p i).1)
            (fun i => (p i).2) -
           recurrenceConcreteExposureScore c P false n h (fun i => (p i).1)
            (fun i => (p i).2)) : ℝ))
        ∂Measure.pi (fun _ : Fin n =>
          ((P.latent.map (fun z : LatentSubject =>
            (z.treatment, (z.death false, z.censor false)))).restrict
              {e | e.1 = false}).prod (@canonicalRecurrenceLaw P false (hν false)) +
          ((P.latent.map (fun z : LatentSubject =>
            (z.treatment, (z.death true, z.censor true)))).restrict
              {e | e.1 = true}).prod (@canonicalRecurrenceLaw P true (hν true))) := by
  obtain ⟨hν, hmix⟩ := iid_selectedArm_exposure_recurrence_map_eq_pi_mixture
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence n
  refine ⟨hν, ?_⟩
  have ho : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have hp : Measurable (fun z : Fin n → LatentSubject =>
      fun i => (selectedArmExposure (z i), selectedArmRecurrence (z i))) := by
    fun_prop
  have ht := measurable_recurrenceError c P hP true n hh hh1
  have hf := measurable_recurrenceError c P hP false n hh hh1
  have hs (a : Arm) := measurable_recurrenceConcreteExposureScore c P
    hP.poissonRecurrence a n hh.le hh1
  have hproj : Measurable (fun p : Fin n →
      (Arm × (ℝ × ENNReal)) × RecurConfig =>
      ((fun i => (p i).1), (fun i => (p i).2))) := by fun_prop
  have hm (a : Arm) : Measurable (fun p : Fin n →
      (Arm × (ℝ × ENNReal)) × RecurConfig =>
      recurrenceConcreteExposureScore c P a n h (fun i => (p i).1)
        (fun i => (p i).2)) := by
    exact (hs a).comp hproj
  rw [recurrence_sampleLaw_eq_latent_map,
    integral_map ho.aemeasurable (by fun_prop)]
  simp_rw [recurrenceError_eq_selectedConcreteExposureScore c P hP true _ hh hh1,
    recurrenceError_eq_selectedConcreteExposureScore c P hP false _ hh hh1]
  rw [← hmix, integral_map hp.aemeasurable (by fun_prop)]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

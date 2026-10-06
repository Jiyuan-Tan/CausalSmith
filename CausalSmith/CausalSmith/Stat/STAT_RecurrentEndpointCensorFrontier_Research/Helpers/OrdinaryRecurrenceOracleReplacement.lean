module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceOracleReplacement
public import Causalean.Stat.RecurrentEvent.PoissonCampbell

/-! # Ordinary recurrence oracle replacement

Roadmap (17)--(19) and (23): recurrence points have nonnegative times under
 the canonical Poisson law. Thus the full-window future-mark score is the
ordinary recurrence error almost surely, and its oracle replacement applies
in the exact error decomposition.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Canonical recurrence points cannot occur before the study window. -/
-- @node: canonicalRecurrenceLaw_ae_nonneg_time
lemma canonicalRecurrenceLaw_ae_nonneg_time (P : SubjectLaw) (a : Arm)
    [hν : IsFiniteMeasure (recurrenceIntensity P a)] :
    ∀ᵐ s ∂(@canonicalRecurrenceLaw P a hν), ∀ i : Fin s.1, 0 ≤ (s.2 i).1 := by
  classical
  let ν := recurrenceIntensity P a
  let Q := normalizedFiniteMeasure ν (Measure.dirac 0)
  let R : Measure ℝ := Measure.dirac 0
  let rate := finiteMeasureMass ν
  let score : ℝ × ℝ → ℝ≥0∞ := fun x => if x.1 < 0 then 1 else 0
  let g : RecurConfig → ℝ≥0∞ := fun s => ∑ i : Fin s.1, score (s.2 i)
  have hscore : Measurable score := by
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_const measurable_const
  have hg : Measurable g := by
    intro t ht
    change @MeasurableSet _
      (⨅ n, (inferInstance : MeasurableSpace (Fin n → ℝ × ℝ)).map (Sigma.mk n))
      (g ⁻¹' t)
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet ((fun x : Fin n → ℝ × ℝ => ∑ i, score (x i)) ⁻¹' t)
    exact ht.preimage (Finset.measurable_sum Finset.univ
      (fun i _ => hscore.comp (measurable_pi_apply i)))
  have hQ : Q (Iio (0 : ℝ)) = 0 := by
    by_cases hz : ν = 0
    · simp [Q, normalizedFiniteMeasure, hz]
    · have hνzero : ν (Iio (0 : ℝ)) = 0 := by
        apply withDensity_absolutelyContinuous
        rw [Measure.restrict_apply measurableSet_Iio]
        have he : Iio (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = ∅ := by
          ext t
          simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_empty_iff_false, iff_false]
          intro h
          linarith [h.1, h.2.1]
        rw [he, measure_empty]
      simp [Q, normalizedFiniteMeasure, hz, Measure.smul_apply, hνzero]
  have hzero : (∫⁻ x, score x ∂Q.prod R) = 0 := by
    have he : score = ((Iio (0 : ℝ)) ×ˢ (univ : Set ℝ)).indicator 1 := by
      funext x
      simp [score, indicator_apply]
    rw [he, lintegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
    simp [Measure.prod_prod, hQ]
  have hlint : (∫⁻ s, g s ∂(@canonicalRecurrenceLaw P a hν)) = 0 := by
    have hcamp := Causalean.Stat.RecurrentEvent.finitePoissonSample_lintegral_sum
      (Q.prod R) rate score hscore
    rw [show @canonicalRecurrenceLaw P a hν = finitePoissonSampleLaw (Q.prod R) rate by
      unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
        finiteMeasureMarkedPoissonLaw finiteMarkedPoissonSampleLaw
      simp only [one_mul, Q, R, rate, ν]]
    change (∫⁻ s, ∑ i : Fin s.1, score (s.2 i) ∂finitePoissonSampleLaw (Q.prod R) rate) = 0
    rw [hcamp, lintegral_smul_measure, hzero, smul_zero]
  filter_upwards [(lintegral_eq_zero_iff' hg.aemeasurable).mp hlint] with s hs
  intro i
  by_contra hi
  have ht : (s.2 i).1 < 0 := lt_of_not_ge hi
  have hle : (1 : ℝ≥0∞) ≤ g s := by
    calc
      1 = score (s.2 i) := by simp [score, ht]
      _ ≤ g s := by
        dsimp only [g]
        exact Finset.single_le_sum (f := fun j : Fin s.1 => score (s.2 j)) (fun j _ => bot_le) (Finset.mem_univ i)
  rw [hs] at hle
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hle

/-- The model's recurrence marginal preserves nonnegative point times. -/
-- @node: recurrence_latent_ae_nonneg_time
lemma recurrence_latent_ae_nonneg_time (P : SubjectLaw) (hP : PoissonRecurrence P)
    (a : Arm) : ∀ᵐ z ∂P.latent, ∀ k : Fin (z.recur a).1,
      0 ≤ ((z.recur a).2 k).1 := by
  obtain ⟨hν, hmap⟩ := (hP a).2.2
  letI := hν
  have h := canonicalRecurrenceLaw_ae_nonneg_time P a
  rw [← hmap] at h
  exact ae_of_ae_map (measurable_latentSubject_recur a).aemeasurable h

/-- The ordinary recurrence error is the compensated full-window future-mark
score under the actual iid latent law. -/
-- @node: recurrenceError_zero_eq_remainingMean_compensated_latent_ae
lemma recurrenceError_zero_eq_remainingMean_compensated_latent_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      recurrenceError c P a (fun i => observe (z i)) 0 =
        remainingMeanRaw a (fun i => observe (z i)) 0 -
          remainingMeanDrift P a (fun i => observe (z i)) 0 := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hi : ∀ i : Fin n, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      ∀ k : Fin ((z i).recur a).1, 0 ≤ (((z i).recur a).2 k).1 := by
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P.latent) i).quasiMeasurePreserving.ae
      (recurrence_latent_ae_nonneg_time P hP.poissonRecurrence a)
  filter_upwards [ae_all_iff.mpr hi] with z hz
  rw [recurrenceError_eq_subject_compensators_of_nonneg c P hP a _ (by norm_num)
    (by norm_num)]
  simp only [sub_zero]
  rw [remainingMeanDrift_eq_subject_integrals c P hP a _ (by constructor <;> norm_num)]
  congr 1
  rw [recurrence_muTilde_eq_latent_point_scores, remainingMeanRaw_eq_latent_point_sum c]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [recurrenceSubjectWeight_eq_exposureHistory]
  simp [remainingRecurrenceWeight, hz i k]

/-- The full-window compensated tail identifies the ordinary recurrence error
almost surely in observed sample space. -/
-- @node: recurrenceError_zero_eq_remainingMean_compensated_ae
lemma recurrenceError_zero_eq_remainingMean_compensated_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (fun s : Fin n → ObsHistory => recurrenceError c P a s 0) =ᵐ[sampleLaw P n]
      (fun s => remainingMeanRaw a s 0 - remainingMeanDrift P a s 0) := by
  have herr := measurable_recurrenceError_of_nonneg c P hP a n
    (h := 0) (by norm_num) (by norm_num)
  have hraw := (measurable_remainingMeanRaw_joint a (n := n)).comp
    (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
  have hdrift := measurable_remainingMeanDrift P hP.poissonRecurrence a
    (n := n) (u := 0) (by constructor <;> norm_num)
  rw [recurrence_sampleLaw_eq_latent_map]
  apply (ae_map_iff
    (show Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) by
      fun_prop).aemeasurable
    (measurableSet_eq_fun herr (hraw.sub hdrift))).2
  exact recurrenceError_zero_eq_remainingMean_compensated_latent_ae c P hP a n

/-- The ordinary recurrence error admits the full-horizon root-n oracle
replacement, including the unbounded endpoint coefficient. -/
-- @node: recurrenceError_zero_oracle_difference_probability_tendsto_zero
lemma recurrenceError_zero_oracle_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * recurrenceError c P a s 0 -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
          (P.p a * Real.sqrt n)|}) atTop (nhds 0) := by
  apply (remainingMeanRaw_oracle_difference_probability_tendsto_zero
    c P hP hk a hε).congr'
  apply Eventually.of_forall
  intro n
  simp only [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [recurrenceError_zero_eq_remainingMean_compensated_ae c P hP a n]
    with s hs
  apply propext
  change (ε < |Real.sqrt n * (remainingMeanRaw a s 0 - remainingMeanDrift P a s 0) -
    observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
      (P.p a * Real.sqrt n)|) ↔
    (ε < |Real.sqrt n * recurrenceError c P a s 0 -
      observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
        (P.p a * Real.sqrt n)|)
  rw [hs]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

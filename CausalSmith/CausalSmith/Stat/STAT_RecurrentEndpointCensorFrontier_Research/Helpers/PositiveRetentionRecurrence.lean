module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskSet
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSamplingEnergy

/-!
# Recurrence energy at positive horizon retention

Roadmap (6)--(7): conditioning on exposure gives the exact ordinary recurrence
second moment, and the binomial reciprocal-risk bound gives a uniform C/n
bound. Neither endpoint smoothness nor a power-tail condition is required.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The ordinary recurrence score has an integrable square under the benchmark
sampling assumptions, without endpoint restrictions. -/
-- @node: positiveRetention_recurrenceError_zero_sq_integrable
lemma positiveRetention_recurrenceError_zero_sq_integrable
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hBounds : RecurrenceBounds c P) (hRandom : RandomAssignment P)
    (hRecurDeath : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (a : Arm) (n : ℕ) :
    Integrable (fun s : Fin n → ObsHistory => recurrenceError c P a s 0 ^ 2)
      (sampleLaw P n) := by
  exact (recurrenceError_secondMoment_eq_exposure_energy_of_nonneg_of_assumptions
    c P hPoisson hBounds hRandom hRecurDeath hCensor a n (by norm_num) (by norm_num)).1

/-- Unit continuation weight removes the polynomial envelope from the ordinary
recurrence energy bound. -/
-- @node: positiveRetention_recurrenceSubjectWeight_zero_energy_le
lemma positiveRetention_recurrenceSubjectWeight_zero_energy_le
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hBounds : RecurrenceBounds c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..1,
      recurrenceSubjectWeight c 0 a s i t ^ 2 * P.lam a t) ≤
      c.lambdaMax * ∫ t in (0 : ℝ)..1, invRisk a s t := by
  have hi (i : Fin n) :=
    recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions
      c P hPoisson a s i (h := 0) (by norm_num) (by norm_num) 2
  simp only [sub_zero] at hi
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i),
    ← intervalIntegral.integral_const_mul]
  have hsum : IntervalIntegrable (fun t => ∑ i : Fin n,
      recurrenceSubjectWeight c 0 a s i t ^ 2 * P.lam a t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integrable_finsetSum Finset.univ (fun i _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp (hi i))
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hsum
    ((recurrenceInvRisk_intervalIntegrable a s (by norm_num : (0 : ℝ) ≤ 1)).const_mul _)
  intro t ht
  rw [← Finset.sum_mul, recurrenceSubjectWeight_sum_sq]
  simp only [continuationWeight, if_true, one_pow, one_mul]
  have hk := deathKMLeft_mem_Icc a s t
  have hk2 : deathKMLeft a s t ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
  have hl := hBounds a t ht
  have hl0 := c.lambdaMin_pos.le.trans hl.1
  have hr := (recurrence_invRisk_mem_Icc a s t).1
  calc
    _ ≤ 1 * invRisk a s t * P.lam a t := by gcongr
    _ ≤ c.lambdaMax * invRisk a s t := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hl.2)]

/-- The exposure-law Poisson identity and Fubini give the ordinary score's
second moment bound while retaining the observed inverse-risk factor. -/
-- @node: positiveRetention_recurrenceError_zero_secondMoment_le_expectedInverseRisk
lemma positiveRetention_recurrenceError_zero_secondMoment_le_expectedInverseRisk
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hBounds : RecurrenceBounds c P) (hRandom : RandomAssignment P)
    (hRecurDeath : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (a : Arm) (n : ℕ) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      c.lambdaMax * ∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
        invRisk a s t ∂sampleLaw P n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => invRisk a p.1 p.2)
      ((sampleLaw P n).prod ν) := by
    apply Integrable.of_bound (measurable_recurrenceInvRisk_joint a).aestronglyMeasurable 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a p.1 p.2).1]
    exact (recurrence_invRisk_mem_Icc a p.1 p.2).2
  have heMeas : Measurable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      ∫ t in (0 : ℝ)..1, recurrenceSubjectWeight c 0 a s i t ^ 2 * P.lam a t) := by
    apply Finset.measurable_sum
    intro i _
    simpa only [sub_zero] using
      measurable_recurrenceWeightIntegral c P hPoisson a i (h := 0)
        (by norm_num) (by norm_num) 2
  have heInt : Integrable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      ∫ t in (0 : ℝ)..1, recurrenceSubjectWeight c 0 a s i t ^ 2 * P.lam a t)
      (sampleLaw P n) := by
    apply Integrable.of_bound heMeas.aestronglyMeasurable
      (n * (weightEnvelope c ^ 2 * c.lambdaMax))
    filter_upwards [] with s
    rw [Real.norm_eq_abs]
    simpa only [sub_zero] using
      recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions
        c P hBounds a s (h := 0) (by norm_num) (by norm_num)
  rw [recurrenceError_secondMoment_eq_subject_energy_of_nonneg_of_assumptions
    c P hPoisson hBounds hRandom hRecurDeath hCensor a n (by norm_num) (by norm_num)]
  simp only [sub_zero]
  calc
    _ ≤ ∫ s : Fin n → ObsHistory, c.lambdaMax * ∫ t, invRisk a s t ∂ν
        ∂sampleLaw P n := by
      apply integral_mono heInt (hi.integral_prod_left.const_mul _)
      intro s
      simpa only [ν, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        positiveRetention_recurrenceSubjectWeight_zero_energy_le c P hPoisson hBounds a s
    _ = _ := by
      rw [integral_const_mul, integral_integral_swap hi]
      dsimp only [ν]
      rw [integral_Ioc_eq_integral_Ioo]

/-- The ordinary recurrence component has the parametric second-moment bound
in roadmap (7), using horizon retention and the reciprocal-binomial estimate. -/
-- @node: positiveRetention_recurrenceError_zero_secondMoment_le_inv_sampleSize
lemma positiveRetention_recurrenceError_zero_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hBounds : RecurrenceBounds c P) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hRecurDeath : RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P)
    (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      (2 * c.lambdaMax / (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  calc
    _ ≤ c.lambdaMax * ∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
        invRisk a s t ∂sampleLaw P n :=
      positiveRetention_recurrenceError_zero_secondMoment_le_expectedInverseRisk
        c P hPoisson hBounds hRandom hRecurDeath hCensor a n
    _ ≤ c.lambdaMax *
        (2 / ((n : ℝ) * (c.pMin * Real.exp (-c.dMax) * c.Ghor))) :=
      mul_le_mul_of_nonneg_left
        (positiveRetention_integral_expected_invRisk_le c P hRandom hAssignment
          hOverlap hDeath hCensor hDeathBounds hHorizon a hn)
        (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
    _ = _ := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

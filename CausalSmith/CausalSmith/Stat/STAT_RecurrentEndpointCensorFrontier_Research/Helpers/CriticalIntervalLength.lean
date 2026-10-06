module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalCoverage
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestBandwidthRates
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Critical interval length and the Jensen bridge

Roadmap (34): clipping bounds the nonfallback length by twice the observable
standard error. The full-range fallback contributes its probability times the
clinical range. Jensen converts mean optional variation to mean standard error.
The statistical mean-variation and exponential fallback bounds are separate
obligations; none is asserted here.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The armwise optional variation is nonnegative on every observed sample. -/
-- @node: armCriticalVariance_nonneg
lemma armCriticalVariance_nonneg (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) : 0 ≤ armCriticalVariance c a s := by
  classical
  unfold armCriticalVariance
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp hx
    positivity
  · rfl

/-- Summing the two arms preserves nonnegativity of the actual studentizer. -/
-- @node: criticalVarianceEstimator_nonneg
lemma criticalVarianceEstimator_nonneg (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : 0 ≤ criticalVarianceEstimator c s := by
  exact add_nonneg (armCriticalVariance_nonneg c false s)
    (armCriticalVariance_nonneg c true s)

/-- Both branches of the studentized interval lie in the clinical target range. -/
-- @node: criticalInterval_subset_range
lemma criticalInterval_subset_range (c : ClassConstants) (alpha : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) : criticalInterval c alpha s ⊆ Icc (-c.lambdaMax) c.lambdaMax := by
  classical
  unfold criticalInterval
  split_ifs
  · exact inter_subset_right
  · exact Subset.rfl

/-- Clipping and fallback give a deterministic bound on the interval length. -/
-- @node: criticalInterval_length_le_range
lemma criticalInterval_length_le_range (c : ClassConstants) (alpha : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) : volume.real (criticalInterval c alpha s) ≤ 2 * c.lambdaMax := by
  have h := measureReal_mono (criticalInterval_subset_range c alpha s)
    (show volume (Icc (-c.lambdaMax) c.lambdaMax) ≠ ⊤ by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  rw [Real.volume_real_Icc_of_le (by linarith [c.lambdaMin_pos, c.lambdaMin_lt])] at h
  linarith

/-- On nonfallback samples, clipping cannot increase the Gaussian length. -/
-- @node: criticalInterval_length_le_standardError
lemma criticalInterval_length_le_standardError (c : ClassConstants) (alpha : ℝ)
    {n : ℕ} (s : Fin n → ObsHistory) (hf : nonFallback c s)
    (hz : 0 ≤ normalQuantile alpha) :
    volume.real (criticalInterval c alpha s) ≤
      2 * normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s) := by
  classical
  rw [criticalInterval, if_pos hf, Icc_inter_Icc, Real.volume_real_Icc]
  apply max_le
  · have hl := le_max_left
      (observableEstimator c s - normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s))
      (-c.lambdaMax)
    have hu := min_le_left
      (observableEstimator c s + normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s))
      c.lambdaMax
    linarith
  · positivity

/-- The explicit clipped endpoints and measurable fallback event give measurable length. -/
-- @node: measurable_criticalInterval_length
@[fun_prop]
lemma measurable_criticalInterval_length (c : ClassConstants) (alpha : ℝ) (n : ℕ) :
    Measurable (fun s : Fin n → ObsHistory => volume.real (criticalInterval c alpha s)) := by
  classical
  have heq : (fun s : Fin n → ObsHistory => volume.real (criticalInterval c alpha s)) =
      fun s => if nonFallback c s then
        max (min (observableEstimator c s +
            normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s))
            c.lambdaMax - max (observableEstimator c s -
            normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s))
            (-c.lambdaMax)) 0
      else 2 * c.lambdaMax := by
    funext s
    by_cases hf : nonFallback c s
    · simp [criticalInterval, hf, Icc_inter_Icc, Real.volume_real_Icc]
    · simp [criticalInterval, hf, Real.volume_real_Icc_of_le
        (show -c.lambdaMax ≤ c.lambdaMax by linarith [c.lambdaMin_pos, c.lambdaMin_lt])]
      ring
  rw [heq]
  apply Measurable.ite (measurableSet_nonFallback c n)
  · fun_prop
  · fun_prop

/-- The clinical range bound supplies length integrability under every finite sample law. -/
-- @node: integrable_criticalInterval_length
lemma integrable_criticalInterval_length (c : ClassConstants) (alpha : ℝ) (n : ℕ)
    (μ : Measure (Fin n → ObsHistory)) [IsFiniteMeasure μ] :
    Integrable (fun s => volume.real (criticalInterval c alpha s)) μ := by
  apply Integrable.of_bound (measurable_criticalInterval_length c alpha n).aestronglyMeasurable
    (2 * c.lambdaMax)
  exact Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact criticalInterval_length_le_range c alpha s)

/-- Finite mean optional variation implies an integrable observable standard error. -/
-- @node: integrable_criticalStandardError_of_variance
lemma integrable_criticalStandardError_of_variance (c : ClassConstants) (n : ℕ)
    (μ : Measure (Fin n → ObsHistory)) [IsFiniteMeasure μ]
    (hv : Integrable (criticalVarianceEstimator c) μ) :
    Integrable (fun s => Real.sqrt (criticalVarianceEstimator c s)) μ := by
  apply ((integrable_const (1 : ℝ)).add hv).mono'
    (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hv0 := criticalVarianceEstimator_nonneg c s
  have hs := Real.sq_sqrt hv0
  have hp := Real.sqrt_nonneg (criticalVarianceEstimator c s)
  change Real.sqrt (criticalVarianceEstimator c s) ≤ 1 + criticalVarianceEstimator c s
  nlinarith [sq_nonneg (Real.sqrt (criticalVarianceEstimator c s) - 1)]

/-- Jensen's inequality bounds expected standard error by root expected optional variation. -/
-- @node: criticalStandardError_integral_le_sqrt_mean_variance
lemma criticalStandardError_integral_le_sqrt_mean_variance (c : ClassConstants) (n : ℕ)
    (μ : Measure (Fin n → ObsHistory)) [IsProbabilityMeasure μ]
    (hv : Integrable (criticalVarianceEstimator c) μ) :
    (∫ s, Real.sqrt (criticalVarianceEstimator c s) ∂μ) ≤
      Real.sqrt (∫ s, criticalVarianceEstimator c s ∂μ) := by
  exact Real.strictConcaveOn_sqrt.concaveOn.le_map_integral
    Real.continuous_sqrt.continuousOn isClosed_Ici
    (Eventually.of_forall (criticalVarianceEstimator_nonneg c)) hv
    (integrable_criticalStandardError_of_variance c n μ hv)

/-- The expected-length bridge retains the full fallback contribution and the
actual optional-variation mean. No convergence or rate bound is assumed. -/
-- @node: criticalInterval_expected_length_le_mean_variance_fallback
lemma criticalInterval_expected_length_le_mean_variance_fallback
    (c : ClassConstants) (alpha : ℝ) (n : ℕ)
    (μ : Measure (Fin n → ObsHistory)) [IsProbabilityMeasure μ]
    (hz : 0 ≤ normalQuantile alpha) (hv : Integrable (criticalVarianceEstimator c) μ) :
    (∫ s, volume.real (criticalInterval c alpha s) ∂μ) ≤
      2 * normalQuantile alpha * Real.sqrt (∫ s, criticalVarianceEstimator c s ∂μ) +
        2 * c.lambdaMax * μ.real {s | ¬ nonFallback c s} := by
  classical
  let B : Set (Fin n → ObsHistory) := {s | ¬ nonFallback c s}
  have hB : MeasurableSet B := (measurableSet_nonFallback c n).compl
  have hi := integral_mono (integrable_criticalInterval_length c alpha n μ)
    (((integrable_criticalStandardError_of_variance c n μ hv).const_mul
      (2 * normalQuantile alpha)).add ((integrable_const (2 * c.lambdaMax)).indicator hB))
    (fun s => show volume.real (criticalInterval c alpha s) ≤
      2 * normalQuantile alpha * Real.sqrt (criticalVarianceEstimator c s) +
        B.indicator (fun _ => 2 * c.lambdaMax) s from by
      by_cases hf : nonFallback c s
      · rw [indicator_of_notMem (show s ∉ B from not_not.mpr hf), add_zero]
        exact criticalInterval_length_le_standardError c alpha s hf hz
      · rw [indicator_of_mem (show s ∈ B from hf)]
        have hb := criticalInterval_length_le_range c alpha s
        exact hb.trans (le_add_of_nonneg_left (by positivity)))
  simp only [Pi.add_apply] at hi
  rw [integral_add
      ((integrable_criticalStandardError_of_variance c n μ hv).const_mul _)
      ((integrable_const (2 * c.lambdaMax)).indicator hB), integral_const_mul,
    integral_indicator_const _ hB] at hi
  have hj := mul_le_mul_of_nonneg_left
    (criticalStandardError_integral_le_sqrt_mean_variance c n μ hv)
    (show 0 ≤ 2 * normalQuantile alpha by positivity)
  have ht := hi.trans (add_le_add hj (le_refl (μ.real B • (2 * c.lambdaMax))))
  simpa only [B, smul_eq_mul, mul_comm (μ.real {s | ¬ nonFallback c s})] using ht


/-- A bounded recurrence point weight has an integrable observed arm count.
The compensated Poisson moment identity supplies the random part; the stopped
intensity integral is uniformly bounded by the finite intensity mass. -/
-- @node: integrable_armRecurrencePointCount
lemma integrable_armRecurrencePointCount (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (T : ℝ) :
    Integrable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      if (s i).treatment = a then
        (((s i).recur.times.filter (fun t => t ≤ T)).map (fun _ => (1 : ℝ))).sum
      else 0) (sampleLaw P n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hs := (observedRecurrenceScore_moments_of_bound c P hP a n T
    (fun _ => 1) measurable_const (by norm_num : (0 : ℝ) ≤ 1)
    (by intros; norm_num)).1
  have hc (i : Fin n) : Integrable (fun s : Fin n → ObsHistory =>
      ∫ t, observedRecurrenceTimeWeight a T (fun _ => 1) (s i) t
        ∂recurrenceIntensity P a) (sampleLaw P n) := by
    apply Integrable.of_bound
      (((measurable_observedRecurrenceTimeWeight a T (fun _ => 1)
        measurable_const).stronglyMeasurable.integral_prod_right.measurable).comp
        (measurable_pi_apply i)).aestronglyMeasurable
      ((recurrenceIntensity P a).real univ)
    filter_upwards [] with s
    simpa using norm_integral_le_of_norm_le_const
      (μ := recurrenceIntensity P a) (C := (1 : ℝ))
      (f := observedRecurrenceTimeWeight a T (fun _ => 1) (s i))
      (Eventually.of_forall (fun t => by
        unfold observedRecurrenceTimeWeight
        split_ifs <;> norm_num))
  have hi := hs.add (integrable_finsetSum Finset.univ (fun i _ => hc i))
  apply hi.congr
  filter_upwards [] with s
  unfold observedRecurrenceScore
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The optional variation is dominated by the observed recurrence count,
using bounded continuation weights, survival products, and totalized inverse risk. -/
-- @node: armCriticalVariance_le_pointCount
lemma armCriticalVariance_le_pointCount (c : ClassConstants) (a : Arm) {n : ℕ}
    (hn : 0 < n) (s : Fin n → ObsHistory) :
    armCriticalVariance c a s ≤ weightEnvelope c ^ 2 *
      (∑ i : Fin n, if (s i).treatment = a then
        (((s i).recur.times.filter (fun t => t ≤ 1 - bandwidth c n)).map
          (fun _ => (1 : ℝ))).sum else 0) := by
  classical
  rw [Finset.mul_sum]
  unfold armCriticalVariance
  apply Finset.sum_le_sum
  intro i _
  split_ifs with ha
  · rw [recurrence_times_filtered_sum, recurrence_times_filtered_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with ht
    · simp only [mul_one]
      have hw := continuationWeight_abs_le_envelope_of_nonneg c
        (bandwidth_pos_and_le_cap c hn).1.le (t := ((s i).recur.2 k).1)
      have hw2 : continuationWeight (holderOrder c) (bandwidth c n)
          ((s i).recur.2 k).1 ^ 2 ≤ weightEnvelope c ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
      have hd := deathKMLeft_mem_Icc a s ((s i).recur.2 k).1
      have hr := recurrence_invRisk_mem_Icc a s ((s i).recur.2 k).1
      have hd2 : deathKMLeft a s ((s i).recur.2 k).1 ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ hd.1 hd.2 2
      have hr2 : invRisk a s ((s i).recur.2 k).1 ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ hr.1 hr.2 2
      calc
        _ ≤ weightEnvelope c ^ 2 * 1 * 1 := by gcongr
        _ = _ := by ring
    · simp
  · simp

/-- Finite Poisson intensity supplies integrability of the arm optional variation.
No inverse-retention moment is added as a premise. -/
-- @node: integrable_armCriticalVariance
lemma integrable_armCriticalVariance (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (armCriticalVariance c a (n := n)) (sampleLaw P n) := by
  apply ((integrable_armRecurrencePointCount c P hP a n (1 - bandwidth c n)).const_mul
    (weightEnvelope c ^ 2)).mono' (by fun_prop)
  exact Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (armCriticalVariance_nonneg c a s)]
    exact armCriticalVariance_le_pointCount c a hn s)

/-- The actual critical variance estimator has finite mean under the stated model. -/
-- @node: integrable_criticalVarianceEstimator
lemma integrable_criticalVarianceEstimator (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 0 < n) :
    Integrable (criticalVarianceEstimator c (n := n)) (sampleLaw P n) := by
  exact (integrable_armCriticalVariance c P hP false hn).add
    (integrable_armCriticalVariance c P hP true hn)

/-- Roadmap (34)'s expectation bridge holds directly for every model law,
with no added integrability premise or statistical rate certificate. -/
-- @node: criticalInterval_expected_length_le_model_mean_variance_fallback
lemma criticalInterval_expected_length_le_model_mean_variance_fallback
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2) {n : ℕ} (hn : 0 < n) :
    (∫ s, volume.real (criticalInterval c alpha s) ∂sampleLaw P n) ≤
      2 * normalQuantile alpha *
        Real.sqrt (∫ s, criticalVarianceEstimator c s ∂sampleLaw P n) +
        2 * c.lambdaMax * (sampleLaw P n).real {s | ¬ nonFallback c s} := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  exact criticalInterval_expected_length_le_mean_variance_fallback c alpha n
    (sampleLaw P n) (normalQuantile_pos ha0 ha1).le
    (integrable_criticalVarianceEstimator c P hP hn)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

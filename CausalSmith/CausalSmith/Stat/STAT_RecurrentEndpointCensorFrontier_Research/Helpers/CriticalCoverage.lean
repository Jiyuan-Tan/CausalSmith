module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoverage

/-!
# Critical interval coverage from its studentized CDF

Roadmap's final coverage step: clipping preserves target membership and the
full-range fallback covers. Shifted CDF sandwiches control finite-sample atoms
along arbitrary triangular sequences. The Gaussian limit and variance
consistency remain separate obligations.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The optional recurrence variation is measurable as a finite configuration sum. -/
-- @node: measurable_armCriticalVariance
@[fun_prop]
lemma measurable_armCriticalVariance (c : ClassConstants) (a : Arm) {n : ℕ} :
    Measurable (armCriticalVariance c a (n := n)) := by
  classical
  unfold armCriticalVariance
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · have hm : Measurable (fun p : (Fin n → ObsHistory) × RecurConfig =>
        ∑ k : Fin p.2.1, if (p.2.2 k).1 ≤ 1 - bandwidth c n then
          (continuationWeight (holderOrder c) (bandwidth c n) (p.2.2 k).1) ^ 2 * (deathKMLeft a p.1 (p.2.2 k).1) ^ 2 *
            (invRisk a p.1 (p.2.2 k).1) ^ 2 else 0) := by
      apply measurable_recurrence_param_point_sum
        (fun s x => if x.1 ≤ 1 - bandwidth c n then
          (continuationWeight (holderOrder c) (bandwidth c n) x.1) ^ 2 * (deathKMLeft a s x.1) ^ 2 * (invRisk a s x.1) ^ 2 else 0)
      apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      · have hx : Measurable (fun p : (Fin n → ObsHistory) × (ℝ × ℝ) =>
            (p.1, p.2.1)) := by fun_prop
        exact ((((measurable_recurrenceContinuationWeight c (bandwidth c n)).comp (by fun_prop)).pow_const 2).mul
          (((measurable_recurrenceDeathKMLeft_joint a).comp hx).pow_const 2)).mul
          (((measurable_recurrenceInvRisk_joint a).comp hx).pow_const 2)
      · exact measurable_const
    have heq : (fun s : Fin n → ObsHistory =>
        Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1 - bandwidth c n)).map
          (fun t => (continuationWeight (holderOrder c) (bandwidth c n) t) ^ 2 * (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2))) =
        fun s => ∑ k : Fin (s i).recur.1, if ((s i).recur.2 k).1 ≤ 1 - bandwidth c n then
          (continuationWeight (holderOrder c) (bandwidth c n) ((s i).recur.2 k).1) ^ 2 * (deathKMLeft a s ((s i).recur.2 k).1) ^ 2 *
            (invRisk a s ((s i).recur.2 k).1) ^ 2 else 0 := by
      funext s
      exact recurrence_times_filtered_sum _ _ _
    rw [heq]
    exact hm.comp (measurable_id.prodMk (by fun_prop))
  · exact measurable_const

/-- The actual summed critical studentizer is measurable. -/
-- @node: measurable_criticalVarianceEstimator
@[fun_prop]
lemma measurable_criticalVarianceEstimator (c : ClassConstants) {n : ℕ} :
    Measurable (criticalVarianceEstimator c (n := n)) := by
  unfold criticalVarianceEstimator
  fun_prop

/-- The critical nonfallback event is measurable. -/
-- @node: measurableSet_nonFallback
lemma measurableSet_nonFallback (c : ClassConstants) (n : ℕ) :
    MeasurableSet {s : Fin n → ObsHistory | nonFallback c s} := by
  unfold nonFallback
  exact (measurableSet_lt measurable_const (measurable_subcritical_armSize false n)).inter
    ((measurableSet_lt measurable_const (measurable_subcritical_armSize true n)).inter
      (measurableSet_lt measurable_const (measurable_criticalVarianceEstimator c)))

/-- Clipping preserves target membership and fallback covers the clinical range. -/
-- @node: mem_criticalInterval_iff_studentized
lemma mem_criticalInterval_iff_studentized (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (alpha : ℝ) {n : ℕ} (s : Fin n → ObsHistory) :
    causalTarget P ∈ criticalInterval c alpha s ↔
      ¬ nonFallback c s ∨ (nonFallback c s ∧
        |(observableEstimator c s - causalTarget P) /
          Real.sqrt (criticalVarianceEstimator c s)| ≤ normalQuantile alpha) := by
  classical
  have hm := causalTarget_mem_range c P hP
  by_cases hf : nonFallback c s
  · have hd := Real.sqrt_pos.mpr hf.2.2
    rw [criticalInterval, if_pos hf, mem_inter_iff, and_iff_left hm]
    simp only [hf, not_true_eq_false, false_or, true_and, mem_Icc]
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · simp [criticalInterval, hf, hm]

/-- Supremum CDF convergence implies convergence at each fixed threshold. -/
-- @node: critical_studentized_cdf_tendsto_of_sup
lemma critical_studentized_cdf_tendsto_of_sup
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (h : Tendsto (fun n => sSup {d : ℝ | ∃ z : ℝ,
      d = |(sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
        (observableEstimator c s - causalTarget (Pseq n)) /
          Real.sqrt (criticalVarianceEstimator c s) ≤ z} - normalCDF z|})
      atTop (nhds 0)) (z : ℝ) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z}) atTop (nhds (normalCDF z)) := by
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI (n : ℕ) : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  have hb (n : ℕ) : BddAbove {d : ℝ | ∃ x : ℝ,
      d = |(sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
        (observableEstimator c s - causalTarget (Pseq n)) /
          Real.sqrt (criticalVarianceEstimator c s) ≤ x} - normalCDF x|} := by
    refine ⟨1, ?_⟩
    rintro d ⟨x, rfl⟩
    have hp0 : 0 ≤ (sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ x} := measureReal_nonneg
    have hp1 : (sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ x} ≤ 1 := measureReal_le_one
    have hn0 : 0 ≤ normalCDF x := measureReal_nonneg
    have hn1 : normalCDF x ≤ 1 := measureReal_le_one
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with n hn
  rw [Real.dist_eq] at hn ⊢
  have hle := le_csSup (hb n) (show
    |(sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z} - normalCDF z| ∈ _ from ⟨z, rfl⟩)
  exact hle.trans_lt ((le_abs_self _).trans_lt (by simpa using hn))

/-- Critical roadmap final step: a Gaussian studentized CDF and vanishing
fallback mass give exact coverage of the clipped interval along triangular laws. -/
-- @node: criticalInterval_coverage_triangular_tendsto
lemma criticalInterval_coverage_triangular_tendsto
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2)
    (hf : Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ¬ nonFallback c s}) atTop (nhds 0))
    (hcdf : ∀ z : ℝ, Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | nonFallback c s ∧ (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z}) atTop (nhds (normalCDF z))) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | causalTarget (Pseq n) ∈ criticalInterval c alpha s}) atTop (nhds (1 - alpha)) := by
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI (n : ℕ) : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  let z := normalQuantile alpha
  have hz : 0 < z := normalQuantile_pos ha0 ha1
  have hnormal (x : ℝ) : normalCDF x = Causalean.Mathlib.stdNormalCDF x :=
    (cdf_eq_real _ _).symm
  have hcont : ContinuousAt normalCDF (-z) := by
    have he : normalCDF = Causalean.Mathlib.stdNormalCDF := funext hnormal
    rw [he]
    exact Causalean.Mathlib.stdNormalCDF_continuous.continuousAt
  have hid : normalCDF z - normalCDF (-z) = 1 - alpha :=
    normalCDF_quantile_difference alpha ha0 ha1
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hnear⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
  let δ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hdist : dist (-z - δ) (-z) < η := by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
    dsimp [δ]; linarith
  have hnorm := hnear hdist
  rw [Real.dist_eq] at hnorm
  filter_upwards [(Metric.tendsto_nhds.mp (hcdf z))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp (hcdf (-z)))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp (hcdf (-z - δ)))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hf) (ε / 4) (by positivity)] with n hhi hlo hshift hfb
  let U : (Fin n → ObsHistory) → ℝ := fun s =>
    (observableEstimator c s - causalTarget (Pseq n)) / Real.sqrt (criticalVarianceEstimator c s)
  have hmU : Measurable U := by
    dsimp [U]
    fun_prop
  have hm : MeasurableSet {s | nonFallback c s ∧ U s ≤ -z - δ} :=
    (measurableSet_nonFallback c n).inter (measurableSet_le hmU measurable_const)
  have hb := twoSided_coverage_probability_sandwich (sampleLaw (Pseq n) n)
    (nonFallback c) U {s | causalTarget (Pseq n) ∈ criticalInterval c alpha s}
    z δ hz.le hδ hm (fun s => mem_criticalInterval_iff_studentized c (Pseq n) (hP n) alpha s)
  rw [Real.dist_eq] at hhi hlo hshift hfb ⊢
  rw [sub_zero, abs_of_nonneg measureReal_nonneg] at hfb
  rw [abs_lt] at hhi hlo hshift hnorm ⊢
  dsimp only [U] at hb
  constructor <;> linarith [hb.1, hb.2]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

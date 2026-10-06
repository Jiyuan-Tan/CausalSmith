module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalGaussianCDF
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestIntervalGeometry
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionBenchmark

/-!
# Coverage of the subcritical observable interval

Roadmap (45): target membership is the two-sided studentized event on
nonfallback samples. CDF sandwiches handle possible endpoint atoms, and the
vanishing fallback mass supplies coverage of the full-range interval.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The ordinary contrast is a measurable zero-bandwidth projected estimate. -/
-- @node: measurable_ordinaryEstimator
@[fun_prop]
lemma measurable_ordinaryEstimator (c : ClassConstants) (n : ℕ) :
    Measurable (ordinaryEstimator c (n := n)) := by
  have he : ordinaryEstimator c (n := n) = fun s =>
      muHatAt c 0 true s - muHatAt c 0 false s := by
    funext s
    exact benchmark_ordinaryEstimator_eq_muHatAt_zero_contrast c s
  rw [he]
  fun_prop

/-- The finite assignment count is measurable. -/
-- @node: measurable_subcritical_armSize
@[fun_prop]
lemma measurable_subcritical_armSize (a : Arm) (n : ℕ) :
    Measurable (armSize (n := n) a) := by
  classical
  have he : armSize (n := n) a = fun s =>
      ∑ i : Fin n, if (s i).treatment = a then (1 : ℕ) else 0 := by
    funext s
    simp [armSize]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    measurable_const measurable_const

/-- The nonfallback event is measurable, including positivity of the actual variance. -/
-- @node: measurableSet_nonFallbackSub
lemma measurableSet_nonFallbackSub (c : ClassConstants) (n : ℕ) :
    MeasurableSet {s : Fin n → ObsHistory | nonFallbackSub c s} := by
  unfold nonFallbackSub
  exact (measurableSet_lt measurable_const (measurable_subcritical_armSize false n)).inter
    ((measurableSet_lt measurable_const (measurable_subcritical_armSize true n)).inter
      (measurableSet_lt measurable_const (measurable_sigmaHatSq c)))

/-- For targets in range, clipping preserves membership; fallback always covers.
On positive sample sizes the remaining event is the exact studentized bound. -/
-- @node: mem_subcriticalInterval_iff_studentized
lemma mem_subcriticalInterval_iff_studentized (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (alpha : ℝ) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) :
    causalTarget P ∈ subcriticalInterval c alpha s ↔
      ¬ nonFallbackSub c s ∨ (nonFallbackSub c s ∧
        |Real.sqrt n * (ordinaryEstimator c s - causalTarget P) /
          Real.sqrt (sigmaHatSq c s)| ≤ normalQuantile alpha) := by
  classical
  have hm := causalTarget_mem_range c P hP
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr := Real.sqrt_pos.mpr hnR
  by_cases hf : nonFallbackSub c s
  · have hd := Real.sqrt_pos.mpr hf.2.2
    rw [subcriticalInterval, if_pos hf, mem_inter_iff, and_iff_left hm]
    simp only [hf, not_true_eq_false, false_or, true_and, mem_Icc]
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_mul, abs_of_pos hnr]
    rw [mul_comm (Real.sqrt (n : ℝ)), ← le_div_iff₀ hnr]
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · simp [subcriticalInterval, hf, hm]

/-- The exact two-sided normal probability at the paper's quantile. -/
-- @node: normalCDF_quantile_difference
lemma normalCDF_quantile_difference (alpha : ℝ) (ha0 : 0 < alpha)
    (ha1 : alpha < 1 / 2) :
    normalCDF (normalQuantile alpha) - normalCDF (-normalQuantile alpha) = 1 - alpha := by
  have he (x : ℝ) : normalCDF x = Causalean.Mathlib.stdNormalCDF x :=
    (cdf_eq_real _ _).symm
  rw [he, he, Causalean.Mathlib.stdNormalCDF_neg, normalQuantile_eq_probit,
    Causalean.Mathlib.stdNormalCDF_probit (by linarith) (by linarith)]
  ring

/-- A two-sided event is sandwiched by CDF differences. The shifted lower
threshold avoids assuming absence of atoms in finite samples. -/
-- @node: twoSided_coverage_probability_sandwich
lemma twoSided_coverage_probability_sandwich {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Prop) (U : Ω → ℝ)
    (C : Set Ω) (z δ : ℝ) (hz : 0 ≤ z) (hδ : 0 < δ)
    (hm : MeasurableSet {s | F s ∧ U s ≤ -z - δ})
    (hC : ∀ s, s ∈ C ↔ ¬ F s ∨ (F s ∧ |U s| ≤ z)) :
    μ.real {s | F s ∧ U s ≤ z} - μ.real {s | F s ∧ U s ≤ -z} ≤ μ.real C ∧
    μ.real C ≤ μ.real {s | F s ∧ U s ≤ z} -
      μ.real {s | F s ∧ U s ≤ -z - δ} + μ.real {s | ¬ F s} := by
  constructor
  · have hi : {s | F s ∧ U s ≤ z} ⊆ C ∪ {s | F s ∧ U s ≤ -z} := by
      intro s hs
      by_cases hl : U s ≤ -z
      · exact Or.inr ⟨hs.1, hl⟩
      · exact Or.inl ((hC s).2 (Or.inr ⟨hs.1, abs_le.mpr ⟨(not_le.mp hl).le, hs.2⟩⟩))
    have hh := (measureReal_mono (μ := μ) hi (by finiteness)).trans (measureReal_union_le _ _)
    linarith
  · have hd : Disjoint {s | F s ∧ U s ≤ -z - δ} C := by
      rw [Set.disjoint_left]
      intro s hs hc
      rcases (hC s).1 hc with hf | hf
      · exact hf hs.1
      · have := (abs_le.mp hf.2).1
        linarith [hs.2]
    have hi : {s | F s ∧ U s ≤ -z - δ} ∪ C ⊆
        {s | F s ∧ U s ≤ z} ∪ {s | ¬ F s} := by
      intro s hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hs.1, by linarith [hs.2]⟩
      · rcases (hC s).1 hs with hf | hf
        · exact Or.inr hf
        · exact Or.inl ⟨hf.1, (abs_le.mp hf.2).2⟩
    have hh := (measureReal_mono (μ := μ) hi (by finiteness)).trans (measureReal_union_le _ _)
    rw [measureReal_union' hd hm] at hh
    linarith

/-- Roadmap (45): the actual clipped interval with full-range fallback has
asymptotically exact two-sided Gaussian coverage. -/
-- @node: subcriticalInterval_coverage_tendsto
lemma subcriticalInterval_coverage_tendsto
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2) :
    Tendsto (fun n => (sampleLaw P n).real
      {s | causalTarget P ∈ subcriticalInterval c alpha s}) atTop (nhds (1 - alpha)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
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
  have hf := nonFallbackSub_compl_probability_tendsto_of_variance_consistency
    c P hP hk (fun e he => sigmaHatSq_probability_tendsto_subcriticalVariance c P hP hk he)
  filter_upwards [eventually_ge_atTop 1,
    (Metric.tendsto_nhds.mp (subcritical_studentized_cdf_tendsto c P hP hk z))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp (subcritical_studentized_cdf_tendsto c P hP hk (-z)))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp (subcritical_studentized_cdf_tendsto c P hP hk (-z - δ)))
      (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hf) (ε / 4) (by positivity)] with n hn hhi hlo hshift hfb
  let U : (Fin n → ObsHistory) → ℝ := fun s =>
    Real.sqrt n * (ordinaryEstimator c s - causalTarget P) / Real.sqrt (sigmaHatSq c s)
  have hmU : Measurable U := by
    dsimp [U]
    fun_prop
  have hm : MeasurableSet {s | nonFallbackSub c s ∧ U s ≤ -z - δ} :=
    (measurableSet_nonFallbackSub c n).inter (measurableSet_le hmU measurable_const)
  have hb := twoSided_coverage_probability_sandwich (sampleLaw P n)
    (nonFallbackSub c) U {s | causalTarget P ∈ subcriticalInterval c alpha s}
    z δ hz.le hδ hm (fun s => mem_subcriticalInterval_iff_studentized c P hP alpha (by omega) s)
  rw [Real.dist_eq] at hhi hlo hshift hfb ⊢
  rw [sub_zero, abs_of_nonneg measureReal_nonneg] at hfb
  rw [abs_lt] at hhi hlo hshift hnorm ⊢
  dsimp only [U] at hb
  constructor <;> linarith [hb.1, hb.2]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

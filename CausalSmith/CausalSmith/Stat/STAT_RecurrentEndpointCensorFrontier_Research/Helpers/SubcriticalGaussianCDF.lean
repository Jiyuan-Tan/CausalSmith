module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceCLT
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalIntervalLength
public import Causalean.Stat.Quantile.CdfConvergence

/-!
# Gaussian CDF assembly for subcritical inference

The actual influence CLT gives oracle CDF convergence. Probability sandwiches
transfer it to the observable studentized statistic, using the already proved
linearization, standard-error consistency, and vanishing fallback mass.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The actual normalized contrast sum is measurable under the sample law. -/
-- @node: aemeasurable_subcriticalInfluence_normalizedSum
lemma aemeasurable_subcriticalInfluence_normalizedSum
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (n : ℕ) :
    AEMeasurable (fun s => (∑ i : Fin n,
      (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
        Real.sqrt n) (sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  apply AEMeasurable.div_const
  exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ =>
    (aemeasurable_subcriticalContrast c P hP hk).comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving)

/-- The influence-sum CDF converges at every threshold to the exact Gaussian CDF. -/
-- @node: subcriticalInfluence_cdf_tendsto
lemma subcriticalInfluence_cdf_tendsto
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (x : ℝ) :
    Tendsto (fun n => (sampleLaw P n).real
      {s | (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
        subcriticalInfluence c P false (s i))) / Real.sqrt n ≤ x}) atTop
      (nhds (cdf (gaussianReal 0 (Real.toNNReal (subcriticalVariance c P))) x)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hv : 0 < Real.toNNReal (subcriticalVariance c P) :=
    Real.toNNReal_pos.mpr (subcriticalVariance_pos c P hP hk)
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ProbabilityMeasure.map (⟨sampleLaw P n, inferInstance⟩ : ProbabilityMeasure (Fin n → ObsHistory))
      (aemeasurable_subcriticalInfluence_normalizedSum c P hP hk n)
  let ν : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (Real.toNNReal (subcriticalVariance c P)), inferInstance⟩
  have hweak : Tendsto νs atTop (nhds ν) := by
    apply (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := νs) (μ := ν)).mpr
    intro f
    exact subcriticalInfluence_normalizedSum_gaussian c P hP hk f f.continuous
      ⟨‖f‖, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  have h := Causalean.Stat.tendsto_cdf_at_of_tendsto hweak
    (Causalean.Stat.continuous_cdf_gaussianReal_zero hv).continuousAt (t := x)
  have heq (n : ℕ) : cdf (νs n : Measure ℝ) x = (sampleLaw P n).real
      {s | (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
        subcriticalInfluence c P false (s i))) / Real.sqrt n ≤ x} := by
    rw [cdf_eq_real]
    exact map_measureReal_apply_of_aemeasurable
      (aemeasurable_subcriticalInfluence_normalizedSum c P hP hk n) measurableSet_Iic
  simp_rw [heq] at h
  exact h

/-- A pathwise CDF sandwich accounts for linearization, studentizer, and
fallback errors without a predictability or independence premise. -/
-- @node: studentized_cdf_probability_sandwich
lemma studentized_cdf_probability_sandwich {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U V D : Ω → ℝ)
    (F : Ω → Prop) (σ z δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ < σ) :
    μ.real {s | V s ≤ z * σ - δ * (1 + |z|)} -
        (μ.real {s | δ < |U s - V s|} +
          μ.real {s | δ < |D s - σ|} + μ.real {s | ¬ F s}) ≤
      μ.real {s | F s ∧ U s / D s ≤ z} ∧
    μ.real {s | F s ∧ U s / D s ≤ z} ≤
      μ.real {s | V s ≤ z * σ + δ * (1 + |z|)} +
        (μ.real {s | δ < |U s - V s|} +
          μ.real {s | δ < |D s - σ|} + μ.real {s | ¬ F s}) := by
  let B := {s | δ < |U s - V s|} ∪
    {s | δ < |D s - σ|} ∪ {s | ¬ F s}
  have hB : μ.real B ≤ μ.real {s | δ < |U s - V s|} +
      μ.real {s | δ < |D s - σ|} + μ.real {s | ¬ F s} :=
    (measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl)
  have hgood (s : Ω) (hs : s ∉ B) :
      |U s - V s| ≤ δ ∧ |D s - σ| ≤ δ ∧ F s := by
    simpa only [B, mem_union, mem_setOf_eq, not_or, not_lt, not_not, and_assoc] using hs
  have hprod (s : Ω) (hs : |D s - σ| ≤ δ) :
      |z * D s - z * σ| ≤ |z| * δ := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg z)
  constructor
  · have hincl : {s | V s ≤ z * σ - δ * (1 + |z|)} ⊆
        {s | F s ∧ U s / D s ≤ z} ∪ B := by
      intro s hs
      by_cases hb : s ∈ B
      · exact Or.inr hb
      · obtain ⟨hu, hd, hf⟩ := hgood s hb
        have hdpos : 0 < D s := by
          have := (abs_le.mp hd).1
          linarith
        refine Or.inl ⟨hf, (div_le_iff₀ hdpos).2 ?_⟩
        have h1 := (abs_le.mp hu).2
        have h2 := (abs_le.mp (hprod s hd)).1
        change V s ≤ z * σ - δ * (1 + |z|) at hs
        nlinarith
    have hm := (measureReal_mono (μ := μ) hincl (by finiteness)).trans
      (measureReal_union_le _ _)
    linarith
  · have hincl : {s | F s ∧ U s / D s ≤ z} ⊆
        {s | V s ≤ z * σ + δ * (1 + |z|)} ∪ B := by
      intro s hs
      by_cases hb : s ∈ B
      · exact Or.inr hb
      · obtain ⟨hu, hd, hf⟩ := hgood s hb
        have hdpos : 0 < D s := by
          have := (abs_le.mp hd).1
          linarith
        have h0 := (div_le_iff₀ hdpos).1 hs.2
        have h1 := (abs_le.mp hu).1
        have h2 := (abs_le.mp (hprod s hd)).2
        exact Or.inl (show V s ≤ z * σ + δ * (1 + |z|) from by nlinarith)
    exact ((measureReal_mono (μ := μ) hincl (by finiteness)).trans
      (measureReal_union_le _ _)).trans (add_le_add le_rfl hB)

/-- Roadmap (44): the actual feasible CDF converges pointwise, including
its nonfallback restriction. -/
-- @node: subcritical_studentized_cdf_tendsto
lemma subcritical_studentized_cdf_tendsto
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (z : ℝ) :
    Tendsto (fun n => (sampleLaw P n).real
      {s | nonFallbackSub c s ∧
        Real.sqrt n * (ordinaryEstimator c s - causalTarget P) /
          Real.sqrt (sigmaHatSq c s) ≤ z}) atTop (nhds (normalCDF z)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let σ := Real.sqrt (subcriticalVariance c P)
  let G : ℝ → ℝ := cdf (gaussianReal 0 (Real.toNNReal (subcriticalVariance c P)))
  have hσ : 0 < σ := Real.sqrt_pos.mpr (subcriticalVariance_pos c P hP hk)
  have hv : 0 < Real.toNNReal (subcriticalVariance c P) :=
    Real.toNNReal_pos.mpr (subcriticalVariance_pos c P hP hk)
  have hG : G (z * σ) = normalCDF z := by
    dsimp only [G]
    rw [Causalean.Stat.cdf_gaussianReal_zero hv,
      Real.coe_toNNReal _ (subcriticalVariance_pos c P hP hk).le]
    rw [mul_div_cancel_right₀ z hσ.ne']
    exact cdf_eq_real _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Causalean.Stat.continuous_cdf_gaussianReal_zero hv).continuousAt
    (ε / 4) (by positivity)
  let δ := min (σ / 2) (η / (2 * (1 + |z|)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδσ : δ < σ := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : δ * (1 + |z|) < η := by
    have h := min_le_right (σ / 2) (η / (2 * (1 + |z|)))
    have hp : 0 < 1 + |z| := by positivity
    have hh : δ * (1 + |z|) ≤ η / 2 := by
      dsimp only [δ]
      calc
        min (σ / 2) (η / (2 * (1 + |z|))) * (1 + |z|) ≤
            (η / (2 * (1 + |z|))) * (1 + |z|) :=
          mul_le_mul_of_nonneg_right h hp.le
        _ = η / 2 := by field_simp
    linarith
  have hnear (a : ℝ) (ha : |a - z * σ| < η) : |G a - normalCDF z| < ε / 4 := by
    have hh := hcont (show dist a (z * σ) < η by simpa [Real.dist_eq] using ha)
    change |G a - G (z * σ)| < ε / 4 at hh
    rw [hG] at hh
    exact hh
  have hminus := hnear (z * σ - δ * (1 + |z|)) (by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity : 0 < δ * (1 + |z|))]
    exact hsmall)
  have hplus := hnear (z * σ + δ * (1 + |z|)) (by
    rw [add_sub_cancel_left, abs_of_pos (by positivity : 0 < δ * (1 + |z|))]
    exact hsmall)
  have hlin := subcritical_ordinaryEstimator_influence_probability_tendsto_zero c P hP hk hδ
  have hse := subcritical_standardError_probability_tendsto_zero c P hP hk hδ
  have hf := nonFallbackSub_compl_probability_tendsto_of_variance_consistency
    c P hP hk (fun e he => sigmaHatSq_probability_tendsto_subcriticalVariance c P hP hk he)
  have herr := (hlin.add hse).add hf
  have hlo := subcriticalInfluence_cdf_tendsto c P hP hk (z * σ - δ * (1 + |z|))
  have hhi := subcriticalInfluence_cdf_tendsto c P hP hk (z * σ + δ * (1 + |z|))
  filter_upwards [(Metric.tendsto_nhds.mp herr) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hlo) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hhi) (ε / 4) (by positivity)] with n hn hnlo hnhi
  have hb := studentized_cdf_probability_sandwich (sampleLaw P n)
    (fun s => Real.sqrt n * (ordinaryEstimator c s - causalTarget P))
    (fun s => (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
      subcriticalInfluence c P false (s i))) / Real.sqrt n)
    (fun s => Real.sqrt (sigmaHatSq c s)) (nonFallbackSub c) σ z δ hσ hδ hδσ
  rw [Real.dist_eq] at hn hnlo hnhi ⊢
  simp only [add_zero, sub_zero] at hn
  rw [abs_lt] at hn hnlo hnhi hminus hplus ⊢
  dsimp only [G] at hminus hplus
  dsimp only [σ] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Roadmap (44), uniformly over thresholds, by the finite-grid monotonicity
argument for the continuous Gaussian CDF. -/
-- @node: subcritical_studentized_cdf_uniform_tendsto
lemma subcritical_studentized_cdf_uniform_tendsto
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) :
    Tendsto (fun n => sSup {d : ℝ | ∃ z : ℝ,
      d = |(sampleLaw P n).real {s | nonFallbackSub c s ∧
        Real.sqrt n * (ordinaryEstimator c s - causalTarget P) /
          Real.sqrt (sigmaHatSq c s) ≤ z} - normalCDF z|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let F : ℕ → ℝ → ℝ := fun n z => (sampleLaw P n).real
    {s | nonFallbackSub c s ∧
      Real.sqrt n * (ordinaryEstimator c s - causalTarget P) /
        Real.sqrt (sigmaHatSq c s) ≤ z}
  have hnormal : normalCDF = Causalean.Mathlib.stdNormalCDF := by
    funext z
    exact (cdf_eq_real _ _).symm
  have hu : TendstoUniformly F normalCDF atTop := by
    apply Causalean.Stat.tendstoUniformly_of_monotone_of_tendsto_at
    · intro n x y hxy
      exact measureReal_mono (fun s hs => ⟨hs.1, hs.2.trans hxy⟩) (by finiteness)
    · intro n z; exact measureReal_nonneg
    · intro n z; exact measureReal_le_one
    · rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_monotone
    · rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_continuous
    · rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_tendsto_atBot
    · rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_tendsto_atTop
    · exact subcritical_studentized_cdf_tendsto c P hP hk
  have hb (n : ℕ) : BddAbove {d : ℝ | ∃ z : ℝ, d = |F n z - normalCDF z|} := by
    refine ⟨1, ?_⟩
    rintro d ⟨z, rfl⟩
    rw [abs_le]
    have hf0 : 0 ≤ F n z := measureReal_nonneg
    have hf1 : F n z ≤ 1 := measureReal_le_one
    have hn0 : 0 ≤ normalCDF z := by rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_nonneg z
    have hn1 : normalCDF z ≤ 1 := by rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_le_one z
    constructor <;> linarith
  have hnon (n : ℕ) : Set.Nonempty {d : ℝ | ∃ z : ℝ, d = |F n z - normalCDF z|} :=
    ⟨_, 0, rfl⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε)] with n hn
  have hl : 0 ≤ sSup {d : ℝ | ∃ z : ℝ, d = |F n z - normalCDF z|} :=
    (abs_nonneg _).trans (le_csSup (hb n) (show
      |F n 0 - normalCDF 0| ∈ {d : ℝ | ∃ z : ℝ, d = |F n z - normalCDF z|} from ⟨0, rfl⟩))
  have hh : sSup {d : ℝ | ∃ z : ℝ, d = |F n z - normalCDF z|} ≤ ε / 2 := by
    apply csSup_le (hnon n)
    rintro d ⟨z, rfl⟩
    have hz := hn z
    rw [Real.dist_eq, abs_sub_comm] at hz
    exact hz.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hl]
  exact hh.trans_lt (by linarith)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

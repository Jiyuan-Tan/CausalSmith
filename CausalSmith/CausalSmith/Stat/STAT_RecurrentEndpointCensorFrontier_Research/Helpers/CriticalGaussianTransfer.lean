module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalWitnessProbability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRelativeVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalGaussianCDF

/-!
# Critical Gaussian distribution transfer

The probability sandwich transfers the conditional recurrence Gaussian limit to
observable studentization along arbitrary triangular laws. The numerator and
denominator errors and fallback probabilities are already proved from the model.
The recurrence Gaussian limit is an explicit input to these assembly lemmas;
this file does not claim to prove roadmap (19).
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Critical rescaling cancels in the feasible ratio for positive sample scale. -/
-- @node: critical_studentized_rescaling_eq
lemma critical_studentized_rescaling_eq (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) (s : Fin n → ObsHistory) :
    (Real.sqrt ((n : ℝ) / Real.log n) *
        (observableEstimator c s - causalTarget P) / Real.sqrt (criticalVariance c P)) /
      (Real.sqrt ((n : ℝ) / Real.log n) * Real.sqrt (criticalVarianceEstimator c s) /
        Real.sqrt (criticalVariance c P)) =
      (observableEstimator c s - causalTarget P) / Real.sqrt (criticalVarianceEstimator c s) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlpos : 0 < Real.log (n : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_log_sampleSize hn)
  have hs := (Real.sqrt_pos.mpr (div_pos hnpos hlpos)).ne'
  have hv := (Real.sqrt_pos.mpr (criticalVariance_pos c P hP)).ne'
  by_cases hd : Real.sqrt (criticalVarianceEstimator c s) = 0
  · simp [hd]
  · field_simp

/-- The recurrence CDF limit, once proved, transfers to the actual studentized
CDF using the proved remainder, relative variance, and fallback estimates. -/
-- @node: critical_studentized_cdf_tendsto_of_recurrence
lemma critical_studentized_cdf_tendsto_of_recurrence
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n))
    (hrec : ∀ x : ℝ, Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      Real.sqrt ((n : ℝ) / Real.log n) *
        (recurrenceError c (Pseq n) true s (bandwidth c n) -
          recurrenceError c (Pseq n) false s (bandwidth c n)) /
        Real.sqrt (criticalVariance c (Pseq n)) ≤ x}) atTop (nhds (normalCDF x)))
    (z : ℝ) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z}) atTop (nhds (normalCDF z)) := by
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI (n : ℕ) : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  let U := fun n (s : Fin n → ObsHistory) => Real.sqrt ((n : ℝ) / Real.log n) *
    (observableEstimator c s - causalTarget (Pseq n)) / Real.sqrt (criticalVariance c (Pseq n))
  let V := fun n (s : Fin n → ObsHistory) => Real.sqrt ((n : ℝ) / Real.log n) *
    (recurrenceError c (Pseq n) true s (bandwidth c n) -
      recurrenceError c (Pseq n) false s (bandwidth c n)) / Real.sqrt (criticalVariance c (Pseq n))
  let D := fun n (s : Fin n → ObsHistory) => Real.sqrt ((n : ℝ) / Real.log n) *
    Real.sqrt (criticalVarianceEstimator c s) / Real.sqrt (criticalVariance c (Pseq n))
  have hnormal : normalCDF = Causalean.Mathlib.stdNormalCDF := by
    funext x; exact (cdf_eq_real _ _).symm
  have hcont : ContinuousAt normalCDF z := by
    rw [hnormal]; exact Causalean.Mathlib.stdNormalCDF_continuous.continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hnear⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
  let δ := min (1 / 2 : ℝ) (η / (2 * (1 + |z|)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : δ * (1 + |z|) < η := by
    have hp : 0 < 1 + |z| := by positivity
    have hh : δ * (1 + |z|) ≤ η / 2 := by
      calc
        _ ≤ (η / (2 * (1 + |z|))) * (1 + |z|) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
        _ = η / 2 := by field_simp
    linarith
  have hminus : |normalCDF (z - δ * (1 + |z|)) - normalCDF z| < ε / 4 := by
    apply hnear
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity : 0 < δ * (1 + |z|))]
    exact hsmall
  have hplus : |normalCDF (z + δ * (1 + |z|)) - normalCDF z| < ε / 4 := by
    apply hnear
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity : 0 < δ * (1 + |z|))]
    exact hsmall
  have hlin : Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | δ < |U n s - V n s|}) atTop (nhds 0) := by
    convert critical_standardized_recurrence_approximation_triangular_tendsto_zero c hk Pseq hP hδ using 1
    funext n
    congr 1
    ext s
    dsimp [U, V]
    congr 2
    ring
  have hse := critical_relative_standardError_triangular_tendsto_zero c hk Pseq hP hδ
  have hf := nonFallback_compl_triangular_tendsto_of_early_witness c Pseq hP
  have herr := (hlin.add hse).add hf
  have hlo := hrec (z - δ * (1 + |z|))
  have hhi := hrec (z + δ * (1 + |z|))
  filter_upwards [(Metric.tendsto_nhds.mp herr) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hlo) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hhi) (ε / 4) (by positivity), eventually_ge_atTop 3]
    with n hn hnlo hnhi hn3
  have hb := studentized_cdf_probability_sandwich (sampleLaw (Pseq n) n)
    (U n) (V n) (D n) (nonFallback c) 1 z δ (by norm_num) hδ hδ1
  have heq : (fun s => nonFallback c s ∧ U n s / D n s ≤ z) =
      (fun s => nonFallback c s ∧ (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z) := by
    funext s
    dsimp only [U, D]
    rw [critical_studentized_rescaling_eq c (Pseq n) (hP n) hn3]
  rw [heq] at hb
  simp only [mul_one] at hb
  rw [Real.dist_eq] at hn hnlo hnhi ⊢
  simp only [add_zero, sub_zero] at hn
  rw [abs_lt] at hn hnlo hnhi hminus hplus ⊢
  dsimp only [V, D] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- The finite-grid argument upgrades the feasible pointwise triangular limit
without a new CLT or measurability premise. -/
-- @node: critical_studentized_cdf_uniform_tendsto_of_pointwise
lemma critical_studentized_cdf_uniform_tendsto_of_pointwise
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hpoint : ∀ z : ℝ, Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | nonFallback c s ∧ (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z}) atTop (nhds (normalCDF z))) :
    Tendsto (fun n => sSup {d : ℝ | ∃ z : ℝ,
      d = |(sampleLaw (Pseq n) n).real {s | nonFallback c s ∧
        (observableEstimator c s - causalTarget (Pseq n)) /
          Real.sqrt (criticalVarianceEstimator c s) ≤ z} - normalCDF z|}) atTop (nhds 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI (n : ℕ) : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  let F : ℕ → ℝ → ℝ := fun n z => (sampleLaw (Pseq n) n).real
    {s | nonFallback c s ∧
      (observableEstimator c s - causalTarget (Pseq n)) /
        Real.sqrt (criticalVarianceEstimator c s) ≤ z}
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
    · exact hpoint
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

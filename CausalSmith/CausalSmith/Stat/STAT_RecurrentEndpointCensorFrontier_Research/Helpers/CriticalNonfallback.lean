module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVarianceBounds

/-!
# Critical nonfallback transfer along triangular sequences

Uniform overlap controls the empty arms even when the subject law changes with
sample size. The uniform variance floor then converts critical variance
consistency into vanishing fallback probability. This transfer does not supply
variance consistency or the stronger exponential fallback bound needed for the
expected interval length.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The empty-arm probability has a geometric bound independent of the subject law. -/
-- @node: armSize_zero_probability_uniform_le
lemma armSize_zero_probability_uniform_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (sampleLaw P n).real {s | armSize a s = 0} ≤ (1 - c.pMin) ^ n := by
  rw [armSize_zero_probability c P hP a]
  have hp := modelClass_assignment_probability_bounds c P hP a
  exact pow_le_pow_left₀ (sub_nonneg.mpr hp.2) (sub_le_sub_left hp.1 1) n

/-- Empty-arm probability vanishes along every triangular model-class sequence. -/
-- @node: armSize_zero_probability_triangular_tendsto_zero
lemma armSize_zero_probability_triangular_tendsto_zero
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | armSize a s = 0})
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 - c.pMin) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [c.pMin_le])
      (by linarith [c.pMin_pos])
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => armSize_zero_probability_uniform_le c (Pseq n) (hP n) a n) hpow

/-- With both arms present, critical fallback forces a fixed-size normalized
variance error, using a uniform population variance floor. -/
-- @node: nonFallback_compl_subset_critical_variance_error
lemma nonFallback_compl_subset_critical_variance_error (c : ClassConstants)
    {vmin v : ℝ} (hvmin : 0 < vmin) (hv : vmin ≤ v) {n : ℕ} (hn : 3 ≤ n) :
    {s : Fin n → ObsHistory | ¬ nonFallback c s} ⊆
      {s | armSize false s = 0} ∪ {s | armSize true s = 0} ∪
        {s | vmin / 2 < |(n : ℝ) * criticalVarianceEstimator c s / Real.log n - v|} := by
  intro s hs
  by_cases hf : armSize false s = 0
  · exact Or.inl (Or.inl hf)
  by_cases ht : armSize true s = 0
  · exact Or.inl (Or.inr ht)
  apply Or.inr
  have hbad : criticalVarianceEstimator c s ≤ 0 := by
    by_contra h
    exact hs ⟨Nat.pos_of_ne_zero hf, Nat.pos_of_ne_zero ht, lt_of_not_ge h⟩
  have hscaled : (n : ℝ) * criticalVarianceEstimator c s / Real.log n ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hbad)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_log_sampleSize hn))
  change vmin / 2 < |(n : ℝ) * criticalVarianceEstimator c s / Real.log n - v|
  rw [abs_of_nonpos (by linarith :
    (n : ℝ) * criticalVarianceEstimator c s / Real.log n - v ≤ 0)]
  linarith

/-- A union bound controls critical fallback by empty arms and normalized variance error. -/
-- @node: nonFallback_compl_probability_le_critical_variance_error
lemma nonFallback_compl_probability_le_critical_variance_error
    (c : ClassConstants) (P : SubjectLaw) {vmin : ℝ} (hvmin : 0 < vmin)
    (hv : vmin ≤ criticalVariance c P) {n : ℕ} (hn : 3 ≤ n) :
    (sampleLaw P n).real {s | ¬ nonFallback c s} ≤
      (sampleLaw P n).real {s | armSize false s = 0} +
      (sampleLaw P n).real {s | armSize true s = 0} +
      (sampleLaw P n).real {s | vmin / 2 <
        |(n : ℝ) * criticalVarianceEstimator c s / Real.log n - criticalVariance c P|} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  exact (measureReal_mono
    (nonFallback_compl_subset_critical_variance_error c hvmin hv hn)
    (by finiteness)).trans ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl))

/-- Critical variance consistency implies vanishing fallback uniformly in the
sequential sense. Consistency remains a separate proof obligation. -/
-- @node: nonFallback_compl_triangular_tendsto_of_critical_variance_consistency
lemma nonFallback_compl_triangular_tendsto_of_critical_variance_consistency
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, CriticalScope c (Pseq n))
    (hvar : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < |(n : ℝ) * criticalVarianceEstimator c s /
        Real.log n - criticalVariance c (Pseq n)|}) atTop (nhds 0)) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | ¬ nonFallback c s})
      atTop (nhds 0) := by
  obtain ⟨vmin, vmax, hvmin, _, hb⟩ := criticalVariance_uniform_non_degenerate c
  have hsum := ((armSize_zero_probability_triangular_tendsto_zero c Pseq
    (fun n => (hP n).modelClass) false).add
    (armSize_zero_probability_triangular_tendsto_zero c Pseq
      (fun n => (hP n).modelClass) true)).add (hvar (vmin / 2) (half_pos hvmin))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa using hsum)
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact nonFallback_compl_probability_le_critical_variance_error c (Pseq n)
    hvmin (hb (Pseq n) (hP n)).1 hn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

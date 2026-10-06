module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathSubcriticalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ProjectionInactivity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSubcriticalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalExtinction

/-!
# Consistency and inactive projection for the ordinary estimator

Roadmap (20)--(23), (27): the exact decomposition and the derived recurrence,
death, and extinction bounds imply consistency of the raw ordinary arm mean.
The strict interior arm means then make projection inactive in probability.
This establishes consistency without assuming the influence expansion.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Root-n negligibility of extinction implies its unscaled consistency. -/
-- @node: subcritical_extinctionError_zero_probability_tendsto_zero
lemma subcritical_extinctionError_zero_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |extinctionError c P a s 0|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (subcritical_extinctionError_rootn_probability_tendsto_zero c P hP hk a hε)
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  change ε < |extinctionError c P a s 0| at hs
  change ε < |Real.sqrt n * extinctionError c P a s 0|
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hs.trans_le (le_mul_of_one_le_left (abs_nonneg _)
    (Real.one_le_sqrt.mpr (by exact_mod_cast hn)))

/-- At zero cutoff the exact decomposition is the ordinary arm-mean error. -/
-- @node: ordinaryMuTilde_error_decomposition_ae
lemma ordinaryMuTilde_error_decomposition_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (fun s : Fin n → ObsHistory => ordinaryMuTilde a s - armMean P a) =ᵐ[sampleLaw P n]
      (fun s => recurrenceError c P a s 0 - deathError c P a s 0 -
        extinctionError c P a s 0) := by
  have he := (exact_error_decomposition c P hP.iid hP.randomAssignment
    hP.poissonRecurrence hP.deathHazard hP.recurrenceDeathIndependence
    hP.independentCensoring hP.deathBounds hP.assignmentLaw).1 n hn
  filter_upwards [he] with s hs
  have h := hs a 0 (by norm_num) (by exact div_nonneg c.x0_pos.le (by norm_num))
  simpa [ordinaryMuTilde, muTildeAt, truncatedMean, armMean, continuationWeight] using h

/-- The actual ordinary raw arm estimator is consistent, assembled from its
three stochastic error components rather than an assumed oracle expansion. -/
-- @node: subcritical_ordinaryMuTilde_probability_tendsto_zero
lemma subcritical_ordinaryMuTilde_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |ordinaryMuTilde a s - armMean P a|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hδ : 0 < ε / 3 := by positivity
  have hlim := ((subcritical_recurrenceError_zero_probability_tendsto_zero c P hP hk a hδ).add
    (subcritical_deathError_zero_probability_tendsto_zero c P hP hk a hδ)).add
      (subcritical_extinctionError_zero_probability_tendsto_zero c P hP hk a hδ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hlim)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let A : Set (Fin n → ObsHistory) := {s | ε / 3 < |recurrenceError c P a s 0|}
  let B : Set (Fin n → ObsHistory) := {s | ε / 3 < |deathError c P a s 0|}
  let C : Set (Fin n → ObsHistory) := {s | ε / 3 < |extinctionError c P a s 0|}
  have hsub : ∀ᵐ s ∂sampleLaw P n,
      ε < |ordinaryMuTilde a s - armMean P a| → s ∈ (A ∪ B) ∪ C := by
    filter_upwards [ordinaryMuTilde_error_decomposition_ae c P hP a hn] with s hs
    intro ht
    change ε < |ordinaryMuTilde a s - armMean P a| at ht
    rw [hs] at ht
    by_contra hnot
    have hR : |recurrenceError c P a s 0| ≤ ε / 3 := by
      simpa [A, B, C, not_or, not_lt] using (not_or.mp (not_or.mp hnot).1).1
    have hD : |deathError c P a s 0| ≤ ε / 3 := by
      simpa [A, B, C, not_or, not_lt] using (not_or.mp (not_or.mp hnot).1).2
    have hE : |extinctionError c P a s 0| ≤ ε / 3 := by
      simpa [A, B, C, not_lt] using (not_or.mp hnot).2
    have hb := (abs_sub (recurrenceError c P a s 0 - deathError c P a s 0)
      (extinctionError c P a s 0)).trans
        (add_le_add (abs_sub (recurrenceError c P a s 0) (deathError c P a s 0)) le_rfl)
    linarith
  calc
    _ ≤ (sampleLaw P n).real ((A ∪ B) ∪ C) :=
      ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
    _ ≤ (sampleLaw P n).real (A ∪ B) + (sampleLaw P n).real C := measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_union_le A B) le_rfl

/-- The ordinary contrast projection is inactive with probability tending to
one because both true arm means lie strictly inside the projection range. -/
-- @node: subcritical_projectionActivity_probability_tendsto_zero
lemma subcritical_projectionActivity_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ordinaryEstimator c s ≠ ordinaryMuTilde true s - ordinaryMuTilde false s})
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let δ := fun a => min (armMean P a) (c.lambdaMax - armMean P a)
  have hδ (a : Arm) : 0 < δ a :=
    lt_min (armMean_mem_projectionInterior c P hP a).1
      (sub_pos.mpr (armMean_mem_projectionInterior c P hP a).2)
  have hlim := (subcritical_ordinaryMuTilde_probability_tendsto_zero c P hP hk true
    (half_pos (hδ true))).add
      (subcritical_ordinaryMuTilde_probability_tendsto_zero c P hP hk false
        (half_pos (hδ false)))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hlim)
  apply Eventually.of_forall
  intro n
  apply (projectionActivity_probability_le_armBoundaryTails c P hP n).trans
  apply add_le_add <;> apply measureReal_mono _ (by finiteness)
  · intro s hs
    exact (half_lt_self (hδ true)).trans_le hs
  · intro s hs
    exact (half_lt_self (hδ false)).trans_le hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier


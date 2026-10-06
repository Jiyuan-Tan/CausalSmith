module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxUpperRisk
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform probability of continued projection activity

Roadmap (25): the uniform interior margin and the proved finite-sample arm
risk imply that clipping changes the continued contrast with probability
vanishing along every triangular model sequence. An active projection puts
the projected arm estimate on a boundary, so its own squared risk suffices;
no new moment premise on the unprojected estimator is needed.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An active projection has projected error at least the interior margin. -/
-- @node: projectArm_error_ge_margin_of_active
lemma projectArm_error_ge_margin_of_active (c : ClassConstants) {x m δ : ℝ}
    (hm : δ ≤ m ∧ δ ≤ c.lambdaMax - m) (ha : projectArm c x ≠ x) :
    δ ≤ |projectArm c x - m| := by
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  by_cases hx : x < 0
  · have he : projectArm c x = 0 := by
      simp [projectArm, min_eq_right (hx.le.trans hL), max_eq_left hx.le]
    rw [he, zero_sub, abs_neg]
    exact hm.1.trans (le_abs_self m)
  · by_cases hy : c.lambdaMax < x
    · have he : projectArm c x = c.lambdaMax := by
        simp [projectArm, min_eq_left hy.le, max_eq_right hL]
      rw [he]
      exact hm.2.trans (le_abs_self _)
    · exact (ha (projectArm_eq_self c ⟨le_of_not_gt hx, le_of_not_gt hy⟩)).elim

/-- Activity of the contrast is contained in the projected arm boundary tails. -/
-- @node: continuedProjectionActivity_subset_projected_tails
lemma continuedProjectionActivity_subset_projected_tails (c : ClassConstants)
    (P : SubjectLaw) {δ : ℝ}
    (hm : ∀ a : Arm, δ ≤ armMean P a ∧ δ ≤ c.lambdaMax - armMean P a) (n : ℕ) :
    {s : Fin n → ObsHistory | observableEstimator c s ≠
      muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s} ⊆
    {s | δ ≤ |muHatAt c (bandwidth c n) true s - armMean P true|} ∪
    {s | δ ≤ |muHatAt c (bandwidth c n) false s - armMean P false|} := by
  intro s hs
  by_cases ht : projectArm c (muTildeAt c (bandwidth c n) true s) =
      muTildeAt c (bandwidth c n) true s
  · have hf : projectArm c (muTildeAt c (bandwidth c n) false s) ≠
        muTildeAt c (bandwidth c n) false s := by
      intro hf
      exact hs (by simp only [observableEstimator, muHatAt, ht, hf])
    exact Or.inr (projectArm_error_ge_margin_of_active c (hm false) hf)
  · exact Or.inl (projectArm_error_ge_margin_of_active c (hm true) ht)

/-- Markov's inequality bounds each projected arm tail by its squared risk. -/
-- @node: muHatAt_boundary_tail_le_sqRisk
lemma muHatAt_boundary_tail_le_sqRisk (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (h : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (sampleLaw P n).real {s | δ ≤ |muHatAt c h a s - armMean P a|} ≤
      Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c h a) (armMean P a) / δ ^ 2 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have he : {s : Fin n → ObsHistory | δ ≤ |muHatAt c h a s - armMean P a|} =
      {s | δ ^ 2 ≤ (muHatAt c h a s - armMean P a) ^ 2} := by
    ext s
    exact (sq_le_sq₀ hδ.le (abs_nonneg _)).symm.trans (by simp only [sq_abs, Set.mem_ofPred_eq])
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      sq_nonneg (muHatAt c h a s - armMean P a)))
    (integrable_muHatAt_sq_loss c P hP a n h) (δ ^ 2)
  simpa only [Causalean.Stat.sqRisk, mul_comm] using hb

/-- A law-independent finite-n risk envelope controls projection activity. -/
-- @node: continuedProjectionActivity_probability_le_riskScale
lemma continuedProjectionActivity_probability_le_riskScale (c : ClassConstants) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ n : ℕ, 3 ≤ n →
      (sampleLaw P n).real {s : Fin n → ObsHistory | observableEstimator c s ≠
        muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s} ≤
          C * riskScale c n := by
  obtain ⟨δ, hδ, hm⟩ := armMean_uniform_projection_margin c
  let K := explicitBiasRisk c + explicitVarianceRisk c * varianceRateEnvelope c +
    explicitExtinctionRisk c * max (extinctionPreEnvelope c) (extinctionTailEnvelope c)
  refine ⟨2 * (|K| + 1) / δ ^ 2, by positivity, ?_⟩
  intro P hP n hn
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hb (a : Arm) : (sampleLaw P n).real
      {s | δ ≤ |muHatAt c (bandwidth c n) a s - armMean P a|} ≤
        (|K| + 1) * riskScale c n / δ ^ 2 := by
    apply (muHatAt_boundary_tail_le_sqRisk c P hP a n (bandwidth c n) hδ).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg δ)
    exact (muHat_bandwidth_sqRisk_le_envelope c P hP a n hn).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (riskScale_pos c hn).le)
  calc
    _ ≤ (sampleLaw P n).real
        ({s | δ ≤ |muHatAt c (bandwidth c n) true s - armMean P true|} ∪
         {s | δ ≤ |muHatAt c (bandwidth c n) false s - armMean P false|}) :=
      measureReal_mono (continuedProjectionActivity_subset_projected_tails c P (hm P hP) n)
        (by finiteness)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ (|K| + 1) * riskScale c n / δ ^ 2 +
        (|K| + 1) * riskScale c n / δ ^ 2 := add_le_add (hb true) (hb false)
    _ = _ := by ring

/-- The critical risk scale tends to zero. -/
-- @node: critical_riskScale_tendsto_zero
lemma critical_riskScale_tendsto_zero (c : ClassConstants) (hk : c.kappa = 1) :
    Tendsto (riskScale c) atTop (nhds 0) := by
  have ht := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun n => riskScale c n) atTop (nhds 0)
  simpa [riskScale, hk, Function.comp_def] using ht

/-- Uniform projection inactivity along arbitrary triangular critical laws. -/
-- @node: continuedProjectionActivity_critical_triangular_tendsto_zero
lemma continuedProjectionActivity_critical_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s : Fin n → ObsHistory |
      observableEstimator c s ≠ muTildeAt c (bandwidth c n) true s -
        muTildeAt c (bandwidth c n) false s}) atTop (nhds 0) := by
  obtain ⟨C, _, hb⟩ := continuedProjectionActivity_probability_le_riskScale c
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa using (critical_riskScale_tendsto_zero c hk).const_mul C)
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact hb (Pseq n) (hP n) n hn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

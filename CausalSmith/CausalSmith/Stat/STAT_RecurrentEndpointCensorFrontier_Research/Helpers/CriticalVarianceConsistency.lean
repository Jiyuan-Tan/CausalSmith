module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalOracleLimit
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPredictableIntegrated
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationLocalization

/-!
# Observable critical variance consistency

The integrated survival and relative-risk comparisons close the stochastic
predictable-variation limit in roadmap (15). The deterministic oracle limit
provides its exact critical coefficient. Finally the proved observable
optional-minus-predictable fluctuation limit (29) gives (30) for the actual
variance estimator, along arbitrary triangular model-law sequences.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The genuine two-arm predictable recurrence energy, before logarithmic
normalization, retaining the sample's KM estimator and risk sets. -/
-- @node: criticalPredictableEnergy
noncomputable def criticalPredictableEnergy (c : ClassConstants) (P : SubjectLaw)
    (n : ℕ) (s : Fin n → ObsHistory) : ℝ :=
  ∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
    recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * P.lam a t

/-- Summing the two armwise integrated comparisons gives vanishing
predictable-minus-oracle error in probability at the logarithmic scale. -/
-- @node: critical_predictable_oracle_error_triangular_tendsto_zero
lemma critical_predictable_oracle_error_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s -
        criticalOracleEnergy c (Pseq n) n) / Real.log n|}) atTop (nhds 0) := by
  have h0 := critical_predictable_arm_oracle_error_triangular_tendsto_zero
    c hk Pseq hP false (half_pos hε)
  have h1 := critical_predictable_arm_oracle_error_triangular_tendsto_zero
    c hk Pseq hP true (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using h0.add h1)
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply le_trans (measureReal_mono ?_ (by finiteness)) (measureReal_union_le _ _)
  intro s hs
  by_contra hne
  have hb := not_or.mp hne
  simp only [Set.mem_setOf_eq] at hb
  have hb0 := le_of_not_gt hb.1
  have hb1 := le_of_not_gt hb.2
  have hor (a : Arm) :
      (∫ t in (0 : ℝ)..(1 - bandwidth c n),
        continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
          survival (Pseq n) a t * (Pseq n).lam a t /
            ((Pseq n).p a * retention (Pseq n) a t)) =
      (∫ t in (0 : ℝ)..(1 - bandwidth c n),
        continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
          survival (Pseq n) a t * (Pseq n).lam a t / retention (Pseq n) a t) /
        (Pseq n).p a := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hor false] at hb0
  rw [hor true] at hb1
  let R := fun a : Arm => ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
    recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * (Pseq n).lam a t
  let O := fun a : Arm => (∫ t in (0 : ℝ)..(1 - bandwidth c n),
    continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
      survival (Pseq n) a t * (Pseq n).lam a t / retention (Pseq n) a t) / (Pseq n).p a
  change |((n : ℝ) * R false - O false) / Real.log n| ≤ ε / 2 at hb0
  change |((n : ℝ) * R true - O true) / Real.log n| ≤ ε / 2 at hb1
  have htri := abs_add_le (((n : ℝ) * R false - O false) / Real.log n)
    (((n : ℝ) * R true - O true) / Real.log n)
  have he : ((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s -
      criticalOracleEnergy c (Pseq n) n) / Real.log n =
      ((n : ℝ) * R false - O false) / Real.log n +
      ((n : ℝ) * R true - O true) / Real.log n := by
    simp only [criticalPredictableEnergy, criticalOracleEnergy, Fintype.sum_bool]
    dsimp [R, O]
    ring
  change ε < |_ / Real.log n| at hs
  rw [he] at hs
  linarith

/-- Roadmap (15): the actual predictable energy has the exact law's critical
variance limit, using the deterministic oracle coefficient and the stochastic
integrated comparison rather than a variance premise. -/
-- @node: critical_predictable_variance_triangular_tendsto_zero
lemma critical_predictable_variance_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |(n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n -
        criticalVariance c (Pseq n)|}) atTop (nhds 0) := by
  have he := critical_predictable_oracle_error_triangular_tendsto_zero
    c hk Pseq hP (half_pos hε)
  have hd := (criticalOracleEnergy_triangular_tendsto c hk Pseq hP).abs
  have hev := hd.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε / 2 by simpa using half_pos hε))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ he
  filter_upwards [hev] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  change ε / 2 < |_ / Real.log n|
  have htri := abs_add_le
    (((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s -
      criticalOracleEnergy c (Pseq n) n) / Real.log n)
    (criticalOracleEnergy c (Pseq n) n / Real.log n - criticalVariance c (Pseq n))
  have heq : (n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n -
      criticalVariance c (Pseq n) =
      ((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s -
        criticalOracleEnergy c (Pseq n) n) / Real.log n +
      (criticalOracleEnergy c (Pseq n) n / Real.log n - criticalVariance c (Pseq n)) := by ring
  change ε < |_ - criticalVariance c (Pseq n)| at hs
  rw [heq] at hs
  change |_ - criticalVariance c (Pseq n)| < ε / 2 at hn
  linarith

/-- Roadmap (30): the fully observable critical variance estimator is
consistent at scale n/log n, by predictable consistency and the proved
optional-minus-predictable fluctuation limit. -/
-- @node: critical_variance_estimator_triangular_tendsto_zero
lemma critical_variance_estimator_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |(n : ℝ) * criticalVarianceEstimator c s / Real.log n -
        criticalVariance c (Pseq n)|}) atTop (nhds 0) := by
  have ho := critical_total_variance_error_triangular_tendsto_zero
    c hk Pseq hP (half_pos hε)
  have hp := critical_predictable_variance_triangular_tendsto_zero
    c hk Pseq hP (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ho.add hp)
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply le_trans (measureReal_mono ?_ (by finiteness)) (measureReal_union_le _ _)
  intro s hs
  by_contra hne
  have hb := not_or.mp hne
  simp only [Set.mem_setOf_eq] at hb
  have hb0 := le_of_not_gt hb.1
  have hb1 := le_of_not_gt hb.2
  change |((n : ℝ) / Real.log n) *
    (criticalVarianceEstimator c s - criticalPredictableEnergy c (Pseq n) n s)| ≤ ε / 2 at hb0
  have htri := abs_add_le
    (((n : ℝ) / Real.log n) *
      (criticalVarianceEstimator c s - criticalPredictableEnergy c (Pseq n) n s))
    ((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n -
      criticalVariance c (Pseq n))
  have heq : (n : ℝ) * criticalVarianceEstimator c s / Real.log n - criticalVariance c (Pseq n) =
    ((n : ℝ) / Real.log n) *
      (criticalVarianceEstimator c s - criticalPredictableEnergy c (Pseq n) n s) +
    ((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n -
      criticalVariance c (Pseq n)) := by ring
  change ε < |_ - criticalVariance c (Pseq n)| at hs
  rw [heq] at hs
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

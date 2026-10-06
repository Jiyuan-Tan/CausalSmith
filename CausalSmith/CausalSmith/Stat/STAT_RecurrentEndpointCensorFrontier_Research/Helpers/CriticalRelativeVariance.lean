module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalIntervalLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceApproximation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVarianceConsistency

/-!
# Relative critical variance and studentizer control

The model's positive variance floor turns the proved absolute limits (15) and
(30) into unit-variance probability limits for the conditional Poisson CLT.
Taking square roots supplies the denominator control required by Slutsky;
the actual recurrence approximation is also standardized by the same floor.
No Gaussian limit is assumed or proved in this module.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A uniformly positive critical variance permits division in triangular
probability limits, even though the model law changes with the sample size. -/
-- @node: critical_negligible_div_variance_triangular
lemma critical_negligible_div_variance_triangular
    (c : ClassConstants) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n))
    (X : (n : ℕ) → (Fin n → ObsHistory) → ℝ)
    (hX : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | δ < |X n s|}) atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < |X n s / criticalVariance c (Pseq n)|}) atTop (nhds 0) := by
  let v := 2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)
  have hv : 0 < v := by
    dsimp [v]
    exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos)
        (c.gMin_pos.trans c.gMin_lt))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (hX (ε * v) (mul_pos hε hv))
  apply Eventually.of_forall
  intro n
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  have hV := criticalVariance_pos c (Pseq n) (hP n)
  have hfloor : v ≤ criticalVariance c (Pseq n) :=
    criticalVariance_uniform_lower c (Pseq n) (hP n)
  change ε < |X n s / criticalVariance c (Pseq n)| at hs
  rw [abs_div, abs_of_pos hV] at hs
  change ε * v < |X n s|
  exact (mul_le_mul_of_nonneg_left hfloor hε.le).trans_lt ((lt_div_iff₀ hV).mp hs)

/-- The conditional recurrence energy normalized by the exact moving model
variance converges to one, the variance input in roadmap (19). -/
-- @node: critical_predictable_relative_variance_triangular_tendsto_zero
lemma critical_predictable_relative_variance_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n) /
        criticalVariance c (Pseq n) - 1|}) atTop (nhds 0) := by
  have h := critical_negligible_div_variance_triangular c Pseq hP
    (fun n s => (n : ℝ) * criticalPredictableEnergy c (Pseq n) n s / Real.log n -
      criticalVariance c (Pseq n))
    (fun _ hδ => critical_predictable_variance_triangular_tendsto_zero c hk Pseq hP hδ) hε
  convert h using 1
  funext n
  congr 1
  ext s
  have hv := (criticalVariance_pos c (Pseq n) (hP n)).ne'
  simp only [Set.mem_ofPred_eq, sub_div, div_self hv]

/-- The fully observable variance has vanishing relative error, by (30)
and the positive floor (16), without an extra variance-consistency premise. -/
-- @node: critical_observable_relative_variance_triangular_tendsto_zero
lemma critical_observable_relative_variance_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) * criticalVarianceEstimator c s / Real.log n) /
        criticalVariance c (Pseq n) - 1|}) atTop (nhds 0) := by
  have h := critical_negligible_div_variance_triangular c Pseq hP
    (fun n s => (n : ℝ) * criticalVarianceEstimator c s / Real.log n -
      criticalVariance c (Pseq n))
    (fun _ hδ => critical_variance_estimator_triangular_tendsto_zero c hk Pseq hP hδ) hε
  convert h using 1
  funext n
  congr 1
  ext s
  have hv := (criticalVariance_pos c (Pseq n) (hP n)).ne'
  simp only [Set.mem_ofPred_eq, sub_div, div_self hv]

/-- Square-root error relative to one is bounded by variance error; this
uses the nonnegative square root and its squared identity. -/
-- @node: critical_sqrt_sub_one_abs_le
lemma critical_sqrt_sub_one_abs_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.sqrt x - 1| ≤ |x - 1| := by
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  by_cases h : 1 ≤ Real.sqrt x
  · rw [abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x - 1),
      abs_of_nonneg (by nlinarith : 0 ≤ x - 1)]
    nlinarith
  · have h' := le_of_not_ge h
    rw [abs_of_nonpos (by linarith : Real.sqrt x - 1 ≤ 0),
      abs_of_nonpos (by nlinarith : x - 1 ≤ 0)]
    nlinarith

/-- The actual standard error divided by its oracle critical scale converges
to one in probability, the denominator input to the roadmap's Slutsky step. -/
-- @node: critical_relative_standardError_triangular_tendsto_zero
lemma critical_relative_standardError_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      ε < |Real.sqrt ((n : ℝ) / Real.log n) * Real.sqrt (criticalVarianceEstimator c s) /
        Real.sqrt (criticalVariance c (Pseq n)) - 1|}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_observable_relative_variance_triangular_tendsto_zero c hk Pseq hP hε)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : 0 ≤ Real.log (n : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_log_sampleSize hn)
  have hv := criticalVariance_pos c (Pseq n) (hP n)
  apply measureReal_mono _ (by finiteness)
  intro s hs
  have hx : 0 ≤ ((n : ℝ) * criticalVarianceEstimator c s / Real.log n) /
      criticalVariance c (Pseq n) := by
    exact div_nonneg (div_nonneg (mul_nonneg hn0 (criticalVarianceEstimator_nonneg c s)) hl) hv.le
  have he : Real.sqrt (((n : ℝ) * criticalVarianceEstimator c s / Real.log n) /
        criticalVariance c (Pseq n)) =
      Real.sqrt ((n : ℝ) / Real.log n) * Real.sqrt (criticalVarianceEstimator c s) /
        Real.sqrt (criticalVariance c (Pseq n)) := by
    rw [Real.sqrt_div' _ hv.le]
    rw [show (n : ℝ) * criticalVarianceEstimator c s / Real.log n =
      ((n : ℝ) / Real.log n) * criticalVarianceEstimator c s by ring,
      Real.sqrt_mul (div_nonneg hn0 hl)]
  have hb := critical_sqrt_sub_one_abs_le hx
  rw [he] at hb
  exact hs.trans_le hb

/-- The observable contrast's nonrecurrence remainder stays negligible after
standardization by the exact moving variance, completing the normalized
numerator input to (26). The recurrence CLT itself is still separate. -/
-- @node: critical_standardized_recurrence_approximation_triangular_tendsto_zero
lemma critical_standardized_recurrence_approximation_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        (observableEstimator c s - causalTarget (Pseq n) -
          (recurrenceError c (Pseq n) true s (bandwidth c n) -
            recurrenceError c (Pseq n) false s (bandwidth c n))) /
        Real.sqrt (criticalVariance c (Pseq n))|}) atTop (nhds 0) := by
  let v := 2 * criticalCoefficient c * (Real.exp (-c.dMax) * c.lambdaMin / c.gMax)
  have hv : 0 < v := by
    dsimp [v]
    exact mul_pos (mul_pos (by norm_num) (criticalCoefficient_pos_lt_half c).1)
      (div_pos (mul_pos (Real.exp_pos _) c.lambdaMin_pos)
        (c.gMin_pos.trans c.gMin_lt))
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_observable_recurrence_triangular_probability_tendsto_zero c hk Pseq hP
      (mul_pos hε hroot))
  apply Eventually.of_forall
  intro n
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  have hV := Real.sqrt_pos.mpr (criticalVariance_pos c (Pseq n) (hP n))
  have hfloor : Real.sqrt v ≤ Real.sqrt (criticalVariance c (Pseq n)) :=
    Real.sqrt_le_sqrt (criticalVariance_uniform_lower c (Pseq n) (hP n))
  simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hV] at hs ⊢
  exact (mul_le_mul_of_nonneg_left hfloor hε.le).trans_lt ((lt_div_iff₀ hV).mp hs)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

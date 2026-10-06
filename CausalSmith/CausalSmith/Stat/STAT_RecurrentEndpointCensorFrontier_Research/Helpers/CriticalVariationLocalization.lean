module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalEmpiricalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationFluctuation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.OrdinaryRecurrenceOracleReplacement

/-!
# Removing critical variation localization on the risk event

Roadmap (27)--(29): the localized conditional Poisson score agrees with the
actual optional-minus-predictable variation on the linear risk-floor event.
Nonnegative recurrence times are derived from the Poisson model. The resulting
probability bound isolates the bad risk event. The proved empirical-risk
bound removes that event along triangular model laws, and measurable
transport and a two-arm union bound close the full observable form of (29).
Predictable-variation asymptotics remain a separate obligation.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Localization does not change the intensity integral on the risk-floor event. -/
-- @node: criticalLocalizedVariationWeight_integral_eq_original
lemma criticalLocalizedVariationWeight_integral_eq_original (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    (r : ℝ) (e : Fin n → Arm × (ℝ × ENNReal))
    (hfloor : ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
      riskSet a (fun j => recurrenceExposureHistory (e j)) t) (i : Fin n) :
    (∫ t, criticalLocalizedVariationWeight c a r e i t ∂recurrenceIntensity P a) =
      ∫ t, criticalRecurrenceVariationWeight c a e i t ∂recurrenceIntensity P a := by
  have hh := bandwidth_pos_and_le_cap c hn
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  have hT1 : 1 - bandwidth c n ≤ 1 := by linarith [hh.1]
  have he : (fun t => if t ≤ 1 - bandwidth c n then
      criticalLocalizedVariationWeight c a r e i t else 0) =
      (fun t => criticalLocalizedVariationWeight c a r e i t) := by
    funext t
    by_cases ht : t ≤ 1 - bandwidth c n
    · simp [ht]
    · simp [criticalLocalizedVariationWeight, criticalRecurrenceVariationWeight, ht]
  rw [← he, recurrenceIntensity_integral_truncated P hP.poissonRecurrence a _ hT hT1]
  change _ = ∫ t, (if t ≤ 1 - bandwidth c n then _ else 0) ∂recurrenceIntensity P a
  rw [recurrenceIntensity_integral_truncated P hP.poissonRecurrence a _ hT hT1]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hT]
  intro t ht
  dsimp only
  rw [criticalLocalizedVariationWeight_eq_original c a r e hfloor i ht]
  simp only [criticalRecurrenceVariationWeight, if_pos ht.2]

/-- Both the finite point sum and its compensator agree on the risk-floor event. -/
-- @node: criticalLocalizedVariationScore_eq_original
lemma criticalLocalizedVariationScore_eq_original (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    (r : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (R : Fin n → RecurConfig)
    (htimes : ∀ i, ∀ k : Fin (R i).1, 0 ≤ ((R i).2 k).1)
    (hfloor : ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
      riskSet a (fun j => recurrenceExposureHistory (e j)) t) :
    recurrenceJointExposureScore P a n (criticalLocalizedVariationWeight c a r) e R =
      recurrenceJointExposureScore P a n (criticalRecurrenceVariationWeight c a) e R := by
  unfold recurrenceJointExposureScore
  apply Finset.sum_congr rfl
  intro i _
  rw [criticalLocalizedVariationWeight_integral_eq_original c P hP a hn r e hfloor i]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : ((R i).2 k).1 ≤ 1 - bandwidth c n
  · exact criticalLocalizedVariationWeight_eq_original c a r e hfloor i ⟨htimes i k, ht⟩
  · simp [criticalLocalizedVariationWeight, criticalRecurrenceVariationWeight, ht]

/-- For genuine latent samples the localized score is the actual variance error
on the risk event; recurrence-time regularity is proved rather than assumed. -/
-- @node: criticalLocalizedVariationScore_eq_variance_error_ae
lemma criticalLocalizedVariationScore_eq_variance_error_ae (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n) (r : ℝ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      (∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
        riskSet a (fun j => recurrenceExposureHistory
          ((z j).treatment, ((z j).death a, (z j).censor a))) t) →
      recurrenceJointExposureScore P a n (criticalLocalizedVariationWeight c a r)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) =
      armCriticalVariance c a (fun j => observe (z j)) -
        (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
          recurrenceSubjectWeight c (bandwidth c n) a (fun j => observe (z j)) i t ^ 2 *
            P.lam a t) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hi : ∀ i : Fin n, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      ∀ k : Fin ((z i).recur a).1, 0 ≤ (((z i).recur a).2 k).1 := by
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P.latent) i).quasiMeasurePreserving.ae
      (recurrence_latent_ae_nonneg_time P hP.poissonRecurrence a)
  filter_upwards [ae_all_iff.mpr hi] with z hz
  intro hfloor
  rw [criticalLocalizedVariationScore_eq_original c P hP a hn r _ _ hz hfloor]
  exact (armCriticalVariance_sub_energy_eq_latent_score c P hP a hn z).symm

/-- The original fluctuation tail is bounded by the localized Poisson tail plus
exactly the probability of failure of the linear risk floor. -/
-- @node: critical_variance_error_probability_le_localized_add_risk_failure
lemma critical_variance_error_probability_le_localized_add_risk_failure
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (r q ε : ℝ) :
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |q * (armCriticalVariance c a (fun j => observe (z j)) -
        (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
          recurrenceSubjectWeight c (bandwidth c n) a (fun j => observe (z j)) i t ^ 2 *
            P.lam a t))|} ≤
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |q * recurrenceJointExposureScore P a n (criticalLocalizedVariationWeight c a r)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} +
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ¬ ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
        riskSet a (fun j => recurrenceExposureHistory
          ((z j).treatment, ((z j).death a, (z j).censor a))) t} := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  apply le_trans (ENNReal.toReal_mono (by finiteness) (measure_mono_ae ?_))
    (measureReal_union_le _ _)
  filter_upwards [criticalLocalizedVariationScore_eq_variance_error_ae c P hP a hn r]
    with z hz
  intro htail
  by_cases hf : ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
      riskSet a (fun j => recurrenceExposureHistory
        ((z j).treatment, ((z j).death a, (z j).censor a))) t
  · apply Or.inl
    simp only [mem_setOf_eq, hz hf]
    exact htail
  · exact Or.inr hf

/-- Roadmap (29) holds for the actual variance error restricted to the risk
floor event, along arbitrary triangular model laws. -/
-- @node: critical_variance_error_on_risk_floor_triangular_tendsto_zero
lemma critical_variance_error_on_risk_floor_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => (Pseq n).latent)).real {z |
      (∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
        riskSet a (fun j => recurrenceExposureHistory
          ((z j).treatment, ((z j).death a, (z j).censor a))) t) ∧
      ε < |((n : ℝ) / Real.log n) *
        (armCriticalVariance c a (fun j => observe (z j)) -
          (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
            recurrenceSubjectWeight c (bandwidth c n) a (fun j => observe (z j)) i t ^ 2 *
              (Pseq n).lam a t))|}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (criticalLocalizedVariationScore_triangular_probability_tendsto_zero
      c hk Pseq hP a hr hε)
  filter_upwards [eventually_ge_atTop 1] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  apply ENNReal.toReal_mono (by finiteness) (measure_mono_ae ?_)
  filter_upwards [criticalLocalizedVariationScore_eq_variance_error_ae
    c (Pseq n) (hP n) a (by omega : 0 < n) r] with z hz
  intro he
  change ε < |((n : ℝ) / Real.log n) *
    recurrenceJointExposureScore (Pseq n) a n (criticalLocalizedVariationWeight c a r)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)|
  rw [hz he.1]
  exact he.2


/-- The observed risk-floor failure bound also controls genuine latent samples,
without requiring measurability of the uncountable risk-floor event. -/
-- @node: critical_latent_risk_floor_failure_triangular_tendsto
lemma critical_latent_risk_floor_failure_triangular_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => (Pseq n).latent)).real {z |
      ¬ ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        (n : ℝ) * (c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2) * (1 - t) ≤
          riskSet a (fun j => recurrenceExposureHistory
            ((z j).treatment, ((z j).death a, (z j).censor a))) t})
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_empirical_risk_linear_floor_failure_triangular_tendsto c hk Pseq hP a)
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  rw [recurrence_sampleLaw_eq_latent_map]
  apply ENNReal.toReal_mono (by finiteness)
  simpa only [Set.preimage_setOf_eq, riskSet_observe_eq_recurrenceExposureHistory] using
    Measure.le_map_apply
      (show Measurable (fun z : Fin n → LatentSubject => fun j => observe (z j)) by
        fun_prop).aemeasurable
      {s | ¬ ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        (n : ℝ) * (c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2) * (1 - t) ≤
          riskSet a s t}

/-- Removing localization closes roadmap (29) for the actual arm optional
variation minus its predictable energy along arbitrary triangular model laws. -/
-- @node: critical_variance_error_triangular_tendsto_zero
lemma critical_variance_error_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => (Pseq n).latent)).real {z |
      ε < |((n : ℝ) / Real.log n) *
        (armCriticalVariance c a (fun j => observe (z j)) -
          (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
            recurrenceSubjectWeight c (bandwidth c n) a (fun j => observe (z j)) i t ^ 2 *
              (Pseq n).lam a t))|}) atTop (nhds 0) := by
  let r := c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2
  have hr : 0 < r := div_pos
    (mul_pos (mul_pos c.pMin_pos (Real.exp_pos _))
      (lt_min c.Gint_pos (div_pos c.gMin_pos (by norm_num)))) (by norm_num)
  have hlocal := criticalLocalizedVariationScore_triangular_probability_tendsto_zero
    c hk Pseq hP a hr hε
  have hbad := critical_latent_risk_floor_failure_triangular_tendsto c hk Pseq hP a
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hlocal.add hbad)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact critical_variance_error_probability_le_localized_add_risk_failure
    c (Pseq n) (hP n) a (by omega) r ((n : ℝ) / Real.log n) ε


/-- The unlocalized fluctuation limit holds in the observable experiment,
using measurability of the genuine optional and predictable variations. -/
-- @node: critical_observed_variance_error_triangular_tendsto_zero
lemma critical_observed_variance_error_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) / Real.log n) *
        (armCriticalVariance c a s -
          (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
            recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 *
              (Pseq n).lam a t))|}) atTop (nhds 0) := by
  apply (critical_variance_error_triangular_tendsto_zero c hk Pseq hP a hε).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hh1 : bandwidth c n ≤ 1 := by linarith [hh.2, c.x0_le]
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
        recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * (Pseq n).lam a t) :=
    Finset.measurable_sum _ (fun i _ =>
      measurable_recurrenceWeightIntegral c (Pseq n) (hP n).poissonRecurrence a i
        hh.1.le hh1 2)
  have hs : MeasurableSet {s : Fin n → ObsHistory |
      ε < |((n : ℝ) / Real.log n) * (armCriticalVariance c a s -
        (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
          recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * (Pseq n).lam a t))|} := by
    exact measurableSet_lt measurable_const
      (((show Measurable (fun s : Fin n → ObsHistory => armCriticalVariance c a s) by
        fun_prop).sub hm).const_mul ((n : ℝ) / Real.log n)).abs
  rw [recurrence_sampleLaw_eq_latent_map]
  simp only [measureReal_def]
  rw [Measure.map_apply (by fun_prop) hs]
  rfl


/-- The full observable optional variation differs negligibly from the sum of
its two genuine predictable energies, completing roadmap (27)--(29). -/
-- @node: critical_total_variance_error_triangular_tendsto_zero
lemma critical_total_variance_error_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) / Real.log n) *
        (criticalVarianceEstimator c s -
          (∑ a : Arm, ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
            recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 *
              (Pseq n).lam a t))|}) atTop (nhds 0) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have h0 := critical_observed_variance_error_triangular_tendsto_zero
    c hk Pseq hP false hhalf
  have h1 := critical_observed_variance_error_triangular_tendsto_zero
    c hk Pseq hP true hhalf
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
  change ε < |((n : ℝ) / Real.log n) *
    (criticalVarianceEstimator c s - _)| at hs
  simp only [criticalVarianceEstimator, Fintype.sum_bool] at hs
  by_contra hne
  have hboth := not_or.mp hne
  simp only [Set.mem_setOf_eq] at hboth
  have hb0 := le_of_not_gt hboth.1
  have hb1 := le_of_not_gt hboth.2
  change |((n : ℝ) / Real.log n) * (armCriticalVariance c false s - _)| ≤ ε / 2 at hb0
  change |((n : ℝ) / Real.log n) * (armCriticalVariance c true s - _)| ≤ ε / 2 at hb1
  have htri := abs_add_le
    (((n : ℝ) / Real.log n) * (armCriticalVariance c false s -
      (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
        recurrenceSubjectWeight c (bandwidth c n) false s i t ^ 2 * (Pseq n).lam false t)))
    (((n : ℝ) / Real.log n) * (armCriticalVariance c true s -
      (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
        recurrenceSubjectWeight c (bandwidth c n) true s i t ^ 2 * (Pseq n).lam true t)))
  rw [show ∀ q a b x y : ℝ, q * (a + b - (x + y)) =
      q * (a - y) + q * (b - x) by intros; ring] at hs
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

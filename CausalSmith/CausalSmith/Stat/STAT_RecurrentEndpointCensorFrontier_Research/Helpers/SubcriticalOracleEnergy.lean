module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleTails

/-!
# Full-horizon oracle predictable energies

The exact risk marginal cancels one inverse-retention factor before time
integration. Product integrability follows from the subcritical tail assumption,
so Fubini applies to the unbounded endpoint oracle weights themselves.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Marginal oracle energy cancels the risk probability, without any
independence assertion about the empirical risk process. -/
-- @node: subcritical_oracle_energy_marginal
lemma subcritical_oracle_energy_marginal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ) :
    (∫ s : Fin n → ObsHistory,
      f t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2) ∂sampleLaw P n) =
      (P.p a)⁻¹ * (survival P a t * f t / retention P a t) := by
  have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
  have hg : retention P a t ≠ 0 :=
    (retention_pos_of_modelClass c P hP a t ht.1.le ht.2).ne'
  rw [integral_const_mul, integral_mul_const,
    DeathCP.observed_integral_riskFraction_eq c P hP a hn ⟨ht.1.le, ht.2.le⟩]
  field_simp

/-- The full random oracle energy is integrable on the product of the sample
law and study-window measure. No bound on inverse retention is assumed. -/
-- @node: subcritical_oracle_energy_integrable_prod
lemma subcritical_oracle_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      f p.2 * (((riskSet a p.1 p.2 : ℝ) / n) *
        (1 / (P.p a * retention P a p.2)) ^ 2))
      ((sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := fun (s : Fin n → ObsHistory) (t : ℝ) =>
    f t * (((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2)
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ => E p.1 p.2) := by
    have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    dsimp [E]
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with t
    exact (DeathCP.integrable_observed_risk_weighted_sq P a t
      (fun _ => 1 / (P.p a * retention P a t)) measurable_const
      (abs_nonneg _) (fun _ => le_rfl)).const_mul (f t)
  · have hi := (subcritical_continuous_invRetention_intervalIntegrable
      c P hP hk a (fun t => survival P a t * |f t|)
      ((modelClass_survival_continuousOn c P hP a).mul hc.abs)).const_mul (P.p a)⁻¹
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have heq : (∫ s : Fin n → ObsHistory, ‖E s t‖ ∂sampleLaw P n) =
        ∫ s : Fin n → ObsHistory,
          |f t| * (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2) ∂sampleLaw P n := by
      apply integral_congr_ae
      filter_upwards [] with s
      dsimp [E]
      rw [abs_mul, abs_of_nonneg (show 0 ≤
        ((riskSet a s t : ℝ) / n) * (1 / (P.p a * retention P a t)) ^ 2 by positivity)]
    rw [heq]
    exact (subcritical_oracle_energy_marginal c P hP a hn ht (fun t => |f t|)).symm

/-- The expectation of full-horizon oracle energy is its exact deterministic
variance integral, justified by the preceding product integrability. -/
-- @node: subcritical_oracle_expected_energy
lemma subcritical_oracle_expected_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      f t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
        survival P a t * f t / retention P a t := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  rw [integral_integral_swap
    (subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc)]
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1,
        (P.p a)⁻¹ * (survival P a t * f t / retention P a t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact subcritical_oracle_energy_marginal c P hP a hn ht f
    _ = _ := integral_const_mul _ _

/-- Continuous coefficients on the study window suffice; no globally smooth
or globally measurable extension of the model hazard is required. -/
-- @node: subcritical_oracle_expected_energy_of_continuousOn
lemma subcritical_oracle_expected_energy_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      f t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
        survival P a t * f t / retention P a t := by
  classical
  let g : ℝ → ℝ := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g :=
    hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t :=
    piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hm := subcritical_oracle_expected_energy c P hP hk a hn g hg hgc
  have hleft : (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      f t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
        g t * (((riskSet a s t : ℝ) / n) *
          (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n := by
    apply integral_congr_ae
    filter_upwards [] with s
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩]
  rw [hleft, hm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [he t ⟨ht.1.le, ht.2.le⟩]

/-- The recurrence oracle has exactly its stated variance contribution on the
full horizon, even when its inverse-retention weight is unbounded. -/
-- @node: subcritical_recurrence_oracle_expected_energy
lemma subcritical_recurrence_oracle_expected_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      P.lam a t * (((riskSet a s t : ℝ) / n) *
        (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
      (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t := by
  rw [subcritical_oracle_expected_energy_of_continuousOn c P hP hk a hn
    (P.lam a) (hP.recurrenceHolder a).1.continuousOn]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]

/-- The deterministic remaining-target death oracle has exactly its stated
variance contribution. Its endpoint weight is integrated via Fubini rather
than inserted into a bounded-integrand isometry. -/
-- @node: subcritical_death_oracle_expected_energy
lemma subcritical_death_oracle_expected_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
      ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        (((riskSet a s t : ℝ) / n) *
          (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) =
      (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
        remainingTarget c P a 0 t ^ 2 * P.hazard a t /
          (survival P a t * retention P a t) := by
  have hc : ContinuousOn (fun t =>
      (remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  rw [subcritical_oracle_expected_energy_of_continuousOn c P hP hk a hn _ hc]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- Summing the two exact oracle energies over treatment arms recovers the
paper variance functional for every positive sample size. This is an energy
identity; the stochastic influence second-moment identity remains separate. -/
-- @node: subcritical_oracle_expected_total_energy
lemma subcritical_oracle_expected_total_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {n : ℕ} (hn : 0 < n) :
    (∑ a : Arm,
      ((∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
        P.lam a t * (((riskSet a s t : ℝ) / n) *
          (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n) +
       (∫ s : Fin n → ObsHistory, (∫ t in Ioo (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
          (((riskSet a s t : ℝ) / n) *
            (1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n))) =
      subcriticalVariance c P := by
  unfold subcriticalVariance
  apply Finset.sum_congr rfl
  intro a _
  rw [subcritical_recurrence_oracle_expected_energy c P hP hk a hn,
    subcritical_death_oracle_expected_energy c P hP hk a hn,
    intervalIntegral.integral_add
      (subcritical_recurrence_energy_intervalIntegrable c P hP hk a)
      (subcritical_death_energy_intervalIntegrable c P hP hk a), mul_add]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

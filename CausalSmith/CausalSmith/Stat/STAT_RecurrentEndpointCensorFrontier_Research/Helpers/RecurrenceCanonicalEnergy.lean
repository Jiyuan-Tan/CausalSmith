module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrencePoissonMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreTransport

/-!
# Canonical recurrence energy

The finite-intensity canonical recurrence law has the same compensated energy
as its intensity measure. Normalization and the auxiliary mark cancel exactly,
so concrete exposure scores retain their time-dependent weights.
-/

public section

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Multiplying the normalized point law by the finite mass recovers the intensity,
including the zero-intensity case. -/
-- @node: recurrence_mass_smul_normalized
lemma recurrence_mass_smul_normalized (ν : Measure ℝ) [IsFiniteMeasure ν] :
    finiteMeasureMass ν • normalizedFiniteMeasure ν (Measure.dirac 0) = ν := by
  by_cases hν : ν = 0
  · subst ν
    simp [finiteMeasureMass, normalizedFiniteMeasure]
  · ext s hs
    rw [normalizedFiniteMeasure, dif_neg hν, Measure.smul_apply, Measure.smul_apply]
    change ((finiteMeasureMass ν : ℝ≥0) : ℝ≥0∞) * ((ν univ)⁻¹ * ν s) = ν s
    rw [finiteMeasureMass, ENNReal.coe_toNNReal (measure_ne_top ν univ),
      ← mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact fun h => hν (Measure.measure_univ_eq_zero.mp h)
    · exact measure_ne_top ν univ

/-- The marked normalized point expectation, multiplied by the Poisson rate,
is the integral against the original time intensity. -/
-- @node: recurrence_normalized_marked_integral
lemma recurrence_normalized_marked_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : ℝ → ℝ) :
    (finiteMeasureMass ν : ℝ) *
      (∫ x : ℝ × ℝ, f x.1
        ∂(normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0)) =
      ∫ t, f t ∂ν := by
  rw [integral_fun_fst]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  calc
    _ = ∫ t, f t ∂(finiteMeasureMass ν • normalizedFiniteMeasure ν (Measure.dirac 0)) :=
      (integral_smul_nnreal_measure f (finiteMeasureMass ν)).symm
    _ = _ := congrArg (fun μ => ∫ t, f t ∂μ) (recurrence_mass_smul_normalized ν)

/-- Bounded measurable time scores are square-integrable under the normalized
marked point law, also when the intensity is zero. -/
-- @node: recurrence_normalized_marked_integrable_sq
lemma recurrence_normalized_marked_integrable_sq (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : ℝ → ℝ) (hf : Measurable f) {K : ℝ} (hK : ∀ t, |f t| ≤ K) :
    Integrable (fun x : ℝ × ℝ => f x.1 ^ 2)
      ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0)) := by
  refine Integrable.comp_fst (f := fun t => f t ^ 2) ?_ (Measure.dirac (0 : ℝ))
  apply (integrable_const (K ^ 2)).mono' (hf.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg (f t)).trans (hK t))).2 (hK t)

/-- For arbitrary bounded measurable subject time scores, the canonical iid
recurrence sample has exact additive compensated energy. -/
-- @node: recurrence_canonical_iid_second_moment
lemma recurrence_canonical_iid_second_moment (ν : Measure ℝ) [IsFiniteMeasure ν]
    (n : ℕ) (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {K : ℝ} (hK : ∀ i t, |f i t| ≤ K) :
    Integrable (fun r : Fin n → RecurConfig =>
      (∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν)) ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) ∧
    (∫ r : Fin n → RecurConfig,
      (∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν)) ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) =
      ∑ i : Fin n, ∫ t, f i t ^ 2 ∂ν := by
  have hmoment := recurrence_poisson_iid_compensated_second_moment
    ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0))
    (finiteMeasureMass ν) n (fun i x => f i x.1)
    (fun i => (hf i).comp measurable_fst)
    (fun i => recurrence_normalized_marked_integrable_sq ν (f i) (hf i) (hK i))
  simp_rw [recurrence_normalized_marked_integral ν] at hmoment
  have henergy (i : Fin n) := recurrence_normalized_marked_integral ν (fun t => f i t ^ 2)
  simp_rw [henergy] at hmoment
  simpa only [canonicalRecurrenceLawOf, finiteMeasureMarkedPoissonLaw, one_mul,
    finiteMarkedPoissonSampleLaw] using hmoment

/-- Truncating a score under the recurrence intensity is precisely its weighted
Lebesgue integral over the estimation interval. -/
-- @node: recurrenceIntensity_integral_truncated
lemma recurrenceIntensity_integral_truncated (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (f : ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ t, (if t ≤ T then f t else 0) ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..T, f t * P.lam a t := by
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hP a).1.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (∫ t in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal (P.lam a t)).toReal • (if t ≤ T then f t else 0)) =
      ∫ t in Ioc (0 : ℝ) 1, (Iic T).indicator (fun t => f t * P.lam a t) t := by
    apply integral_congr_ae
    filter_upwards [(hP a).2.1] with t ht
    simp only [ENNReal.toReal_ofReal ht, smul_eq_mul, indicator_apply, mem_Iic]
    split_ifs <;> ring
  rw [heq, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic T ∩ Ioc (0 : ℝ) 1 = Ioc 0 T := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨htT, ht0, _⟩
      exact ⟨ht0, htT⟩
    · rintro ⟨ht0, htT⟩
      exact ⟨htT, ht0, htT.trans hT1⟩
  rw [hset, intervalIntegral.integral_of_le hT]

/-- With exposure held fixed, the concrete recurrence score has exactly the
integrated subject-weight energy as its conditional second moment. -/
-- @node: recurrenceConcreteExposureScore_conditional_second_moment
lemma recurrenceConcreteExposureScore_conditional_second_moment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (e : Fin n → Arm × (ℝ × ENNReal)) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Integrable (fun r => recurrenceConcreteExposureScore c P a n h e r ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) ∧
    (∫ r, recurrenceConcreteExposureScore c P a n h e r ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) =
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t := by
  let w := fun i => recurrenceSubjectWeight c h a
    (fun j => recurrenceExposureHistory (e j)) i
  let f := fun i t => if t ≤ 1 - h then w i t else 0
  have hf (i : Fin n) : Measurable (f i) := by
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · exact measurable_recurrenceSubjectWeight c h a _ i
    · exact measurable_const
  have hK (i : Fin n) (t : ℝ) : |f i t| ≤ weightEnvelope c := by
    dsimp [f]
    split_ifs
    · exact recurrenceSubjectWeight_abs_le c hh a _ i t
    · simp only [abs_zero]
      unfold weightEnvelope continuationNorm
      positivity
  have hm := recurrence_canonical_iid_second_moment (recurrenceIntensity P a) n f hf hK
  have hmean (i : Fin n) : (∫ t, f i t ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h), w i t * P.lam a t :=
    recurrenceIntensity_integral_truncated P hP.poissonRecurrence a (w i)
      (by linarith) (by linarith)
  have henergy (i : Fin n) : (∫ t, f i t ^ 2 ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h), w i t ^ 2 * P.lam a t := by
    have hp : (fun t => f i t ^ 2) = fun t => if t ≤ 1 - h then w i t ^ 2 else 0 := by
      funext t
      dsimp [f]
      split_ifs <;> simp
    rw [hp]
    exact recurrenceIntensity_integral_truncated P hP.poissonRecurrence a
      (fun t => w i t ^ 2) (by linarith) (by linarith)
  simp_rw [hmean, henergy] at hm
  exact hm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

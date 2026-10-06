module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceCanonicalEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance

/-!
# Unbounded canonical recurrence scores

Square integrability against the finite time intensity suffices for exact
Poisson centering and energy. These lemmas remove the bounded-score restriction
from the canonical recurrence calculation used in roadmap (24). They do not
assume that an endpoint inverse-retention weight is globally bounded.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An intensity-integrable score remains integrable under normalization;
the zero-intensity fallback is treated separately. -/
-- @node: recurrence_normalized_marked_integrable_of_integrable
lemma recurrence_normalized_marked_integrable_of_integrable
    (ν : Measure ℝ) [IsFiniteMeasure ν] (f : ℝ → ℝ)
    (hi : Integrable f ν) :
    Integrable (fun x : ℝ × ℝ => f x.1)
      ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0)) := by
  apply Integrable.comp_fst (μ := normalizedFiniteMeasure ν (Measure.dirac 0))
    (ν := Measure.dirac (0 : ℝ))
  classical
  by_cases hν : ν = 0
  · rw [normalizedFiniteMeasure, dif_pos hν]
    exact integrable_dirac (by finiteness)
  · rw [normalizedFiniteMeasure, dif_neg hν]
    exact hi.to_average

/-- Unbounded square-integrable time scores have exact additive canonical
Poisson energy. Square integrability, rather than a supremum envelope, is the
only analytic input. -/
-- @node: recurrence_canonical_iid_second_moment_of_integrable_sq
lemma recurrence_canonical_iid_second_moment_of_integrable_sq
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (fun t => f i t ^ 2) ν) :
    Integrable (fun r : Fin n → RecurConfig =>
      (∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν)) ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) ∧
    (∫ r : Fin n → RecurConfig,
      (∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν)) ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) =
      ∑ i : Fin n, ∫ t, f i t ^ 2 ∂ν := by
  have hm := recurrence_poisson_iid_compensated_second_moment
    ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0))
    (finiteMeasureMass ν) n (fun i x => f i x.1)
    (fun i => (hf i).comp measurable_fst)
    (fun i => recurrence_normalized_marked_integrable_of_integrable ν
      (fun t => f i t ^ 2) (hi i))
  simp_rw [recurrence_normalized_marked_integral ν] at hm
  have he (i : Fin n) := recurrence_normalized_marked_integral ν (fun t => f i t ^ 2)
  simp_rw [he] at hm
  simpa only [canonicalRecurrenceLawOf, finiteMeasureMarkedPoissonLaw, one_mul,
    finiteMarkedPoissonSampleLaw] using hm

/-- An intensity-integrable canonical compensated recurrence score has zero
mean, with no boundedness premise. -/
-- @node: recurrence_canonical_iid_mean_zero_of_integrable
lemma recurrence_canonical_iid_mean_zero_of_integrable
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) ν) :
    Integrable (fun r : Fin n → RecurConfig =>
      ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν))
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) ∧
    (∫ r : Fin n → RecurConfig,
      ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν)
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) = 0 := by
  have hm := recurrence_poisson_iid_compensated_mean_zero
    ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0))
    (finiteMeasureMass ν) n (fun i x => f i x.1)
    (fun i => (hf i).comp measurable_fst)
    (fun i => recurrence_normalized_marked_integrable_of_integrable ν
      (f i) (hi i))
  unfold recurrenceExposureScore at hm
  simp_rw [recurrence_normalized_marked_integral ν] at hm
  simpa only [canonicalRecurrenceLawOf, finiteMeasureMarkedPoissonLaw, one_mul,
    finiteMarkedPoissonSampleLaw] using hm

/-- Averaging over random exposures preserves the exact unbounded-score
energy. Fubini is justified by the averaged energy, without factoring any
exposure-dependent score. Conditional square integrability is needed only
almost surely, so exceptional endpoint exposures cause no extra premise. -/
-- @node: recurrence_canonical_random_exposure_second_moment_of_integrable_sq
lemma recurrence_canonical_random_exposure_second_moment_of_integrable_sq
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [SFinite Q]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : E → Fin n → ℝ → ℝ)
    (hf : ∀ e i, Measurable (f e i))
    (hi : ∀ᵐ e ∂Q, ∀ i, Integrable (fun t => f e i t ^ 2) ν)
    (hs : Measurable (fun p : E × (Fin n → RecurConfig) =>
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)))
    (he : Integrable (fun e => ∑ i : Fin n, ∫ t, f e i t ^ 2 ∂ν) Q) :
    Integrable (fun p : E × (Fin n → RecurConfig) =>
      (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)) ^ 2)
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) ∧
    (∫ p : E × (Fin n → RecurConfig),
      (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)) ^ 2
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) =
      ∫ e, ∑ i : Fin n, ∫ t, f e i t ^ 2 ∂ν ∂Q := by
  let : IsProbabilityMeasure (canonicalRecurrenceLawOf ν) := by
    unfold canonicalRecurrenceLawOf finiteMeasureMarkedPoissonLaw
    infer_instance
  have hlocal (e : E) (hei : ∀ i, Integrable (fun t => f e i t ^ 2) ν) :=
    recurrence_canonical_iid_second_moment_of_integrable_sq ν n (f e) (hf e) hei
  have hprod : Integrable (fun p : E × (Fin n → RecurConfig) =>
      (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)) ^ 2)
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) := by
    apply (integrable_prod_iff (hs.pow_const 2).aestronglyMeasurable).2
    constructor
    · filter_upwards [hi] with e hei
      exact (hlocal e hei).1
    · apply he.congr
      filter_upwards [hi] with e hei
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (hlocal e hei).2.symm
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [hi] with e hei
  exact (hlocal e hei).2

/-- Finite averaged canonical energy also gives centering after exposure
averaging. Each conditional Poisson score is centered before integration. -/
-- @node: recurrence_canonical_random_exposure_mean_zero_of_integrable_sq
lemma recurrence_canonical_random_exposure_mean_zero_of_integrable_sq
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : E → Fin n → ℝ → ℝ)
    (hf : ∀ e i, Measurable (f e i))
    (hi : ∀ᵐ e ∂Q, ∀ i, Integrable (fun t => f e i t ^ 2) ν)
    (hs : Measurable (fun p : E × (Fin n → RecurConfig) =>
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)))
    (he : Integrable (fun e => ∑ i : Fin n, ∫ t, f e i t ^ 2 ∂ν) Q) :
    Integrable (fun p : E × (Fin n → RecurConfig) =>
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν))
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) ∧
    (∫ p : E × (Fin n → RecurConfig),
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) = 0 := by
  let : IsProbabilityMeasure (canonicalRecurrenceLawOf ν) := by
    unfold canonicalRecurrenceLawOf finiteMeasureMarkedPoissonLaw
    infer_instance
  have hi2 := (recurrence_canonical_random_exposure_second_moment_of_integrable_sq
    Q ν n f hf hi hs he).1
  have hint := ((memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2
    hi2).integrable (by norm_num)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have hmean (e : E) (hei : ∀ i, Integrable (fun t => f e i t ^ 2) ν) :
      (∫ r : Fin n → RecurConfig,
        ∑ i : Fin n, ((∑ k : Fin (r i).1, f e i (((r i).2 k).1)) -
          ∫ t, f e i t ∂ν)
        ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) = 0 := by
    apply (recurrence_canonical_iid_mean_zero_of_integrable ν n (f e) (hf e) _).2
    intro i
    exact ((memLp_two_iff_integrable_sq (hf e i).aestronglyMeasurable).2
      (hei i)).integrable (by norm_num)
  calc
    _ = ∫ _ : E, (0 : ℝ) ∂Q := by
      apply integral_congr_ae
      filter_upwards [hi] with e hei
      exact hmean e hei
    _ = 0 := integral_zero _ _

/-- Stopping strictly before the endpoint gives conditional square
integrability of the actual inverse-retention score under any finite time
intensity. The bound follows from retention monotonicity and model positivity,
so no inverse-weight moment assumption is added. -/
-- @node: recurrence_stopped_invRetention_integrable_sq
lemma recurrence_stopped_invRetention_integrable_sq
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (ν : Measure ℝ) [IsFiniteMeasure ν] {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Integrable (fun t => (if t ≤ T then (retention P a t)⁻¹ else 0) ^ 2) ν := by
  have hg : 0 < retention P a T :=
    retention_pos_of_modelClass c P hP a T hT0 hT1
  have hm : Measurable (fun t => if t ≤ T then (retention P a t)⁻¹ else 0) :=
    (measurable_retention P a).inv.ite
      (measurableSet_le measurable_id measurable_const) measurable_const
  apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable
    ((retention P a T)⁻¹ ^ 2)
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases ht : t ≤ T
  · rw [if_pos ht]
    apply pow_le_pow_left₀ (inv_nonneg.mpr measureReal_nonneg)
    exact (inv_le_inv₀ (hg.trans_le (retention_antitone P a ht)) hg).2
      (retention_antitone P a ht)
  · simp only [if_neg ht, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

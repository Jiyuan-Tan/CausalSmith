module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureDensities
public import Causalean.Stat.Minimax.HellingerAffinity
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Integrating conditional original-record experiments

The uniform record reference separates into the public covariate law and the
uniform four-label law. Regrouping its finite product and applying Fubini retains
all original records and integrates their conditional label discrepancy.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The four-label reference assigns probability one quarter to each label. -/
-- @node: labelReference
def labelReference : Measure (Bool × Bool) := (1/4 : ℝ≥0∞) • Measure.count

/-- The fair label reference has total mass one. [the stated conclusion](goal) holds. -/
-- @node: labelReference_probability
instance labelReference_probability : IsProbabilityMeasure labelReference := by
  constructor
  norm_num [labelReference, Measure.smul_apply, Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Every label array has exactly the uniform mass four to the minus n. [the stated conclusion](goal) holds. -/
-- @node: labelReference_pi_eq_count
lemma labelReference_pi_eq_count (n : ℕ) :
    Measure.pi (fun _ : Fin n => labelReference) =
      (1/4 : ℝ≥0∞) ^ n • (Measure.count : Measure (Fin n → Bool × Bool)) := by
  apply Measure.ext_of_singleton
  intro l
  rw [Measure.pi_singleton]
  simp [labelReference, Measure.smul_apply]

/-- Conditional integration over labels is a finite uniform average. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:f). -/
-- @node: integral_labelReference_pi
lemma integral_labelReference_pi (n : ℕ) (f : (Fin n → Bool × Bool) → ℝ) :
    (∫ l, f l ∂Measure.pi (fun _ : Fin n => labelReference)) =
      (1/4 : ℝ) ^ n * ∑ l, f l := by
  rw [labelReference_pi_eq_count, integral_smul_measure, integral_count]
  simp

/-- The actual one-record reference is the product of covariates and fair labels. [the stated conclusion](goal) holds. -/
-- @node: recordReference_eq_prod
lemma recordReference_eq_prod : recordReference = uniformLaw.prod labelReference := by
  apply Measure.ext_of_lintegral
  intro f hf
  have h := lintegral_jointLaw_cells
    (lawFromCells (fun _ _ _ => 1/4) fairDefault_valid) f hf
  change (∫⁻ o, f o ∂recordReference) = _ at h
  rw [h, lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro x
  simp [labelReference, lintegral_smul_measure, lintegral_count,
    tsum_fintype, Fintype.sum_prod_type, lawFromCells, mul_add]

/-- Regrouping a sample into its covariates and labels preserves the full
reference measure. This is a bijection and discards no sample coordinates. [the documented result](goal) -/
-- @node: recordReference_regroup_preserving
lemma recordReference_regroup_preserving (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow Covariate (Bool × Bool) (Fin n))
      (Measure.pi (fun _ : Fin n => recordReference))
      ((Measure.pi (fun _ : Fin n => uniformLaw)).prod
        (Measure.pi (fun _ : Fin n => labelReference))) := by
  simp_rw [recordReference_eq_prod]
  exact measurePreserving_arrowProdEquivProdArrow _ _ _ _ _

/-- Fubini identifies the original-sample integral with the covariate integral
of the conditional label integral whenever the sample integrand is integrable. [the documented result](goal) Under [the stated assumptions](hyp:hf). -/
-- @node: integral_original_records_conditional
lemma integral_original_records_conditional (n : ℕ) (f : (Fin n → Record) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin n => recordReference))) :
    (∫ o, f o ∂Measure.pi (fun _ : Fin n => recordReference)) =
      ∫ x, ∫ l, f (fun i => (x i, l i))
        ∂Measure.pi (fun _ : Fin n => labelReference)
        ∂Measure.pi (fun _ : Fin n => uniformLaw) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Covariate (Bool × Bool) (Fin n)
  have hp := (recordReference_regroup_preserving n).symm e
  have hi : Integrable (fun z => f (e.symm z))
      ((Measure.pi (fun _ : Fin n => uniformLaw)).prod
        (Measure.pi (fun _ : Fin n => labelReference))) :=
    (hp.integrable_comp hf.aestronglyMeasurable).2 hf
  rw [← hp.integral_comp e.symm.measurableEmbedding f, integral_prod _ hi]
  rfl

/-- Product likelihoods of the actual observed laws are integrable under the
sample reference. [the documented result](goal) -/
-- @node: sampleCellDensity_integrable
lemma sampleCellDensity_integrable (n : ℕ) (P : ObservedLaw) :
    Integrable (sampleCellDensity n P) (Measure.pi (fun _ : Fin n => recordReference)) := by
  exact Integrable.fintype_prod_dep (fun _ => recordCellDensity_integrable P)

/-- The shared-sign finite-prior likelihood is integrable under the same
sample reference, with no independence assumption on its mixture components. [the documented result](goal) -/
-- @node: signMixtureCellDensity_integrable
lemma signMixtureCellDensity_integrable (n k : ℕ)
    (laws : (Fin (k + 1) → Bool) → ObservedLaw) :
    Integrable (signMixtureCellDensity n k laws)
      (Measure.pi (fun _ : Fin n => recordReference)) := by
  unfold signMixtureCellDensity
  exact (integrable_finsetSum _ (fun σ _ => sampleCellDensity_integrable n (laws σ))).const_mul _

/-- Nonnegative integrable densities have an integrable squared square-root
discrepancy: its pointwise value is bounded by their sum. [the documented result](goal) Under [the stated assumptions](hyp:μ,f,g,hf,hg,hf0,hg0). -/
-- @node: mixture_hellinger_integrand_integrable
lemma mixture_hellinger_integrand_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ o, 0 ≤ f o) (hg0 : ∀ o, 0 ≤ g o) :
    Integrable (fun o => (Real.sqrt (f o) - Real.sqrt (g o)) ^ 2) μ := by
  apply (hf.add hg).mono'
  · fun_prop
  · filter_upwards [] with o
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (Real.sqrt (f o) - Real.sqrt (g o)) ^ 2 ≤ f o + g o
    nlinarith [Real.sq_sqrt (hf0 o), Real.sq_sqrt (hg0 o),
      mul_nonneg (Real.sqrt_nonneg (f o)) (Real.sqrt_nonneg (g o))]

/-- [The unconditional discrepancy is exactly the covariate integral of the
conditional label discrepancy, since the two experiments share their covariate
marginal. Fubini applies to the integrable actual likelihood discrepancy. [the documented result](goal) Under [the stated assumptions](hyp:f,g,hf,hg,hf0,hg0). -/
-- @node: mixture_hellinger_conditional_integral
lemma mixture_hellinger_conditional_integral (n : ℕ)
    (f g : (Fin n → Record) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin n => recordReference)))
    (hg : Integrable g (Measure.pi (fun _ : Fin n => recordReference)))
    (hf0 : ∀ o, 0 ≤ f o) (hg0 : ∀ o, 0 ≤ g o) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => recordReference)) f g =
      ∫ x, Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
        (fun l => f (fun i => (x i, l i))) (fun l => g (fun i => (x i, l i)))
        ∂Measure.pi (fun _ : Fin n => uniformLaw) := by
  exact integral_original_records_conditional n _
    (mixture_hellinger_integrand_integrable _ f g hf hg hf0 hg0)

end CausalSmith.Stat.LogoddsLowsmoothFrontier

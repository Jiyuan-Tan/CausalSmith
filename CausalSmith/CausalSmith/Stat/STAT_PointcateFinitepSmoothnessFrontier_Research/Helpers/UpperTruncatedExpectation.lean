module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperExpectation

/-! Bounded-response disintegration identities for the numerator's original-record terms. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- A clipped response is bounded at every real threshold. -/
-- @node: upper_trunc_abs_bound
lemma upper_trunc_abs_bound (T y : ℝ) : |trunc T y| ≤ |T| := by
  by_cases hy : |y| ≤ T
  · simpa only [trunc, if_pos hy] using hy.trans (le_abs_self T)
  · simp only [trunc, if_neg hy, abs_zero]
    exact abs_nonneg _

/-- Integrating a bounded response and a treatment weight against the record kernel
retains the two original conditional arm integrals. -/
-- @node: upper_record_truncated_integral
lemma upper_record_truncated_integral (law : ObservedLaw) (x : unitInterval)
    (b : Bool → ℝ) (T : ℝ) :
    (∫ r : Bool × ℝ, b r.1 * trunc T r.2 ∂recordMeasure law.e law.Q x) =
      law.e x * (b true * ∫ y, trunc T y ∂law.Q true x) +
      (1-law.e x) * (b false * ∫ y, trunc T y ∂law.Q false x) := by
  have hbm : Measurable b := measurable_of_finite b
  have hmeas : Measurable (fun r : Bool × ℝ => b r.1 * trunc T r.2) := by fun_prop
  have hi (a : Bool) : Integrable (fun r : Bool × ℝ => b r.1 * trunc T r.2)
      ((Measure.dirac a).prod (law.Q a x)) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable ((|b true|+|b false|)*|T|)
    apply Filter.Eventually.of_forall
    intro r
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |b r.1| ≤ |b true|+|b false| := by
      cases r.1 <;> linarith [abs_nonneg (b true), abs_nonneg (b false)]
    exact mul_le_mul hb (upper_trunc_abs_bound T r.2) (abs_nonneg _) (by positivity)
  have he (a : Bool) : (∫ r : Bool × ℝ, b r.1 * trunc T r.2
      ∂((Measure.dirac a).prod (law.Q a x))) = b a * ∫ y, trunc T y ∂law.Q a x := by
    rw [Measure.dirac_prod, integral_map (by fun_prop) hmeas.aestronglyMeasurable]
    simpa only using integral_const_mul (b a) (trunc T)
  unfold recordMeasure
  rw [integral_add_measure ((hi true).smul_measure ENNReal.ofReal_ne_top)
    ((hi false).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, he]
  rw [ENNReal.toReal_ofReal (law.e_range x).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (law.e_range x).2)]

/-- Uniform design converts a bounded covariate-weighted clipped outcome into its
conditional arm integrals. -/
-- @node: upper_weighted_truncated_integral
lemma upper_weighted_truncated_integral (law : ObservedLaw) (hu : UniformDesign law)
    (f : unitInterval → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C)
    (b : Bool → ℝ) (T : ℝ) :
    (∫ o, f (X o) * (b (A o) * trunc T (Y o)) ∂law.P) =
      ∫ x, f x * (law.e x * (b true * ∫ y, trunc T y ∂law.Q true x) +
        (1-law.e x) * (b false * ∫ y, trunc T y ∂law.Q false x)) ∂design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let := completion_record_kernel_markov law
  have hbm : Measurable b := measurable_of_finite b
  have hmeas : Measurable (fun o : O => f (X o) * (b (A o) * trunc T (Y o))) := by
    unfold X A Y
    fun_prop
  have hi : Integrable (fun o => f (X o) * (b (A o) * trunc T (Y o))) law.P := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable (C*((|b true|+|b false|)*|T|))
    apply Filter.Eventually.of_forall
    intro o
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hb' : |b (A o)| ≤ |b true|+|b false| := by
      cases A o <;> linarith [abs_nonneg (b true), abs_nonneg (b false)]
    have hC : 0 ≤ C := (abs_nonneg _).trans (hb (X o))
    exact mul_le_mul (hb (X o))
      (mul_le_mul hb' (upper_trunc_abs_bound T (Y o)) (abs_nonneg _) (by positivity))
      (by positivity) hC
  have hv : law.P = design ⊗ₘ recordKernel law.e law.e_measurable law.Q :=
    law.record_version.trans (by rw [hu])
  rw [hv] at hi ⊢
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (∫ r : Bool × ℝ, f x * (b r.1 * trunc T r.2) ∂recordMeasure law.e law.Q x) = _
  rw [integral_const_mul, upper_record_truncated_integral]

/-- The unmarked clipped response integrates to the truncated marginal mean. -/
-- @node: upper_marginal_truncated_integral
lemma upper_marginal_truncated_integral (law : ObservedLaw) (hu : UniformDesign law)
    (f : unitInterval → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C)
    (T : ℝ) :
    (∫ o, f (X o) * trunc T (Y o) ∂law.P) = ∫ x, f x * truncatedMean law T x ∂design := by
  simpa only [one_mul, truncatedMean] using
    upper_weighted_truncated_integral law hu f hf C hb (fun _ => 1) T

/-- The treated clipped response integrates to the treated original conditional mean. -/
-- @node: upper_marked_truncated_integral
lemma upper_marked_truncated_integral (law : ObservedLaw) (hu : UniformDesign law)
    (f : unitInterval → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C)
    (T : ℝ) :
    (∫ o, f (X o) * (bit (A o) * trunc T (Y o)) ∂law.P) =
      ∫ x, f x * (law.e x * ∫ y, trunc T y ∂law.Q true x) ∂design := by
  simpa only [bit, Bool.false_eq_true, if_true, if_false, one_mul, zero_mul, mul_zero,
    add_zero] using upper_weighted_truncated_integral law hu f hf C hb bit T

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

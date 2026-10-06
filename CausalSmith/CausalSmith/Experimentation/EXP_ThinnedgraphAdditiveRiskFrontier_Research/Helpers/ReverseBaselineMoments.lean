module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalGraphMixture
public import Mathlib.Probability.Independence.Integration

/-!
# Integrating the independent baselines in the observable reverse test

Evenness removes the baseline mean and independent baseline coordinates remove
cross-row covariance. Compact support bounds the remaining diagonal energy.
-/

public section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A polynomial of a baseline coordinate is integrable on its compact support.  [For the stated data and conditions](hyp:B,i), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_coordinate_integrable
lemma reverse_baseline_coordinate_integrable (B : ℕ) (i : Fin B) :
    Integrable (fun U => U i) (blockBaselineLaw B) ∧
    Integrable (fun U => (U i) ^ 2) (blockBaselineLaw B) := by
  let := blockBaselineLaw_probability B
  constructor
  · apply (integrable_const (1 / 4 : ℝ)).mono' (measurable_pi_apply i).aestronglyMeasurable
    filter_upwards [blockBaselineLaw_ae_support B] with U hU
    simpa only [Real.norm_eq_abs] using hU i
  · apply (integrable_const (1 / 16 : ℝ)).mono' ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
    filter_upwards [blockBaselineLaw_ae_support B] with U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hi := hU i
    nlinarith [sq_abs (U i), abs_nonneg (U i)]

/-- Evenness of the actual joint baseline law centers each coordinate.  [For the stated data and conditions](hyp:B,i), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_coordinate_mean
lemma reverse_baseline_coordinate_mean (B : ℕ) (i : Fin B) :
    (∫ U, U i ∂blockBaselineLaw B) = 0 := by
  have ht := integral_map (show AEMeasurable (fun U : Fin B → ℝ => fun ℓ => -U ℓ)
    (blockBaselineLaw B) from (measurable_pi_lambda _ (fun ℓ =>
      (measurable_pi_apply ℓ).neg)).aemeasurable)
    (measurable_pi_apply i).aestronglyMeasurable
  rw [blockBaselineLaw_map_neg, integral_neg] at ht
  linarith

/-- Distinct independent baseline coordinates have zero mixed moment.  [For the stated data and conditions](hyp:B,i,j,hij), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_cross_moment
lemma reverse_baseline_cross_moment (B : ℕ) (i j : Fin B) (hij : i ≠ j) :
    (∫ U, U i * U j ∂blockBaselineLaw B) = 0 := by
  let μ := volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))
  let : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal cosSqDensity_integrable_normalized.1
        (Filter.Eventually.of_forall cosSqDensity_nonneg),
      cosSqDensity_integrable_normalized.2]
    simp
  have hind := (iIndepFun_pi (μ := fun _ : Fin B => μ)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have he := hind.integral_mul_eq_mul_integral
    (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable
  change (∫ U, U i * U j ∂blockBaselineLaw B) = _ at he
  change (∫ U, U i * U j ∂blockBaselineLaw B) =
    (∫ U, U i ∂blockBaselineLaw B) * (∫ U, U j ∂blockBaselineLaw B) at he
  rw [he, reverse_baseline_coordinate_mean, zero_mul]

/-- The baseline's diagonal second moment is bounded by its support radius.  [For the stated data and conditions](hyp:B,i), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_coordinate_second_le
lemma reverse_baseline_coordinate_second_le (B : ℕ) (i : Fin B) :
    (∫ U, (U i) ^ 2 ∂blockBaselineLaw B) ≤ 1 / 16 := by
  let := blockBaselineLaw_probability B
  calc
    _ ≤ ∫ _U, (1 / 16 : ℝ) ∂blockBaselineLaw B := by
      apply integral_mono_ae (reverse_baseline_coordinate_integrable B i).2
        (integrable_const _)
      filter_upwards [blockBaselineLaw_ae_support B] with U hU
      have hi := hU i
      nlinarith [sq_abs (U i), abs_nonneg (U i)]
    _ = _ := by simp

/-- A weighted baseline sum and its square are integrable without new premises.  [For the stated data and conditions](hyp:B,a), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_sum_integrable
lemma reverse_baseline_sum_integrable (B : ℕ) (a : Fin B → ℝ) :
    Integrable (fun U => ∑ i, a i * U i) (blockBaselineLaw B) ∧
    Integrable (fun U => (∑ i, a i * U i) ^ 2) (blockBaselineLaw B) := by
  let := blockBaselineLaw_probability B
  have hb : ∀ᵐ U ∂blockBaselineLaw B,
      |∑ i, a i * U i| ≤ ∑ i, |a i| / 4 := by
    filter_upwards [blockBaselineLaw_ae_support B] with U hU
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, div_eq_mul_inv]
    simpa using mul_le_mul_of_nonneg_left (hU i) (abs_nonneg (a i))
  constructor
  · exact integrable_finset_sum _ (fun i _ =>
      (reverse_baseline_coordinate_integrable B i).1.const_mul _)
  · apply (integrable_const ((∑ i, |a i| / 4) ^ 2)).mono'
      ((Finset.measurable_sum _ (fun i _ => (show Measurable (fun U : Fin B → ℝ => U i) from measurable_pi_apply i).const_mul (a i))).pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (∑ i, a i * U i), abs_nonneg (∑ i, a i * U i)]

/-- Independent centered baselines contribute only their diagonal energies.  [For the stated data and conditions](hyp:B,a), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_sum_second
lemma reverse_baseline_sum_second (B : ℕ) (a : Fin B → ℝ) :
    (∫ U, (∑ i, a i * U i) ^ 2 ∂blockBaselineLaw B) =
      ∑ i, a i ^ 2 * ∫ U, (U i) ^ 2 ∂blockBaselineLaw B := by
  let := blockBaselineLaw_probability B
  have hcross (i j : Fin B) : Integrable (fun U => U i * U j) (blockBaselineLaw B) := by
    apply (integrable_const (1 / 16 : ℝ)).mono'
      ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
    filter_upwards [blockBaselineLaw_ae_support B] with U hU
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    nlinarith [hU i, hU j, abs_nonneg (U i), abs_nonneg (U j)]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    by
      apply ((hcross i j).const_mul (a i * a j)).congr
      exact Filter.Eventually.of_forall (fun U => by ring)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ =>
    by
      apply ((hcross i j).const_mul (a i * a j)).congr
      exact Filter.Eventually.of_forall (fun U => by ring))]
  have he (j : Fin B) :
      (∫ U, a i * U i * (a j * U j) ∂blockBaselineLaw B) =
        if j = i then a i * a i * ∫ U, U i * U i ∂blockBaselineLaw B else 0 := by
    have hp (U : Fin B → ℝ) : a i * U i * (a j * U j) =
        (a i * a j) * (U i * U j) := by ring
    simp_rw [hp, integral_const_mul]
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, reverse_baseline_cross_moment B i j (Ne.symm hj)]
  simp_rw [he]
  simp

/-- Adding any fixed signal leaves only its squared value and baseline energy.  [For the stated data and conditions](hyp:B,a,c), [the stated conclusion holds](goal). -/
-- @node: reverse_baseline_shifted_second_le
lemma reverse_baseline_shifted_second_le (B : ℕ) (a : Fin B → ℝ) (c : ℝ) :
    (∫ U, ((∑ i, a i * U i) + c) ^ 2 ∂blockBaselineLaw B) ≤
      (∑ i, a i ^ 2) / 16 + c ^ 2 := by
  let := blockBaselineLaw_probability B
  have hm : (∫ U, (∑ i, a i * U i) ∂blockBaselineLaw B) = 0 := by
    rw [integral_finset_sum _ (fun i _ =>
      (reverse_baseline_coordinate_integrable B i).1.const_mul _)]
    simp_rw [integral_const_mul, reverse_baseline_coordinate_mean, mul_zero]
    simp
  have he (U : Fin B → ℝ) : ((∑ i, a i * U i) + c) ^ 2 =
      (∑ i, a i * U i) ^ 2 + 2 * c * (∑ i, a i * U i) + c ^ 2 := by ring
  simp_rw [he]
  have hlin := (reverse_baseline_sum_integrable B a).1
  have hsq := (reverse_baseline_sum_integrable B a).2
  integral_linearity
  rw [hm, mul_zero, add_zero, reverse_baseline_sum_second]
  simp only [integral_const, probReal_univ, one_smul]
  have henergy : (∑ i, a i ^ 2 * (∫ U, (U i) ^ 2 ∂blockBaselineLaw B)) ≤
      (∑ i, a i ^ 2) / 16 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (reverse_baseline_coordinate_second_le B i) (sq_nonneg (a i))
  linarith

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

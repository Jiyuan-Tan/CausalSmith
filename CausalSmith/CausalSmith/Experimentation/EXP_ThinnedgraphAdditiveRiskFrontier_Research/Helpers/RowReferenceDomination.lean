module
public import Causalean.Mathlib.Probability.ProductAbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.Pi
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelEnergy

/-!
# Domination of translated rows by their reference law

The finite reference mixture controls each row likelihood, including the zero-density
set. These bounds justify the finite integrals in the hidden-allocation roadmap.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Each component of the uniform reference mixture is bounded by its number of components
 times the mixture density.  [For the stated data and conditions](hyp:d,h,w,ε), [the stated conclusion holds](goal). -/
-- @node: rowDensity_le_reference
lemma rowDensity_le_reference (d : ℕ) (h w : ℝ) (ε : Fin d → Bool) :
    rowDensity d h ε w ≤ (2 : ℝ) ^ d * refDensity d h w := by
  have hs := Finset.single_le_sum (fun δ _ => cosSqDensity_nonneg
    (w - h / (2 * d) * ∑ j, signOf (δ j))) (Finset.mem_univ ε)
  simpa only [refDensity, rowDensity, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ d ≠ 0),
    one_mul] using hs

/-- The row likelihood is nonnegative and bounded on the entire real line, with the
 conventional zero value at a zero of the reference density.  [For the stated data and conditions](hyp:d,h,w,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_bounds
lemma rowLikelihood_bounds (d : ℕ) (h w : ℝ) (ε : Fin d → Bool) :
    0 ≤ rowDensity d h ε w / refDensity d h w ∧
      rowDensity d h ε w / refDensity d h w ≤ (2 : ℝ) ^ d := by
  constructor
  · exact div_nonneg (cosSqDensity_nonneg _) (refDensity_nonneg d h w)
  · by_cases hz : refDensity d h w = 0
    · rw [hz, div_zero]; positivity
    · exact (div_le_iff₀ (lt_of_le_of_ne (refDensity_nonneg d h w) (Ne.symm hz))).mpr
        (rowDensity_le_reference d h w ε)

/-- Multiplying the likelihood by the reference recovers the component density even on
 the zero-density set.  [For the stated data and conditions](hyp:d,h,w,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_mul_reference
lemma rowLikelihood_mul_reference (d : ℕ) (h w : ℝ) (ε : Fin d → Bool) :
    (rowDensity d h ε w / refDensity d h w) * refDensity d h w =
      rowDensity d h ε w := by
  by_cases hz : refDensity d h w = 0
  · rw [hz, mul_zero, rowDensity_eq_zero_of_refDensity_eq_zero d h w hz ε]
  · exact div_mul_cancel₀ _ hz

/-- Each translated row law is bounded by a finite multiple of the reference law.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLaw_le_reference
lemma rowLaw_le_reference (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    volume.withDensity (fun w => ENNReal.ofReal (rowDensity d h ε w)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) •
        volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w)) := by
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (rowDensity d h ε w) ≤
    ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (refDensity d h w)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ d)]
  exact ENNReal.ofReal_le_ofReal (rowDensity_le_reference d h w ε)

/-- The reference law dominates every sign-conditioned translated row law.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLaw_absolutelyContinuous_reference
lemma rowLaw_absolutelyContinuous_reference (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    volume.withDensity (fun w => ENNReal.ofReal (rowDensity d h ε w)) ≪
      volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w)) := by
  exact Measure.absolutelyContinuous_of_le_smul (rowLaw_le_reference d h ε)

/-- Reweighting the reference by the bounded row likelihood gives the exact translated law.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLaw_eq_reference_withDensity
lemma rowLaw_eq_reference_withDensity (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    volume.withDensity (fun w => ENNReal.ofReal (rowDensity d h ε w)) =
      (volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))).withDensity
        (fun w => ENNReal.ofReal (rowDensity d h ε w / refDensity d h w)) := by
  rw [← withDensity_mul volume (by fun_prop) (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [] with w
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (refDensity_nonneg d h w), mul_comm,
    rowLikelihood_mul_reference]

/-- A normalized reference density defines a probability law.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: referenceRowLaw_probability
lemma referenceRowLaw_probability (d : ℕ) (h : ℝ) :
    IsProbabilityMeasure (volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (refDensity_integrable_normalized d h).1
      (Filter.Eventually.of_forall (refDensity_nonneg d h)),
    (refDensity_integrable_normalized d h).2]
  simp

/-- Each translated component is a probability law.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: translatedRowLaw_probability
lemma translatedRowLaw_probability (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    IsProbabilityMeasure (volume.withDensity (fun w => ENNReal.ofReal (rowDensity d h ε w))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (rowDensity_integrable_normalized d h ε).1
      (Filter.Eventually.of_forall (fun w => cosSqDensity_nonneg
        (w - h / (2 * d) * ∑ j, signOf (ε j)))),
    (rowDensity_integrable_normalized d h ε).2]
  simp

/-- The exact bounded likelihood integrates to one under the reference law.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_integral_reference
lemma rowLikelihood_integral_reference (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    (∫ w, rowDensity d h ε w / refDensity d h w
      ∂volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) = 1 := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (refDensity_nonneg d h _), smul_eq_mul]
  simp_rw [mul_comm (refDensity d h _), rowLikelihood_mul_reference]
  exact (rowDensity_integrable_normalized d h ε).2

/-- Independent rows with arbitrary fixed sign vectors are dominated by the independent
reference responses. This does not replace the constrained allocation by independent signs.  [For the stated data and conditions](hyp:B,d,h,ε), [the stated conclusion holds](goal). -/
-- @node: translatedRows_absolutelyContinuous_reference
lemma translatedRows_absolutelyContinuous_reference (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    Measure.pi (fun ℓ => volume.withDensity (fun w => ENNReal.ofReal (rowDensity d h (ε ℓ) w))) ≪
      Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w))) := by
  let ν := volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))
  let μ := fun δ : Fin d → Bool => volume.withDensity
    (fun w => ENNReal.ofReal (rowDensity d h δ w))
  let := referenceRowLaw_probability d h
  haveI (δ : Fin d → Bool) : IsProbabilityMeasure (μ δ) := translatedRowLaw_probability d h δ
  change Measure.pi (fun ℓ => μ (ε ℓ)) ≪ Measure.pi (fun _ : Fin B => ν)
  induction B with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ B ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (B + 1) => ℝ) 0
    have hμ := (measurePreserving_piFinSuccAbove (fun ℓ => μ (ε ℓ)) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (B + 1) => ν) 0).map_eq
    have hprod := (rowLaw_absolutelyContinuous_reference d h (ε 0)).prod
      (ih (fun ℓ => ε ((0 : Fin (B + 1)).succAbove ℓ)))
    have hmap : (Measure.pi (fun ℓ => μ (ε ℓ))).map e ≪
        (Measure.pi (fun _ : Fin (B + 1) => ν)).map e := by
      rw [hμ, hν]
      exact hprod
    have hmapped := hmap.map (f := e.symm) e.symm.measurable
    rwa [Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id,
      Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id] at hmapped

/-- A product of row likelihoods is bounded by the product of their finite row bounds.  [For the stated data and conditions](hyp:B,d,h,ε,y), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_product_bounds
lemma rowLikelihood_product_bounds (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) (y : Fin B → ℝ) :
    0 ≤ (∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ)) ∧
      (∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ)) ≤
        ((2 : ℝ) ^ d) ^ B := by
  constructor
  · exact Finset.prod_nonneg (fun ℓ _ => (rowLikelihood_bounds d h (y ℓ) (ε ℓ)).1)
  · calc
      _ ≤ ∏ _ : Fin B, (2 : ℝ) ^ d := Finset.prod_le_prod
        (fun ℓ _ => (rowLikelihood_bounds d h (y ℓ) (ε ℓ)).1)
        (fun ℓ _ => (rowLikelihood_bounds d h (y ℓ) (ε ℓ)).2)
      _ = _ := by simp

/-- [A finite product of the total row likelihoods is measurable, including at reference zeros](goal). -/
-- @node: rowLikelihood_product_measurable
@[fun_prop]
lemma rowLikelihood_product_measurable (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    Measurable (fun y : Fin B → ℝ =>
      ∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ)) := by
  apply Finset.measurable_prod
  intro ℓ _
  exact ((rowDensity_measurable d h (ε ℓ)).comp (measurable_pi_apply ℓ)).div
    ((refDensity_measurable d h).comp (measurable_pi_apply ℓ))

/-- A fixed-allocation likelihood is integrable under the independent reference responses.  [For the stated data and conditions](hyp:B,d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_product_integrable
lemma rowLikelihood_product_integrable (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    Integrable (fun y : Fin B → ℝ =>
      ∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ))
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
  let := referenceRowLaw_probability d h
  apply (integrable_const (((2 : ℝ) ^ d) ^ B)).mono'
    (rowLikelihood_product_measurable B d h ε).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (rowLikelihood_product_bounds B d h ε y).1]
  exact (rowLikelihood_product_bounds B d h ε y).2

/-- Fixed-allocation likelihoods have finite second moments under the reference law.  [For the stated data and conditions](hyp:B,d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_product_sq_integrable
lemma rowLikelihood_product_sq_integrable (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    Integrable (fun y : Fin B → ℝ =>
      (∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ)) ^ 2)
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
  let := referenceRowLaw_probability d h
  apply (integrable_const ((((2 : ℝ) ^ d) ^ B) ^ 2)).mono'
    ((rowLikelihood_product_measurable B d h ε).pow_const 2).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (rowLikelihood_product_bounds B d h ε y).1
    (rowLikelihood_product_bounds B d h ε y).2 2

/-- The product likelihood remains normalized because its reference responses are independent.  [For the stated data and conditions](hyp:B,d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowLikelihood_product_integral_reference
lemma rowLikelihood_product_integral_reference (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    (∫ y : Fin B → ℝ, ∏ ℓ, rowDensity d h (ε ℓ) (y ℓ) / refDensity d h (y ℓ)
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) = 1 := by
  let := referenceRowLaw_probability d h
  rw [integral_fintype_prod_eq_prod
    (fun ℓ w => rowDensity d h (ε ℓ) w / refDensity d h w)]
  simp_rw [rowLikelihood_integral_reference]
  exact Finset.prod_const_one

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

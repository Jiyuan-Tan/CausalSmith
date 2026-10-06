module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentPartition

/-! Normalization of the joint null and intermediate full-label component laws. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The two coarse signs and their conditional coefficient laws form a normalized mixture. [This is the stated conclusion](goal). -/
-- @node: component_sign_pair_weight_sum
lemma component_sign_pair_weight_sum (K M : ℕ) (δ : Disclosure K) :
    (∑ t : Bool × CoefficientPairs K,
      conditionalPairWeight true K M (fun _ => t.1) δ t.2 / 2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div, conditionalPairWeight_sum]
  norm_num

/-- The intermediate component density is the actual finite mixture over its two coarse signs and all undisclosed coefficient pairs. [This is the stated conclusion](goal). -/
-- @node: averageComponent_eq_sign_pair_mixture
lemma averageComponent_eq_sign_pair_mixture (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    averageComponent n K M a u aug C labels =
      ∑ t : Bool × CoefficientPairs K,
        (conditionalPairWeight true K M (fun _ => t.1) aug.2.2 t.2 / 2) *
          ∏ i ∈ C, labelDensity true K M a u ((fun _ => t.1), t.2)
            (aug.1 i) (aug.2.1 i) (labels i) := by
  rw [Fintype.sum_prod_type]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  simp [averageComponent, componentDensity]

/-- The product of the complete null component densities has unit fair-label mass. The proof uses the observation partition, not coefficient-independence assumptions. [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_sum
lemma nullConditionalDensity_sum (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) :
    (∑ labels : Labels n, nullConditionalDensity n K M a u aug labels) = (4:ℝ)^n := by
  classical
  have hmix := component_partition_mixture_sum n K M aug
    (fun _ pairs => conditionalPairWeight false K M (fun _ => false) aug.2.2 pairs)
    (fun _ pairs i label => labelDensity false K M a u ((fun _ => false), pairs)
      (aug.1 i) (aug.2.1 i) label)
    (fun _ => conditionalPairWeight_sum false K M (fun _ => false) aug.2.2)
    (fun _ pairs i => labelDensity_sum false K M a u ((fun _ => false), pairs)
      (aug.1 i) (aug.2.1 i))
  change (∑ labels : Labels n, ∏ C : {C // C ∈ components n K M aug},
    nullComponent n K M a u aug C.val labels) = _ at hmix
  have hp (labels : Labels n) := Finset.prod_coe_sort (components n K M aug)
    (fun C => nullComponent n K M a u aug C labels)
  simp_rw [hp] at hmix
  exact hmix

/-- Independent sign-averaged component laws define a normalized intermediate probability density on every full-label alphabet, including unused zero-mark labels. [This is the stated conclusion](goal). -/
-- @node: intermediateDensity_sum
lemma intermediateDensity_sum (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) :
    (∑ labels : Labels n, intermediateDensity n K M a u aug labels) = (4:ℝ)^n := by
  classical
  have hmix := component_partition_mixture_sum n K M aug
    (fun _ (t : Bool × CoefficientPairs K) =>
      conditionalPairWeight true K M (fun _ => t.1) aug.2.2 t.2 / 2)
    (fun _ (t : Bool × CoefficientPairs K) i label =>
      labelDensity true K M a u ((fun _ => t.1), t.2) (aug.1 i) (aug.2.1 i) label)
    (fun _ => component_sign_pair_weight_sum K M aug.2.2)
    (fun _ t i => labelDensity_sum true K M a u ((fun _ => t.1), t.2)
      (aug.1 i) (aug.2.1 i))
  simp_rw [← averageComponent_eq_sign_pair_mixture] at hmix
  have hp (labels : Labels n) := Finset.prod_coe_sort (components n K M aug)
    (fun C => averageComponent n K M a u aug C labels)
  simp_rw [hp] at hmix
  exact hmix

/-- The joint null law is a probability law with the actual positive product denominator. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: nullConditionalLaw_isProbabilityMeasure
lemma nullConditionalLaw_isProbabilityMeasure (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16) (aug : Augmentation n K) :
    IsProbabilityMeasure (nullConditionalLaw n K M a u aug) := by
  apply fairLabelMeasure_isProbabilityMeasure
  · intro labels
    apply Finset.prod_nonneg
    intro C _
    exact le_trans (by positivity) (component_denominator_bounds n K M a u hK ha hu aug C labels).1
  · exact nullConditionalDensity_sum n K M a u aug

/-- The joint intermediate law is a probability law with the actual positive product denominator. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: intermediateConditionalLaw_isProbabilityMeasure
lemma intermediateConditionalLaw_isProbabilityMeasure (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16) (aug : Augmentation n K) :
    IsProbabilityMeasure (intermediateConditionalLaw n K M a u aug) := by
  apply fairLabelMeasure_isProbabilityMeasure
  · intro labels
    apply Finset.prod_nonneg
    intro C _
    exact le_trans (by positivity) (component_denominator_bounds n K M a u hK ha hu aug C labels).2
  · exact intermediateDensity_sum n K M a u aug

end CausalSmith.Stat.FinitepHomogeneityDensegamma

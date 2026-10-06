module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentMixedSlope

/-! The second propensity jet of a finite component likelihood. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The first propensity jet of the even discrepancy. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: evenDiscrepancyPropensityDerivative
def evenDiscrepancyPropensityDerivative (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentPropensityDerivative true true n K M a u aug C labels +
    componentPropensityDerivative true false n K M a u aug C labels) / 2 -
    componentPropensityDerivative false false n K M a u aug C labels

/-- One propensity differentiation of the even discrepancy gives its concrete first jet. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_first_propensity_jet
lemma evenDiscrepancy_first_propensity_jet (n K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n))
    (labels : Labels n) :
    HasDerivAt (fun b => evenDiscrepancy n K M b u aug C labels)
      (evenDiscrepancyPropensityDerivative n K M a u aug C labels) a := by
  exact (((componentDensity_hasDerivAt_propensity true true n K M a u ha aug C labels).add
    (componentDensity_hasDerivAt_propensity true false n K M a u ha aug C labels)).div_const 2).sub
      (componentDensity_hasDerivAt_propensity false false n K M a u ha aug C labels)

/-- The concrete first propensity jet has the required value zero on the propensity axis. [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancyPropensityDerivative_zero
lemma evenDiscrepancyPropensityDerivative_zero (n K M : ℕ) (u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    evenDiscrepancyPropensityDerivative n K M 0 u aug C labels = 0 := by
  exact (evenDiscrepancy_first_propensity_jet n K M 0 u (by norm_num) aug C labels).unique
    (evenDiscrepancy_hasDerivAt_propensity_zero n K M u aug C labels)

/-- The exact second propensity derivative of a component likelihood. The first summand assigns the two differentiations to distinct records; the second assigns both to one record. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: componentPropensityCurvature
def componentPropensityCurvature (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ i ∈ C,
      ((∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j,
          labelDensity ν K M a u ((fun _ => s),p) (aug.1 k) (aug.2.1 k) (labels k)) *
            labelPropensityDerivative ν K M a u ((fun _ => s),p)
              (aug.1 j) (aug.2.1 j) (labels j)) *
          labelPropensityDerivative ν K M a u ((fun _ => s),p)
            (aug.1 i) (aug.2.1 i) (labels i) +
        (∏ j ∈ C.erase i,
          labelDensity ν K M a u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
            labelPropensityCurvature ν K M a u ((fun _ => s),p)
              (aug.1 i) (aug.2.1 i) (labels i))

/-- Differentiating the first propensity component jet gives the exact second jet. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: componentPropensityDerivative_hasDerivAt_propensity
lemma componentPropensityDerivative_hasDerivAt_propensity (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentPropensityDerivative ν s n K M b u aug C labels)
      (componentPropensityCurvature ν s n K M a u aug C labels) a := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (HasDerivAt.fun_finsetProd (fun j _ =>
    labelDensity_hasDerivAt_propensity ν K M a u ha _ _ _ _)).mul
      (labelPropensityDerivative_hasDerivAt ν K M a u ha _ _ _ _)

/-- The concrete second propensity component jet has the same quadratic record-count envelope as the mixed first jet. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_propensity_curvature_bound
lemma component_propensity_curvature_bound (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |componentPropensityCurvature ν s n K M a u aug C labels| ≤
      16*(C.card:ℝ)^2*2^C.card := by
  apply conditionalPairWeight_abs_average_bound
  intro p
  apply record_product_mixed_slope_bound
  · intro i _
    exact labelDensity_abs_le_two_closed ν K M a u hK ha hu ((fun _ => s),p)
      (aug.1 i) (aug.2.1 i) (labels i)
  · intro i _
    exact (label_propensity_derivative_bounds ν K M hK a u ha hu
      ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).1
  · intro i _
    exact (label_propensity_derivative_bounds ν K M hK a u ha hu
      ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).1
  · intro i _
    exact (label_propensity_derivative_bounds ν K M hK a u ha hu
      ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).2

/-- The `(2,0)` jet of the even discrepancy. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: evenDiscrepancyPropensityCurvature
def evenDiscrepancyPropensityCurvature (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentPropensityCurvature true true n K M a u aug C labels +
    componentPropensityCurvature true false n K M a u aug C labels) / 2 -
    componentPropensityCurvature false false n K M a u aug C labels

/-- Two propensity differentiations of the even discrepancy give its concrete `(2,0)` jet. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_second_propensity_jet
lemma evenDiscrepancy_second_propensity_jet (n K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n))
    (labels : Labels n) :
    HasDerivAt (fun b => evenDiscrepancyPropensityDerivative n K M b u aug C labels)
      (evenDiscrepancyPropensityCurvature n K M a u aug C labels) a := by
  unfold evenDiscrepancyPropensityDerivative
  exact (((componentPropensityDerivative_hasDerivAt_propensity true true n K M a u ha
    aug C labels).add
      (componentPropensityDerivative_hasDerivAt_propensity true false n K M a u ha
        aug C labels)).div_const 2).sub
          (componentPropensityDerivative_hasDerivAt_propensity false false n K M a u ha
            aug C labels)

/-- The even discrepancy `(2,0)` jet has a uniform component envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_propensity_curvature_bound
lemma evenDiscrepancy_propensity_curvature_bound (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |evenDiscrepancyPropensityCurvature n K M a u aug C labels| ≤
      32*(C.card:ℝ)^2*2^C.card := by
  have hp := component_propensity_curvature_bound true true n K M a u hK ha hu aug C labels
  have hm := component_propensity_curvature_bound true false n K M a u hK ha hu aug C labels
  have h0 := component_propensity_curvature_bound false false n K M a u hK ha hu aug C labels
  unfold evenDiscrepancyPropensityCurvature
  calc
    |(componentPropensityCurvature true true n K M a u aug C labels +
        componentPropensityCurvature true false n K M a u aug C labels) / 2 -
        componentPropensityCurvature false false n K M a u aug C labels| ≤
      |(componentPropensityCurvature true true n K M a u aug C labels +
        componentPropensityCurvature true false n K M a u aug C labels) / 2| +
        |componentPropensityCurvature false false n K M a u aug C labels| := abs_sub _ _
    _ ≤
      (|componentPropensityCurvature true true n K M a u aug C labels| +
        |componentPropensityCurvature true false n K M a u aug C labels|) / 2 +
        |componentPropensityCurvature false false n K M a u aug C labels| := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact add_le_add
            ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
              (abs_add_le _ _)) le_rfl
    _ ≤ 32*(C.card:ℝ)^2*2^C.card := by linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma

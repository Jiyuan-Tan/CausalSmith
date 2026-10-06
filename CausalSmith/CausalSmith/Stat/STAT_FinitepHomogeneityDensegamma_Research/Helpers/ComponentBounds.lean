module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDensity
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.FrameBounds

/-! Positive normalized coefficient averages and full-label component denominator bounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Disclosure fixes some coefficient pairs and leaves normalized copula weights at all other nodes. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_sum
lemma conditionalPairWeight_sum (ν : Bool) (K M : ℕ) (σ : Fin (M/2) → Bool)
    (δ : Disclosure K) : ∑ pairs : CoefficientPairs K, conditionalPairWeight ν K M σ δ pairs = 1 := by
  unfold conditionalPairWeight
  let w (i : Fin (K+1)) (p : Bool × Bool) : ℝ :=
    match δ i with
    | some q => if p = q then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) p.1 p.2
  have he : (∑ pairs : CoefficientPairs K, ∏ i, w i (pairs i)) = ∏ i, ∑ p, w i p :=
    (Fintype.prod_sum w).symm
  change (∑ pairs : CoefficientPairs K, ∏ i, w i (pairs i)) = 1
  rw [he]
  dsimp only [w]
  have hs (i : Fin (K+1)) :
      (∑ p : Bool × Bool, match δ i with
        | some q => if p = q then (1:ℝ) else 0
        | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) p.1 p.2) = 1 := by
    cases δ i with
    | some q => simp
    | none => exact pairWeight_sum _ _
  simp_rw [hs]
  simp

/-- Every conditional coefficient weight is nonnegative, including arbitrary fixed disclosure values. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_nonneg
lemma conditionalPairWeight_nonneg (ν : Bool) (K M : ℕ) (σ : Fin (M/2) → Bool)
    (δ : Disclosure K) (pairs : CoefficientPairs K) :
    0 ≤ conditionalPairWeight ν K M σ δ pairs := by
  unfold conditionalPairWeight
  apply Finset.prod_nonneg
  intro i _
  cases δ i with
  | some q => simp only; split <;> norm_num
  | none => exact pairWeight_nonneg _ _ (coarseTent_abs_le_one _ _ _) _ _

/-- Both marked and unmarked full-record label densities stay uniformly inside the positive envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: labelDensity_bounds
lemma labelDensity_bounds (ν : Bool) (K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    1/2 ≤ labelDensity ν K M a u idx x marked label ∧
      labelDensity ν K M a u idx x marked label ≤ 2 := by
  obtain ⟨hξ, hυ, hζ⟩ := copula_coordinates_abs_bounds K M hK a u ha hu ν idx x
  have hξ' := abs_le.mp hξ
  have hυ' := abs_le.mp hυ
  have hζ' := abs_le.mp hζ
  rcases label with ⟨l, h⟩
  cases marked <;> cases l <;> cases h <;>
    simp only [labelDensity, signVal, Bool.false_eq_true, ↓reduceIte,
      one_mul, neg_one_mul, mul_one, mul_neg_one] <;> constructor <;> linarith

/-- Averaging positive record products over normalized coefficient weights preserves the occupancy envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: componentDensity_bounds
lemma componentDensity_bounds (ν sign : Bool) (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    (1/2:ℝ)^C.card ≤ componentDensity ν sign n K M a u aug C labels ∧
      componentDensity ν sign n K M a u aug C labels ≤ (2:ℝ)^C.card := by
  have hp (pairs : CoefficientPairs K) :
      (1/2:ℝ)^C.card ≤ ∏ i ∈ C, labelDensity ν K M a u ((fun _ => sign), pairs)
        (aug.1 i) (aug.2.1 i) (labels i) ∧
      (∏ i ∈ C, labelDensity ν K M a u ((fun _ => sign), pairs)
        (aug.1 i) (aug.2.1 i) (labels i)) ≤ (2:ℝ)^C.card := by
    constructor
    · rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ => by norm_num)
      intro i _
      exact (labelDensity_bounds _ _ _ _ _ hK ha hu _ _ _ _).1
    · rw [← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro i _
        exact (by linarith [(labelDensity_bounds ν K M a u hK ha hu
          ((fun _ => sign), pairs) (aug.1 i) (aug.2.1 i) (labels i)).1])
      · intro i _
        exact (labelDensity_bounds _ _ _ _ _ hK ha hu _ _ _ _).2
  unfold componentDensity
  have hs := conditionalPairWeight_sum ν K M (fun _ => sign) aug.2.2
  constructor
  · calc
      _ = ∑ pairs, conditionalPairWeight ν K M (fun _ => sign) aug.2.2 pairs * (1/2:ℝ)^C.card := by
        rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun pairs _ => mul_le_mul_of_nonneg_left
        (hp pairs).1 (conditionalPairWeight_nonneg _ _ _ _ _ _))
  · calc
      _ ≤ ∑ pairs, conditionalPairWeight ν K M (fun _ => sign) aug.2.2 pairs * (2:ℝ)^C.card :=
        Finset.sum_le_sum (fun pairs _ => mul_le_mul_of_nonneg_left
          (hp pairs).2 (conditionalPairWeight_nonneg _ _ _ _ _ _))
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

/-- The null and intermediate denominator bounds apply to every design and every finite component. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_denominator_bounds
lemma component_denominator_bounds (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    (1/2:ℝ)^C.card ≤ nullComponent n K M a u aug C labels ∧
    (1/2:ℝ)^C.card ≤ averageComponent n K M a u aug C labels := by
  refine ⟨(componentDensity_bounds false false n K M a u hK ha hu aug C labels).1, ?_⟩
  have hp := (componentDensity_bounds true true n K M a u hK ha hu aug C labels).1
  have hm := (componentDensity_bounds true false n K M a u hK ha hu aug C labels).1
  unfold averageComponent
  linarith

/-- Summing all fair treatment and mark signs cancels every label-density perturbation. [This is the stated conclusion](goal). -/
-- @node: labelDensity_sum
lemma labelDensity_sum (ν : Bool) (K M : ℕ) (a u : ℝ) (idx : CopulaIndex K M)
    (x : unitInterval) (marked : Bool) :
    ∑ label : Bool × Bool, labelDensity ν K M a u idx x marked label = 4 := by
  cases marked <;> simp [Fintype.sum_prod_type, labelDensity, signVal] <;> ring

/-- A component likelihood is normalized on the entire fair-label alphabet, including unused labels. [This is the stated conclusion](goal). -/
-- @node: componentDensity_sum
lemma componentDensity_sum (ν sign : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    ∑ labels : Labels n, componentDensity ν sign n K M a u aug C labels = (4:ℝ)^n := by
  have hp (pairs : CoefficientPairs K) :
      (∑ labels : Labels n, ∏ i ∈ C, labelDensity ν K M a u ((fun _ => sign), pairs)
        (aug.1 i) (aug.2.1 i) (labels i)) = (4:ℝ)^n := by
    let w (i : Fin n) (label : Bool × Bool) : ℝ :=
      if i ∈ C then labelDensity ν K M a u ((fun _ => sign), pairs)
        (aug.1 i) (aug.2.1 i) label else 1
    have hw (labels : Labels n) :
        (∏ i ∈ C, labelDensity ν K M a u ((fun _ => sign), pairs)
          (aug.1 i) (aug.2.1 i) (labels i)) = ∏ i : Fin n, w i (labels i) := by
      simp [w]
    simp_rw [hw]
    rw [← Fintype.prod_sum w]
    have hs (i : Fin n) : ∑ label : Bool × Bool, w i label = 4 := by
      by_cases hi : i ∈ C
      · simp only [w, if_pos hi]
        exact labelDensity_sum _ _ _ _ _ _ _ _
      · simp [w, hi]
    simp_rw [hs]
    simp
  unfold componentDensity
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hp]
  rw [← Finset.sum_mul, conditionalPairWeight_sum, one_mul]

/-- Averaging the two normalized component densities preserves normalization. [This is the stated conclusion](goal). -/
-- @node: averageComponent_sum
lemma averageComponent_sum (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    ∑ labels : Labels n, averageComponent n K M a u aug C labels = (4:ℝ)^n := by
  simp only [averageComponent]
  rw [← Finset.sum_div, Finset.sum_add_distrib, componentDensity_sum, componentDensity_sum]
  ring

/-- The fair-label prefactor cancels the cardinality of the complete label alphabet. [This is the stated conclusion](goal). -/
-- @node: fair_label_cardinality
lemma fair_label_cardinality (n : ℕ) :
    (4:ℝ)^(-(n:ℤ)) * (Fintype.card (Labels n):ℝ) = 1 := by
  simp [Labels, Fintype.card_fun, Fintype.card_prod, ← Nat.cast_pow, zpow_neg]
  norm_num

/-- Complete-record likelihoods sum to the fair-label cardinality before latent averaging. [This is the stated conclusion](goal). -/
-- @node: fullLabelLikelihood_sum
lemma fullLabelLikelihood_sum (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (aug : Augmentation n K) :
    (∑ labels : Labels n, ∏ i : Fin n,
      labelDensity ν K M a u idx (aug.1 i) (aug.2.1 i) (labels i)) = (4:ℝ)^n := by
  rw [← Fintype.prod_sum]
  simp_rw [labelDensity_sum]
  simp

/-- Averaging normalized coefficient weights and undisclosed coarse signs preserves total mass. [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalDensity_sum
lemma alternativeConditionalDensity_sum (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) :
    ∑ labels : Labels n, alternativeConditionalDensity n K M a u aug labels = (4:ℝ)^n := by
  unfold alternativeConditionalDensity
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (σ : Fin (M/2) → Bool) :
      (∑ labels : Labels n, ∑ pairs : CoefficientPairs K,
        conditionalPairWeight true K M σ aug.2.2 pairs *
          ∏ i : Fin n, labelDensity true K M a u (σ,pairs)
            (aug.1 i) (aug.2.1 i) (labels i)) = (4:ℝ)^n := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fullLabelLikelihood_sum]
    rw [← Finset.sum_mul, conditionalPairWeight_sum, one_mul]
  simp_rw [hs]
  simp [Fintype.card_fun, ← Nat.cast_pow, zpow_neg]
  field_simp
  norm_cast

/-- The complete alternative label density is nonnegative for every disclosed design. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalDensity_nonneg
lemma alternativeConditionalDensity_nonneg (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (labels : Labels n) :
    0 ≤ alternativeConditionalDensity n K M a u aug labels := by
  unfold alternativeConditionalDensity
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro σ _
  apply Finset.sum_nonneg
  intro pairs _
  apply mul_nonneg (conditionalPairWeight_nonneg _ _ _ _ _ _)
  apply Finset.prod_nonneg
  intro i _
  exact le_trans (by norm_num) (labelDensity_bounds true K M a u hK ha hu
    (σ, pairs) (aug.1 i) (aug.2.1 i) (labels i)).1

/-- A nonnegative normalized finite fair-label density defines an actual probability measure. This statement assumes [the hpos condition](hyp:hpos), [the hsum condition](hyp:hsum). [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_isProbabilityMeasure
lemma fairLabelMeasure_isProbabilityMeasure (n : ℕ) (density : Labels n → ℝ)
    (hpos : ∀ labels, 0 ≤ density labels)
    (hsum : ∑ labels, density labels = (4:ℝ)^n) :
    IsProbabilityMeasure (fairLabelMeasure n density) := by
  constructor
  simp only [fairLabelMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun labels _ => mul_nonneg (by positivity) (hpos labels)),
    ← Finset.mul_sum, hsum]
  simp [zpow_neg]

/-- The actual alternative conditional law is normalized without discarding any record category. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalLaw_isProbabilityMeasure
lemma alternativeConditionalLaw_isProbabilityMeasure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) :
    IsProbabilityMeasure (alternativeConditionalLaw n K M a u aug) := by
  exact fairLabelMeasure_isProbabilityMeasure n _
    (alternativeConditionalDensity_nonneg n K M a u hK ha hu aug)
    (alternativeConditionalDensity_sum n K M a u aug)

/-- The null component density has exactly the fair-label total mass. [This is the stated conclusion](goal). -/
-- @node: nullComponent_sum
lemma nullComponent_sum (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    ∑ labels : Labels n, nullComponent n K M a u aug C labels = (4:ℝ)^n :=
  componentDensity_sum false false n K M a u aug C

/-- The even component discrepancy has zero label mean against its actual null density. [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_sum_zero
lemma evenDiscrepancy_sum_zero (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    ∑ labels : Labels n, evenDiscrepancy n K M a u aug C labels = 0 := by
  simp only [evenDiscrepancy, Finset.sum_sub_distrib, averageComponent_sum,
    nullComponent_sum, sub_self]

/-- The odd component discrepancy has zero label mean before the coarse sign is mixed. [This is the stated conclusion](goal). -/
-- @node: oddDiscrepancy_sum_zero
lemma oddDiscrepancy_sum_zero (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    ∑ labels : Labels n, oddDiscrepancy n K M a u aug C labels = 0 := by
  simp only [oddDiscrepancy, ← Finset.sum_div, Finset.sum_sub_distrib,
    componentDensity_sum, sub_self, zero_div]

/-- Each actual null component and sign-averaged component defines a normalized probability law. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: componentLabelLaws_isProbabilityMeasure
lemma componentLabelLaws_isProbabilityMeasure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    IsProbabilityMeasure (fairLabelMeasure n (nullComponent n K M a u aug C)) ∧
    IsProbabilityMeasure (fairLabelMeasure n (averageComponent n K M a u aug C)) := by
  have hp (labels : Labels n) := component_denominator_bounds n K M a u hK ha hu aug C labels
  constructor
  · exact fairLabelMeasure_isProbabilityMeasure n _
      (fun labels => le_trans (by positivity) (hp labels).1)
      (nullComponent_sum n K M a u aug C)
  · exact fairLabelMeasure_isProbabilityMeasure n _
      (fun labels => le_trans (by positivity) (hp labels).2)
      (averageComponent_sum n K M a u aug C)

/-- The odd discrepancy is dominated by its sign-averaged density, so its activity is at most one. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: componentOddActivity_le_one
lemma componentOddActivity_le_one (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    componentOddActivity n K M a u aug C ≤ 1 := by
  have hterm (labels : Labels n) :
      oddDiscrepancy n K M a u aug C labels^2/averageComponent n K M a u aug C labels ≤
        averageComponent n K M a u aug C labels := by
    have hp := (componentDensity_bounds true true n K M a u hK ha hu aug C labels).1
    have hm := (componentDensity_bounds true false n K M a u hK ha hu aug C labels).1
    have hp0 : 0 ≤ componentDensity true true n K M a u aug C labels :=
      (by positivity : (0:ℝ) ≤ (1/2:ℝ)^C.card).trans hp
    have hm0 : 0 ≤ componentDensity true false n K M a u aug C labels :=
      (by positivity : (0:ℝ) ≤ (1/2:ℝ)^C.card).trans hm
    have hq : 0 < averageComponent n K M a u aug C labels :=
      lt_of_lt_of_le (by positivity)
        (component_denominator_bounds n K M a u hK ha hu aug C labels).2
    apply (div_le_iff₀ hq).2
    unfold oddDiscrepancy averageComponent
    nlinarith [mul_nonneg hp0 hm0]
  unfold componentOddActivity
  calc
    _ ≤ (4:ℝ)^(-(n:ℤ))*∑ labels, averageComponent n K M a u aug C labels :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun labels _ => hterm labels)) (by positivity)
    _ = 1 := by rw [averageComponent_sum]; simp [zpow_neg]

/-- A positive component denominator converts a pointwise discrepancy envelope into a squared activity bound. This statement assumes [the hB condition](hyp:hB), [the hD condition](hyp:hD), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finite_component_activity_bound
lemma finite_component_activity_bound (n m : ℕ) (D p : Labels n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hD : ∀ labels, |D labels| ≤ B)
    (hp : ∀ labels, (1/2:ℝ)^m ≤ p labels) :
    (4:ℝ)^(-(n:ℤ)) * ∑ labels, D labels^2/p labels ≤ B^2*2^m := by
  have hp0 (labels) : 0 < p labels := lt_of_lt_of_le (by positivity) (hp labels)
  have hpt (labels) : 1 ≤ p labels*2^m := by
    have hh := mul_le_mul_of_nonneg_right (hp labels) (by positivity : (0:ℝ) ≤ 2^m)
    have he : (1/2:ℝ)^m*2^m = 1 := by rw [← mul_pow]; norm_num
    rwa [he] at hh
  have hsq (labels) : D labels^2 ≤ B^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hD labels) 2
    simpa only [sq_abs] using hh
  have hterm (labels) : D labels^2/p labels ≤ B^2*2^m := by
    apply (div_le_iff₀ (hp0 labels)).2
    calc
      _ ≤ B^2 := hsq labels
      _ ≤ B^2*(p labels*2^m) := le_mul_of_one_le_right (sq_nonneg _) (hpt labels)
      _ = _ := by ring
  calc
    _ ≤ (4:ℝ)^(-(n:ℤ)) * ∑ _ : Labels n, B^2*2^m :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun labels _ => hterm labels)) (by positivity)
    _ = B^2*2^m := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, fair_label_cardinality, one_mul]

/-- The actual null denominator yields the roadmap's even-component activity envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: componentEvenActivity_bound
lemma componentEvenActivity_bound (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n))
    (hb : ∀ labels, |evenDiscrepancy n K M a u aug C labels| ≤
      128*a^2*u^2*(C.card:ℝ)^4*2^C.card) :
    componentEvenActivity n K M a u aug C ≤
      2^14*a^4*u^4*(C.card:ℝ)^8*8^C.card := by
  have h := finite_component_activity_bound n C.card
    (evenDiscrepancy n K M a u aug C) (nullComponent n K M a u aug C)
    (128*a^2*u^2*(C.card:ℝ)^4*2^C.card) (by positivity) hb
    (fun labels => (component_denominator_bounds n K M a u hK ha hu aug C labels).1)
  change _ ≤ _ at h
  unfold componentEvenActivity
  convert h using 1
  rw [show (8:ℝ)^C.card = ((2:ℝ)^C.card)^3 by rw [show (8:ℝ) = 2^3 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]]
  ring

/-- The actual intermediate denominator yields the roadmap's odd-component activity envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: componentOddActivity_bound
lemma componentOddActivity_bound (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n))
    (hb : ∀ labels, |oddDiscrepancy n K M a u aug C labels| ≤
      16*a*u*(C.card:ℝ)^2*2^C.card) :
    componentOddActivity n K M a u aug C ≤
      2^8*a^2*u^2*(C.card:ℝ)^4*8^C.card := by
  have hap := ha.1
  have hup := hu.1
  have h := finite_component_activity_bound n C.card
    (oddDiscrepancy n K M a u aug C) (averageComponent n K M a u aug C)
    (16*a*u*(C.card:ℝ)^2*2^C.card) (by positivity) hb
    (fun labels => (component_denominator_bounds n K M a u hK ha hu aug C labels).2)
  unfold componentOddActivity
  convert h using 1
  rw [show (8:ℝ)^C.card = ((2:ℝ)^C.card)^3 by rw [show (8:ℝ) = 2^3 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]]
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma

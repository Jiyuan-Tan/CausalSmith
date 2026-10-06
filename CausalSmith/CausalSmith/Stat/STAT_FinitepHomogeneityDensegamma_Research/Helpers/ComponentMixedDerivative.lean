module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentRationalDerivative

/-! Record mixed derivatives, exact component slopes, and bounds uniform over all occupancies. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The outcome slope of the full record density is independent of the outcome amplitude. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). -/
-- @node: labelOutcomeDerivative
def labelOutcomeDerivative (ν : Bool) (K M : ℕ) (a : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  if marked then
    signVal label.2 * frameField K (fun j => signVal (idx.2 j).2) x +
      signVal label.1 * signVal label.2 *
        (a * frameField K (fun j => signVal (idx.2 j).1) x *
          frameField K (fun j => signVal (idx.2 j).2) x -
          (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
            correctionFactor ((frameField K (fun j => signVal (idx.2 j).1) x)^2) a)
  else 0

/-- One differentiation in each amplitude retains the complete marked-label interaction. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). -/
-- @node: labelMixedDerivative
def labelMixedDerivative (ν : Bool) (K M : ℕ) (a : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  if marked then signVal label.1 * signVal label.2 *
    (frameField K (fun j => signVal (idx.2 j).1) x *
      frameField K (fun j => signVal (idx.2 j).2) x -
      (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
        correctionSlope ((frameField K (fun j => signVal (idx.2 j).1) x)^2) a)
  else 0

/-- Two propensity differentiations and one outcome differentiation retain the rational curvature. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). -/
-- @node: labelMixedCurvature
def labelMixedCurvature (ν : Bool) (K M : ℕ) (a : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  if marked then -signVal label.1 * signVal label.2 *
    (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
      correctionCurvature ((frameField K (fun j => signVal (idx.2 j).1) x)^2) a
  else 0

/-- Affinity in the outcome amplitude gives its derivative at every amplitude, with all labels retained. [This is the stated conclusion](goal). -/
-- @node: labelDensity_hasDerivAt_outcome
lemma labelDensity_hasDerivAt_outcome (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelDensity ν K M a b idx x marked label)
      (labelOutcomeDerivative ν K M a idx x marked label) u := by
  have hd := ((hasDerivAt_id u).mul_const
    (labelDensity ν K M a 1 idx x marked label - labelDensity ν K M a 0 idx x marked label)).const_add
      (labelDensity ν K M a 0 idx x marked label)
  convert hd using 1 <;> first
  | rfl
  | (funext b; exact labelDensity_affine_outcome ν K M a b idx x marked label)
  | (cases ν <;> cases marked <;> simp [labelOutcomeDerivative, labelDensity, copulaXi,
      copulaUpsilon, copulaZeta_correctionFactor] <;> ring)

/-- Differentiating the outcome slope in propensity gives the first mixed derivative. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: labelOutcomeDerivative_hasDerivAt
lemma labelOutcomeDerivative_hasDerivAt (ν : Bool) (K M : ℕ) (a : ℝ)
    (ha : 1-a^2 ≠ 0) (idx : CopulaIndex K M) (x : unitInterval)
    (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelOutcomeDerivative ν K M b idx x marked label)
      (labelMixedDerivative ν K M a idx x marked label) a := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  cases marked with
  | false => simpa [labelOutcomeDerivative, labelMixedDerivative] using hasDerivAt_const a (0:ℝ)
  | true =>
    have hd := (((((hasDerivAt_id a).mul_const Λ).mul_const H).sub
      ((correctionFactor_hasDerivAt (Λ^2) a ha).const_mul c)).const_mul
        (signVal label.1 * signVal label.2)).const_add (signVal label.2 * H)
    convert hd using 1 <;> first | rfl |
      (simp [labelOutcomeDerivative, labelMixedDerivative, Λ, H, c] <;> ring)

/-- Differentiating the first mixed derivative in propensity gives the mixed curvature. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: labelMixedDerivative_hasDerivAt
lemma labelMixedDerivative_hasDerivAt (ν : Bool) (K M : ℕ) (a : ℝ)
    (ha : 1-a^2 ≠ 0) (idx : CopulaIndex K M) (x : unitInterval)
    (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelMixedDerivative ν K M b idx x marked label)
      (labelMixedCurvature ν K M a idx x marked label) a := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  cases marked with
  | false => simpa [labelMixedDerivative, labelMixedCurvature] using hasDerivAt_const a (0:ℝ)
  | true =>
    have hd := ((hasDerivAt_const a (Λ*H)).sub
      ((correctionSlope_hasDerivAt (Λ^2) a ha).const_mul c)).const_mul
        (signVal label.1 * signVal label.2)
    convert hd using 1 <;> first | rfl |
      (cases ν <;> simp [labelMixedDerivative, labelMixedCurvature, Λ, H, c] <;> ring)

/-- Differentiating in the opposite order gives the same mixed slope. [This is the stated conclusion](goal). -/
-- @node: labelPropensityDerivative_hasDerivAt_outcome
lemma labelPropensityDerivative_hasDerivAt_outcome (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelPropensityDerivative ν K M a b idx x marked label)
      (labelMixedDerivative ν K M a idx x marked label) u := by
  cases marked with
  | false => simpa [labelPropensityDerivative, labelMixedDerivative] using
      hasDerivAt_const u (signVal label.1 * frameField K (fun j => signVal (idx.2 j).1) x)
  | true =>
    have hd := ((hasDerivAt_id u).const_mul
      (labelMixedDerivative ν K M a idx x true label)).const_add
        (signVal label.1 * frameField K (fun j => signVal (idx.2 j).1) x)
    convert hd using 1 <;> first
    | rfl
    | (funext b; cases ν <;> simp [labelPropensityDerivative, labelMixedDerivative] <;> ring)
    | simp

/-- The outcome derivative of propensity curvature equals the same mixed curvature. [This is the stated conclusion](goal). -/
-- @node: labelPropensityCurvature_hasDerivAt_outcome
lemma labelPropensityCurvature_hasDerivAt_outcome (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelPropensityCurvature ν K M a b idx x marked label)
      (labelMixedCurvature ν K M a idx x marked label) u := by
  cases marked with
  | false => simpa [labelPropensityCurvature, labelMixedCurvature] using hasDerivAt_const u (0:ℝ)
  | true =>
    convert (hasDerivAt_id u).mul_const (labelMixedCurvature ν K M a idx x true label) using 1 <;> first
    | rfl
    | (funext b; simp only [labelPropensityCurvature, labelMixedCurvature, if_true, id]; ring)
    | simp

/-- Every record derivative with two outcome differentiations vanishes, including both mixed orders. [This is the stated conclusion](goal). -/
-- @node: label_second_outcome_derivatives
lemma label_second_outcome_derivatives (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun _ : ℝ => labelOutcomeDerivative ν K M a idx x marked label) 0 u ∧
    HasDerivAt (fun _ : ℝ => labelMixedDerivative ν K M a idx x marked label) 0 u ∧
    HasDerivAt (fun _ : ℝ => labelMixedCurvature ν K M a idx x marked label) 0 u :=
  ⟨hasDerivAt_const _ _, hasDerivAt_const _ _, hasDerivAt_const _ _⟩

/-- Two signed frame fields have product at most two, using the square-root frame envelope. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: signed_frame_fields_product_bound
lemma signed_frame_fields_product_bound (K : ℕ) (hK : 0 < K)
    (p : CoefficientPairs K) (x : unitInterval) :
    |frameField K (fun j => signVal (p j).1) x *
      frameField K (fun j => signVal (p j).2) x| ≤ 2 := by
  have hs (b : Bool) : |signVal b| ≤ 1 := by cases b <;> norm_num [signVal]
  have hΛ := frameField_abs_le_sqrt_two K hK (fun j => signVal (p j).1) (fun _ => hs _) x
  have hH := frameField_abs_le_sqrt_two K hK (fun j => signVal (p j).2) (fun _ => hs _) x
  rw [abs_mul]
  calc
    _ ≤ Real.sqrt 2 * Real.sqrt 2 := mul_le_mul hΛ hH (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 := Real.mul_self_sqrt (by norm_num)

/-- The rational factor itself is bounded by one fifteenth on the amplitude rectangle. This statement assumes [the ht condition](hyp:ht), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correctionFactor_bound
lemma correctionFactor_bound (t a : ℝ) (ht : 0 ≤ t ∧ t ≤ 2)
    (ha : 0 ≤ a ∧ a ≤ 1/16) : |correctionFactor t a| ≤ 1/15 := by
  have hd := correction_denominator_bounds a ha
  have hpos : 0 < 1-a^2 := by linarith [hd.2.2.1]
  have hnum : 0 ≤ 1-a^2*t := by
    have hh := mul_le_mul_of_nonneg_left ht.2 hd.1
    nlinarith [hd.2.1]
  have hnum' : 1-a^2*t ≤ 1 := by nlinarith [mul_nonneg hd.1 ht.1]
  unfold correctionFactor
  rw [abs_div, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hnum, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have hh := mul_le_mul_of_nonneg_left hnum' ha.1
  nlinarith [hd.2.2.1]

/-- All nonzero mixed record derivatives satisfy the roadmap's bound of four uniformly over every record category, fixed coefficient index and covariate. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: label_mixed_derivative_bounds
lemma label_mixed_derivative_bounds (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1/16) (idx : CopulaIndex K M)
    (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    |labelOutcomeDerivative ν K M a idx x marked label| ≤ 4 ∧
    |labelMixedDerivative ν K M a idx x marked label| ≤ 4 ∧
    |labelMixedCurvature ν K M a idx x marked label| ≤ 4 := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  have hs (b : Bool) : |signVal b| = 1 := by cases b <;> norm_num [signVal]
  have hH : |H| ≤ 2 := frameField_abs_le_two K hK _ (fun _ => (hs _).le) x
  have hprod : |Λ*H| ≤ 2 := signed_frame_fields_product_bound K hK idx.2 x
  have hc : |c| ≤ 1/16 := by
    have hg := smoothedTent_abs_le_one K M hK idx.1 x
    cases ν <;> simp only [c, Bool.false_eq_true, ↓reduceIte, zero_mul, abs_zero,
      one_mul, kappa0, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/16)]
    · norm_num
    · nlinarith
  have hf := frameField_abs_le_sqrt_two K hK (fun j => signVal (idx.2 j).1)
    (fun _ => (hs _).le) x
  have ht : Λ^2 ≤ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hf
    rw [← sq, sq_abs] at hh
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hr := frame_correction_derivative_bounds K M hK a ha idx x
  have hfactor : |correctionFactor (Λ^2) a| ≤ 1/15 :=
    correctionFactor_bound _ a ⟨sq_nonneg _, ht⟩ ha
  have hmix : |Λ*H-c*correctionSlope (Λ^2) a| ≤ 17/8 := by
    calc
      _ ≤ |Λ*H| + |c| * |correctionSlope (Λ^2) a| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using abs_add_le (Λ*H) (-(c*correctionSlope (Λ^2) a))
      _ ≤ 2 + (1/16)*2 := by gcongr <;> first | assumption | exact hr.1
      _ = 17/8 := by norm_num
  have hbase : |a*Λ*H-c*correctionFactor (Λ^2) a| ≤ 31/240 := by
    calc
      _ ≤ a*|Λ*H| + |c| *|correctionFactor (Λ^2) a| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg ha.1, mul_assoc] using
          abs_add_le (a*(Λ*H)) (-(c*correctionFactor (Λ^2) a))
      _ ≤ (1/16)*2 + (1/16)*(1/15) := by gcongr <;> first | assumption | exact ha.2
      _ = 31/240 := by norm_num
  cases marked with
  | false => simp [labelOutcomeDerivative, labelMixedDerivative, labelMixedCurvature]
  | true =>
    constructor
    · change |signVal label.2 * H + signVal label.1 * signVal label.2 *
        (a*Λ*H-c*correctionFactor (Λ^2) a)| ≤ 4
      calc
        _ ≤ |signVal label.2*H| + |signVal label.1*signVal label.2*
            (a*Λ*H-c*correctionFactor (Λ^2) a)| := abs_add_le _ _
        _ = |H| + |a*Λ*H-c*correctionFactor (Λ^2) a| := by simp only [abs_mul, hs, one_mul]
        _ ≤ 2 + 31/240 := add_le_add hH hbase
        _ ≤ 4 := by norm_num
    constructor
    · change |signVal label.1*signVal label.2*(Λ*H-c*correctionSlope (Λ^2) a)| ≤ 4
      simp only [abs_mul, hs, one_mul]
      exact hmix.trans (by norm_num)
    · have he : labelMixedCurvature ν K M a idx x true label =
          -signVal label.1*signVal label.2*c*correctionCurvature (Λ^2) a := by
        simp only [labelMixedCurvature, if_true, c, Λ]
        ring
      rw [he]
      simp only [abs_mul, abs_neg, hs, one_mul]
      calc
        |c| * |correctionCurvature (Λ^2) a| ≤ (1/16)*1 :=
          mul_le_mul hc hr.2 (abs_nonneg _) (by norm_num)
        _ ≤ 4 := by norm_num


/-- Differentiating a product selects one record propensity slope and retains every other label. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: componentPropensityDerivative
def componentPropensityDerivative (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ i ∈ C, (∏ j ∈ C.erase i,
      labelDensity ν K M a u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
        labelPropensityDerivative ν K M a u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)

/-- The outcome slope averages the single-record outcome derivatives against the unchanged prior. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: componentOutcomeDerivative
def componentOutcomeDerivative (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ i ∈ C, (∏ j ∈ C.erase i,
      labelDensity ν K M a u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
        labelOutcomeDerivative ν K M a ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)

/-- Finite product and sum differentiation gives the component propensity derivative at every non-pole amplitude. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: componentDensity_hasDerivAt_propensity
lemma componentDensity_hasDerivAt_propensity (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentDensity ν s n K M b u aug C labels)
      (componentPropensityDerivative ν s n K M a u aug C labels) a := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact HasDerivAt.fun_finsetProd (fun i _ =>
    labelDensity_hasDerivAt_propensity ν K M a u ha _ _ _ _)

/-- The outcome derivative holds at every amplitude, including zero, because each record is affine. [This is the stated conclusion](goal). -/
-- @node: componentDensity_hasDerivAt_outcome
lemma componentDensity_hasDerivAt_outcome (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentDensity ν s n K M a b aug C labels)
      (componentOutcomeDerivative ν s n K M a u aug C labels) u := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact HasDerivAt.fun_finsetProd (fun i _ =>
    labelDensity_hasDerivAt_outcome ν K M a u _ _ _ _)

/-- A first differentiated product has at most one term per record; each slope is bounded by four and all undifferentiated factors are bounded by two. This statement assumes [the hf condition](hyp:hf), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: record_product_slope_bound
lemma record_product_slope_bound {ι : Type*} [DecidableEq ι] (C : Finset ι)
    (f d : ι → ℝ) (hf : ∀ i ∈ C, |f i| ≤ 2) (hd : ∀ i ∈ C, |d i| ≤ 4) :
    |∑ i ∈ C, (∏ j ∈ C.erase i, f j) * d i| ≤ 4*(C.card:ℝ)*2^C.card := by
  have hp (i : ι) : |∏ j ∈ C.erase i, f j| ≤ (2:ℝ)^C.card := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j ∈ C.erase i, (2:ℝ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        (fun j hj => hf j (Finset.mem_of_mem_erase hj))
      _ = (2:ℝ)^(C.erase i).card := by simp
      _ ≤ (2:ℝ)^C.card := by
        exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.erase_subset _ _))
  calc
    _ ≤ ∑ i ∈ C, |(∏ j ∈ C.erase i, f j) * d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ C, (2:ℝ)^C.card*4 := Finset.sum_le_sum (fun i hi => by
      rw [abs_mul]
      exact mul_le_mul (hp i) (hd i hi) (abs_nonneg _) (by positivity))
    _ = 4*(C.card:ℝ)*2^C.card := by simp; ring

/-- Averaging a uniformly bounded quantity against the actual normalized conditional prior preserves the bound, even when arbitrary boundary coefficients have been disclosed. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_abs_average_bound
lemma conditionalPairWeight_abs_average_bound (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (f : CoefficientPairs K → ℝ) (B : ℝ)
    (hf : ∀ p, |f p| ≤ B) :
    |∑ p, conditionalPairWeight ν K M σ δ p * f p| ≤ B := by
  calc
    _ ≤ ∑ p, |conditionalPairWeight ν K M σ δ p * f p| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p, conditionalPairWeight ν K M σ δ p * |f p| := by
      apply Finset.sum_congr rfl
      intro p _
      rw [abs_mul, abs_of_nonneg (conditionalPairWeight_nonneg _ _ _ _ _ _)]
    _ ≤ ∑ p, conditionalPairWeight ν K M σ δ p * B :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hf p)
        (conditionalPairWeight_nonneg _ _ _ _ _ _))
    _ = B := by rw [← Finset.sum_mul, conditionalPairWeight_sum, one_mul]

/-- Both component slopes obey the first-order all-occupancy envelope from the roadmap. No independence between positions or zero transition tensor is used. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_first_derivative_bounds
lemma component_first_derivative_bounds (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |componentPropensityDerivative ν s n K M a u aug C labels| ≤ 4*(C.card:ℝ)*2^C.card ∧
    |componentOutcomeDerivative ν s n K M a u aug C labels| ≤ 4*(C.card:ℝ)*2^C.card := by
  have hb (p : CoefficientPairs K) (i : Fin n) :
      |labelDensity ν K M a u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)| ≤ 2 := by
    have hh := labelDensity_bounds ν K M a u hK ha hu ((fun _ => s),p)
      (aug.1 i) (aug.2.1 i) (labels i)
    rw [abs_of_nonneg (by linarith [hh.1])]
    exact hh.2
  constructor
  · apply conditionalPairWeight_abs_average_bound
    intro p
    apply record_product_slope_bound
    · intro i _; exact hb p i
    · intro i _
      exact (label_propensity_derivative_bounds ν K M hK a u ⟨ha.1.le, ha.2⟩ ⟨hu.1.le, hu.2⟩
        ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).1
  · apply conditionalPairWeight_abs_average_bound
    intro p
    apply record_product_slope_bound
    · intro i _; exact hb p i
    · intro i _
      exact (label_mixed_derivative_bounds ν K M hK a ⟨ha.1.le, ha.2⟩
        ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).1

end CausalSmith.Stat.FinitepHomogeneityDensegamma

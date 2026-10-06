module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentMixedDerivative
public import Mathlib.Analysis.Calculus.MeanValue

/-! Mixed component slopes and the first-order rectangular remainder for odd discrepancies. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open scoped BigOperators
open Set
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The mixed slope assigns the two labeled differentiations to distinct records or to one record, retaining the actual coefficient prior in both cases. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
-- @node: componentMixedDerivative
def componentMixedDerivative (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ i ∈ C,
      ((∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j,
          labelDensity ν K M a u ((fun _ => s),p) (aug.1 k) (aug.2.1 k) (labels k)) *
            labelOutcomeDerivative ν K M a ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
          labelPropensityDerivative ν K M a u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i) +
        (∏ j ∈ C.erase i,
          labelDensity ν K M a u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
            labelMixedDerivative ν K M a ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i))

/-- Differentiating the exact propensity slope in the outcome amplitude gives the mixed slope. [This is the stated conclusion](goal). -/
-- @node: componentPropensityDerivative_hasDerivAt_outcome
lemma componentPropensityDerivative_hasDerivAt_outcome (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentPropensityDerivative ν s n K M a b aug C labels)
      (componentMixedDerivative ν s n K M a u aug C labels) u := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (HasDerivAt.fun_finsetProd (fun j _ =>
    labelDensity_hasDerivAt_outcome ν K M a u _ _ _ _)).mul
      (labelPropensityDerivative_hasDerivAt_outcome ν K M a u _ _ _ _)

/-- The twice differentiated product has at most the square of its record count terms, with coincident assignments bounded by the same enlarged envelope. This statement assumes [the hf condition](hyp:hf), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hau condition](hyp:hau). [This is the stated conclusion](goal). -/
-- @node: record_product_mixed_slope_bound
lemma record_product_mixed_slope_bound {ι : Type*} [DecidableEq ι] (C : Finset ι)
    (f da du dau : ι → ℝ) (hf : ∀ i ∈ C, |f i| ≤ 2)
    (ha : ∀ i ∈ C, |da i| ≤ 4) (hu : ∀ i ∈ C, |du i| ≤ 4)
    (hau : ∀ i ∈ C, |dau i| ≤ 4) :
    |∑ i ∈ C, ((∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j, f k) * du j) * da i +
      (∏ j ∈ C.erase i, f j) * dau i)| ≤ 16*(C.card:ℝ)^2*2^C.card := by
  have hp (i : ι) : |∏ j ∈ C.erase i, f j| ≤ (2:ℝ)^C.card := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j ∈ C.erase i, (2:ℝ) := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun j hj => hf j (Finset.mem_of_mem_erase hj))
      _ = (2:ℝ)^(C.erase i).card := by simp
      _ ≤ (2:ℝ)^C.card := pow_le_pow_right₀ (by norm_num)
        (Finset.card_le_card (Finset.erase_subset _ _))
  have ht (i : ι) (hi : i ∈ C) :
      |(∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j, f k) * du j) * da i +
        (∏ j ∈ C.erase i, f j) * dau i| ≤ 16*(C.card:ℝ)*2^C.card := by
    have hs := record_product_slope_bound (C.erase i) f du
      (fun j hj => hf j (Finset.mem_of_mem_erase hj))
      (fun j hj => hu j (Finset.mem_of_mem_erase hj))
    have he : ((C.erase i).card:ℝ) = (C.card:ℝ)-1 := by
      rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.card_pos.mpr ⟨i, hi⟩)]
      simp
    have hn : 1 ≤ (C.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    have hs' : |∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j, f k) * du j| ≤
        4*((C.card:ℝ)-1)*2^C.card := by
      apply hs.trans
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num)
          (Finset.card_le_card (Finset.erase_subset _ _))) (by positivity)
    calc
      _ ≤ |(∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j, f k) * du j) * da i| +
        |(∏ j ∈ C.erase i, f j) * dau i| := abs_add_le _ _
      _ ≤ (4*((C.card:ℝ)-1)*2^C.card)*4 + 2^C.card*4 := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hs' (ha i hi) (abs_nonneg _) (by positivity))
          (mul_le_mul (hp i) (hau i hi) (abs_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith [show (0:ℝ) ≤ 2^C.card by positivity]
  calc
    _ ≤ ∑ i ∈ C, |((∑ j ∈ C.erase i, (∏ k ∈ (C.erase i).erase j, f k) * du j) * da i +
      (∏ j ∈ C.erase i, f j) * dau i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ C, 16*(C.card:ℝ)*2^C.card := Finset.sum_le_sum ht
    _ = _ := by simp; ring

/-- The record envelope also holds on the axes of the integration rectangle. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: labelDensity_abs_le_two_closed
lemma labelDensity_abs_le_two_closed (ν : Bool) (K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    |labelDensity ν K M a u idx x marked label| ≤ 2 := by
  have hs (b : Bool) : |signVal b| = 1 := by cases b <;> norm_num [signVal]
  have hb (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1/16) (field : ℝ) (hf : |field| ≤ 2)
      (b : Bool) : |1 + signVal b * (t * field)| ≤ 2 := by
    calc
      _ ≤ |(1:ℝ)| + |signVal b * (t * field)| := abs_add_le _ _
      _ = 1 + t * |field| := by simp [abs_mul, hs, abs_of_nonneg ht.1]
      _ ≤ 1 + (1/16)*2 := by gcongr <;> first | exact ht.2 | exact hf
      _ ≤ 2 := by norm_num
  by_cases ha0 : a = 0
  · subst a
    cases marked
    · simp [labelDensity, copulaXi]
    · simpa [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT] using
        hb u hu _ (frameField_abs_le_two K hK _ (fun _ => (hs _).le) x) label.2
  by_cases hu0 : u = 0
  · subst u
    cases marked <;> simpa [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT] using
      hb a ha _ (frameField_abs_le_two K hK _ (fun _ => (hs _).le) x) label.1
  have hh := labelDensity_bounds ν K M a u hK ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), ha.2⟩
    ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩ idx x marked label
  rw [abs_of_nonneg (by linarith [hh.1])]
  exact hh.2

/-- The actual conditional coefficient average preserves the mixed all-occupancy envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_mixed_derivative_bound
lemma component_mixed_derivative_bound (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |componentMixedDerivative ν s n K M a u aug C labels| ≤ 16*(C.card:ℝ)^2*2^C.card := by
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
    exact (label_mixed_derivative_bounds ν K M hK a ha
      ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).1
  · intro i _
    exact (label_mixed_derivative_bounds ν K M hK a ha
      ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)).2.1

/-- The odd discrepancy uses the exact axis cancellations and two first-order remainders. This estimate includes every mixed transition tensor and every occupancy. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: oddDiscrepancy_rectangular_bound
lemma oddDiscrepancy_rectangular_bound (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |oddDiscrepancy n K M a u aug C labels| ≤ 16*a*u*(C.card:ℝ)^2*2^C.card := by
  let F := fun b v => oddDiscrepancy n K M b v aug C labels
  let S := fun b v => (componentPropensityDerivative true true n K M b v aug C labels -
    componentPropensityDerivative true false n K M b v aug C labels)/2
  let T := fun b v => (componentMixedDerivative true true n K M b v aug C labels -
    componentMixedDerivative true false n K M b v aug C labels)/2
  let B : ℝ := 16*(C.card:ℝ)^2*2^C.card
  have hp (b : ℝ) (hb : b ∈ Icc 0 a) : 1-b^2 ≠ 0 := by
    have hh := correction_denominator_bounds b ⟨hb.1, hb.2.trans ha.2⟩
    linarith [hh.2.2.1]
  have hF (b v : ℝ) (hb : b ∈ Icc 0 a) : HasDerivAt (fun t => F t v) (S b v) b :=
    ((componentDensity_hasDerivAt_propensity true true n K M b v (hp b hb) aug C labels).sub
      (componentDensity_hasDerivAt_propensity true false n K M b v (hp b hb) aug C labels)).div_const 2
  have hS (b v : ℝ) : HasDerivAt (fun t => S b t) (T b v) v :=
    ((componentPropensityDerivative_hasDerivAt_outcome true true n K M b v aug C labels).sub
      (componentPropensityDerivative_hasDerivAt_outcome true false n K M b v aug C labels)).div_const 2
  have hT (b v : ℝ) (hb : b ∈ Icc 0 a) (hv : v ∈ Icc 0 u) : |T b v| ≤ B := by
    have hplus := component_mixed_derivative_bound true true n K M b v hK
      ⟨hb.1, hb.2.trans ha.2⟩ ⟨hv.1, hv.2.trans hu.2⟩ aug C labels
    have hminus := component_mixed_derivative_bound true false n K M b v hK
      ⟨hb.1, hb.2.trans ha.2⟩ ⟨hv.1, hv.2.trans hu.2⟩ aug C labels
    dsimp [T, B] at *
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    have hh : |componentMixedDerivative true true n K M b v aug C labels -
        componentMixedDerivative true false n K M b v aug C labels| ≤
        |componentMixedDerivative true true n K M b v aug C labels| +
        |componentMixedDerivative true false n K M b v aug C labels| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (componentMixedDerivative true true n K M b v aug C labels)
        (-componentMixedDerivative true false n K M b v aug C labels)
    linarith
  have hSzero (b : ℝ) (hb : b ∈ Icc 0 a) : S b 0 = 0 := by
    have he : (fun t => F t 0) = fun _ => 0 := by
      funext t
      exact (component_discrepancies_on_axes n K M t 0 aug C labels).2.1
    have hd := hF b 0 hb
    rw [he] at hd
    exact hd.unique (hasDerivAt_const b (0:ℝ))
  have hSbound (b : ℝ) (hb : b ∈ Icc 0 a) : |S b u| ≤ B*u := by
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v (_ : v ∈ Icc 0 u) => (hS b v).hasDerivWithinAt)
      (fun v hv => by simpa only [Real.norm_eq_abs] using hT b v hb hv)
      (convex_Icc 0 u) (left_mem_Icc.mpr hu.1) (right_mem_Icc.mpr hu.1)
    simpa only [Real.norm_eq_abs, hSzero b hb, sub_zero, abs_of_nonneg hu.1] using hm
  have hFzero : F 0 u = 0 :=
    (component_discrepancies_on_axes n K M 0 u aug C labels).2.2.2
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun b hb => (hF b u hb).hasDerivWithinAt)
    (fun b hb => by simpa only [Real.norm_eq_abs] using hSbound b hb)
    (convex_Icc 0 a) (left_mem_Icc.mpr ha.1) (right_mem_Icc.mpr ha.1)
  have hbnd : |F a u| ≤ (B*u)*a := by
    simpa only [Real.norm_eq_abs, hFzero, sub_zero, abs_of_nonneg ha.1] using hm
  calc
    _ ≤ (B*u)*a := hbnd
    _ = _ := by dsimp [B]; ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma

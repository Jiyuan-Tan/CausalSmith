module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentJointNormalization

/-! Exact component overlaps and the diagonal-free shared-sign exponential bound. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A fixed-sign component density is its sign average plus the signed odd discrepancy. [This is the stated conclusion](goal). -/
-- @node: componentDensity_eq_average_add_odd
lemma componentDensity_eq_average_add_odd (s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentDensity true s n K M a u aug C labels =
      averageComponent n K M a u aug C labels +
        signVal s * oddDiscrepancy n K M a u aug C labels := by
  cases s <;> simp only [averageComponent, oddDiscrepancy, signVal,
    Bool.false_eq_true, ↓reduceIte] <;> ring

/-- Centered finite densities have an exact overlap consisting of unit mass and their squared odd activity; the linear terms cancel before averaging any coarse sign. This statement assumes [the hq condition](hyp:hq), [the hmass condition](hyp:hmass), [the hd condition](hyp:hd), [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: finite_centered_density_overlap
lemma finite_centered_density_overlap {ι : Type*} [Fintype ι]
    (q d : ι → ℝ) (w mass s t : ℝ) (hq : ∀ i, q i ≠ 0)
    (hmass : ∑ i, q i = mass) (hd : ∑ i, d i = 0) (hw : w * mass = 1) :
    w * ∑ i, (q i + s*d i)*(q i + t*d i)/q i =
      1 + s*t*(w * ∑ i, d i^2/q i) := by
  have he (i : ι) : (q i + s*d i)*(q i + t*d i)/q i =
      q i + (s+t)*d i + s*t*(d i^2/q i) := by
    field_simp [hq i]
    <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hmass, hd]
  linear_combination hw

/-- The actual full-label component overlap is one plus the product of the two coarse signs times the odd activity, with the positive intermediate density as denominator. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_signed_overlap
lemma component_signed_overlap (s t : Bool) (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    (4:ℝ)^(-(n:ℤ)) * ∑ labels : Labels n,
      componentDensity true s n K M a u aug C labels *
        componentDensity true t n K M a u aug C labels /
          averageComponent n K M a u aug C labels =
      1 + signVal s * signVal t * componentOddActivity n K M a u aug C := by
  simp_rw [componentDensity_eq_average_add_odd]
  apply finite_centered_density_overlap
  · intro labels
    exact ne_of_gt (lt_of_lt_of_le (by positivity)
      (component_denominator_bounds n K M a u hK ha hu aug C labels).2)
  · exact averageComponent_sum n K M a u aug C
  · exact oddDiscrepancy_sum_zero n K M a u aug C
  · simp [zpow_neg]

/-- Inserting a component into the ordered distinct-pair budget adds exactly its products with old components; its diagonal square never enters. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: distinct_pair_budget_insert
lemma distinct_pair_budget_insert {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι) (hx : x ∉ S) (d : ι → ℝ) :
    (∑ i ∈ insert x S, ∑ j ∈ insert x S, if i ≠ j then d i*d j else 0)/2 =
      (∑ i ∈ S, ∑ j ∈ S, if i ≠ j then d i*d j else 0)/2 +
        d x * ∑ i ∈ S, d i := by
  rw [Finset.sum_insert hx]
  simp only [Finset.sum_insert hx, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
  have hxj : ∀ j ∈ S, x ≠ j := fun j hj h => hx (h ▸ hj)
  have hjx : ∀ j ∈ S, j ≠ x := fun j hj h => hx (h ▸ hj)
  simp_rw [Finset.sum_add_distrib]
  have h1 : (∑ j ∈ S, if x ≠ j then d x*d j else 0) = d x * ∑ j ∈ S, d j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => if_pos (hxj j hj))
  have h2 : (∑ i ∈ S, if i ≠ x then d i*d x else 0) = d x * ∑ i ∈ S, d i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [if_pos (hjx i hi), mul_comm])
  rw [h1, h2]
  ring

/-- The even and odd parts of a finite product are nonnegative. The odd part is bounded by the sum of component activities times the even part, providing the induction invariant for pairing. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: shared_sign_product_invariants
lemma shared_sign_product_invariants {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ S, 0 ≤ d i) :
    0 ≤ ((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2 ∧
    0 ≤ ((∏ i ∈ S, (1+d i)) - ∏ i ∈ S, (1-d i))/2 ∧
    ((∏ i ∈ S, (1+d i)) - ∏ i ∈ S, (1-d i))/2 ≤
      (∑ i ∈ S, d i) * (((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have hdx := hd x (Finset.mem_insert_self _ _)
    have hh := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hsum : 0 ≤ ∑ i ∈ S, d i := Finset.sum_nonneg (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx]
    constructor
    · nlinarith [mul_nonneg hdx hh.2.1]
    constructor
    · nlinarith [mul_nonneg hdx hh.1]
    · have hmul := mul_nonneg (add_nonneg hdx hsum) (mul_nonneg hdx hh.2.1)
      nlinarith [hh.2.2]

/-- Averaging a shared fair sign bounds the even-subset product by the exponential of the sum over distinct pairs. Unlike a squared-sum bound, no diagonal activity is charged. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: shared_sign_product_le_exp_distinct_pairs
lemma shared_sign_product_le_exp_distinct_pairs {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ S, 0 ≤ d i) :
    ((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2 ≤
      Real.exp ((∑ i ∈ S, ∑ j ∈ S, if i ≠ j then d i*d j else 0)/2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have hdS := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hdx := hd x (Finset.mem_insert_self _ _)
    have hinv := shared_sign_product_invariants S d hdS
    have hsum : 0 ≤ ∑ i ∈ S, d i := Finset.sum_nonneg hdS
    have he :
        ((∏ i ∈ insert x S, (1+d i)) + ∏ i ∈ insert x S, (1-d i))/2 =
        (((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2) +
          d x * (((∏ i ∈ S, (1+d i)) - ∏ i ∈ S, (1-d i))/2) := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    rw [he, distinct_pair_budget_insert S x hx d, Real.exp_add]
    calc
      _ ≤ (((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2) *
          (1 + d x * ∑ i ∈ S, d i) := by
        nlinarith [mul_le_mul_of_nonneg_left hinv.2.2 hdx]
      _ ≤ Real.exp ((∑ i ∈ S, ∑ j ∈ S, if i ≠ j then d i*d j else 0)/2) *
          Real.exp (d x * ∑ i ∈ S, d i) :=
        mul_le_mul (ih hdS) (by linarith [Real.add_one_le_exp (d x * ∑ i ∈ S, d i)])
          (by positivity) (Real.exp_pos _).le

/-- Summing the pair budgets of coarse-sign groups counts precisely distinct components in one group, and counts no cross-group or diagonal products. [This is the stated conclusion](goal). -/
-- @node: grouped_distinct_pair_budget
lemma grouped_distinct_pair_budget {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (d : ι → ℝ) :
    (∑ k ∈ S.image g, (∑ i ∈ S.filter (fun i => g i = k),
      ∑ j ∈ S.filter (fun j => g j = k), if i ≠ j then d i*d j else 0)/2) =
      (∑ i ∈ S, ∑ j ∈ S, if i ≠ j ∧ g i = g j then d i*d j else 0)/2 := by
  rw [← Finset.sum_div]
  congr 1
  trans ∑ k ∈ S.image g, ∑ i ∈ S.filter (fun i => g i = k),
    ∑ j ∈ S.filter (fun j => g j = g i), if i ≠ j then d i*d j else 0
  · apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i = j <;> by_cases h' : g i = g j <;> simp [h, h', eq_comm]

/-- Independent coarse-sign groups obey the exact diagonal-free global pair budget. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: grouped_shared_sign_product_le_exp
lemma grouped_shared_sign_product_le_exp {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (d : ι → ℝ) (hd : ∀ i ∈ S, 0 ≤ d i) :
    (∏ k ∈ S.image g,
      ((∏ i ∈ S.filter (fun i => g i = k), (1+d i)) +
        ∏ i ∈ S.filter (fun i => g i = k), (1-d i))/2) ≤
      Real.exp ((∑ i ∈ S, ∑ j ∈ S, if i ≠ j ∧ g i = g j then d i*d j else 0)/2) := by
  rw [← grouped_distinct_pair_budget S g d, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro k hk
    exact (shared_sign_product_invariants _ d
      (fun i hi => hd i (Finset.mem_filter.mp hi).1)).1
  · intro k hk
    exact shared_sign_product_le_exp_distinct_pairs _ d
      (fun i hi => hd i (Finset.mem_filter.mp hi).1)

/-- The intermediate-versus-null component overlap has unit mass plus the even activity, using cancellation against the actual null denominator. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_even_overlap
lemma component_even_overlap (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    (4:ℝ)^(-(n:ℤ)) * ∑ labels : Labels n,
      averageComponent n K M a u aug C labels^2 / nullComponent n K M a u aug C labels =
        1 + componentEvenActivity n K M a u aug C := by
  have hh := finite_centered_density_overlap
    (nullComponent n K M a u aug C) (evenDiscrepancy n K M a u aug C)
    ((4:ℝ)^(-(n:ℤ))) ((4:ℝ)^n) 1 1
    (fun labels => ne_of_gt (lt_of_lt_of_le (by positivity)
      (component_denominator_bounds n K M a u hK ha hu aug C labels).1))
    (nullComponent_sum n K M a u aug C) (evenDiscrepancy_sum_zero n K M a u aug C)
    (by simp [zpow_neg])
  simpa only [componentEvenActivity, one_mul, evenDiscrepancy, add_sub_cancel,
    ← pow_two, one_pow] using hh

/-- The two independent copies of a shared fair coarse sign select exactly the even part of the component product, retaining all distinct-component odd interactions. [This is the stated conclusion](goal). -/
-- @node: shared_sign_overlap_average
lemma shared_sign_overlap_average {ι : Type*} (S : Finset ι) (d : ι → ℝ) :
    (∑ s : Bool, ∑ t : Bool, ∏ i ∈ S, (1 + signVal s * signVal t * d i))/4 =
      ((∏ i ∈ S, (1+d i)) + ∏ i ∈ S, (1-d i))/2 := by
  simp [signVal, sub_eq_add_neg]
  ring

/-- Nonnegative even activities exponentiate their sum without changing the exact product. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: component_product_le_exp_sum
lemma component_product_le_exp_sum {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ S, 0 ≤ d i) :
    (∏ i ∈ S, (1+d i)) ≤ Real.exp (∑ i ∈ S, d i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [hd i hi]
  · intro i hi
    linarith [Real.add_one_le_exp (d i)]

end CausalSmith.Stat.FinitepHomogeneityDensegamma

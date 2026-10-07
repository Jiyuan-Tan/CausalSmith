module
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Real.Basic

/-!
# Product-difference telescopes

Bounds on the difference of two finite products of real numbers, ∏ᵢ aᵢ − ∏ᵢ bᵢ. When all factors
lie in [0, 1], the difference is at most ∑ᵢ |aᵢ − bᵢ| in absolute value. For general factors the
difference along a list is written exactly as a telescoping sum in which the i-th term is
(aᵢ − bᵢ) times the earlier a-factors and the later b-factors; for nonnegative factors its absolute
value is at most the same expression with |aᵢ − bᵢ| in place of aᵢ − bᵢ, which gives a weighted
bound on the product gap over a finite index type.

## Main definitions

* `weightedProductTelescope` — the recursive telescoping expansion of a list-product difference.
* `weightedProductTelescopeAbs` — the same expansion with each difference replaced by its absolute
  value.

## Main results

* `abs_prod_sub_prod_le_sum_abs` — for factors in [0, 1], |∏ aᵢ − ∏ bᵢ| ≤ ∑ |aᵢ − bᵢ|.
* `list_prod_sub_prod_eq_weightedProductTelescope` — the product difference equals its telescope.
* `abs_weightedProductTelescope_le` — for nonnegative factors the telescope is bounded by its
  absolute-value envelope.
* `abs_fintype_prod_sub_prod_le_weighted` — for nonnegative factors on a finite type, the product
  gap is bounded by the envelope along the list of all indices.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Algebra.BigOperators.Ring

/-- For [a finite set of coordinates](hyp:s) and [two families of factors](hyp:a,b)
that [both lie in the unit interval](hyp:ha,hb), the absolute difference of
their products is bounded by the sum of coordinatewise absolute differences. The result is [the unit-interval product Lipschitz bound](goal). -/
lemma abs_prod_sub_prod_le_sum_abs {I : Type*}
    (s : Finset I) (a b : I → ℝ)
    (ha : ∀ i ∈ s, a i ∈ Set.Icc 0 1)
    (hb : ∀ i ∈ s, b i ∈ Set.Icc 0 1) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai := ha i (Finset.mem_insert_self i s)
      have hbi := hb i (Finset.mem_insert_self i s)
      have haS (j : I) (hj : j ∈ s) : a j ∈ Set.Icc (0 : ℝ) 1 :=
        ha j (Finset.mem_insert_of_mem hj)
      have hbS (j : I) (hj : j ∈ s) : b j ∈ Set.Icc (0 : ℝ) 1 :=
        hb j (Finset.mem_insert_of_mem hj)
      have hrec := ih haS hbS
      have hpa0 : 0 ≤ ∏ j ∈ s, a j :=
        Finset.prod_nonneg fun j hj => (haS j hj).1
      have hpb0 : 0 ≤ ∏ j ∈ s, b j :=
        Finset.prod_nonneg fun j hj => (hbS j hj).1
      have hpb1 : (∏ j ∈ s, b j) ≤ 1 :=
        Finset.prod_le_one (fun j hj => (hbS j hj).1)
          (fun j hj => (hbS j hj).2)
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by ring_nf
        _ ≤ |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)| +
            |(a i - b i) * ∏ j ∈ s, b j| := abs_add_le _ _
        _ = a i * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
            |a i - b i| * ∏ j ∈ s, b j := by
          rw [abs_mul, abs_mul, abs_of_nonneg hai.1, abs_of_nonneg hpb0]
        _ ≤ |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| + |a i - b i| := by
          apply add_le_add
          · simpa using mul_le_mul_of_nonneg_right hai.2
              (abs_nonneg ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
          · simpa using mul_le_mul_of_nonneg_left hpb1 (abs_nonneg (a i - b i))
        _ ≤ |a i - b i| + ∑ j ∈ s, |a j - b j| := by linarith


/-- Given [two real-valued coordinate families a and b](hyp:a,b) and a list of coordinates,
[the weighted product telescope](goal) is the sum, over positions in the list, of the product of
the a-values at the earlier positions, times the difference a − b at that position, times the
product of the b-values at the later positions. It is defined by recursion on the list and is
zero for the empty list. -/
noncomputable def weightedProductTelescope {I : Type*} (a b : I → ℝ) :
    List I → ℝ
  | [] => 0
  | i :: l => (a i - b i) * (l.map b).prod +
      a i * weightedProductTelescope a b l


/-- For [two real-valued coordinate families](hyp:a,b) and a [coordinate
list](hyp:l), their list-product difference equals the recursive weighted
product telescope. The result is [the equality between the list-product difference and its weighted telescope](goal). -/
lemma list_prod_sub_prod_eq_weightedProductTelescope {I : Type*}
    (a b : I → ℝ) (l : List I) :
    (l.map a).prod - (l.map b).prod = weightedProductTelescope a b l := by
  induction l with
  | nil => simp [weightedProductTelescope]
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, weightedProductTelescope]
      rw [← ih]
      ring


/-- Given [two real-valued coordinate families a and b](hyp:a,b), recursively form the
envelope of their weighted product telescope along a [coordinate
list](goal), replacing each coordinate difference by its absolute value: the empty list gives
zero, and a list with head i and tail l gives |a(i) − b(i)| times the product of b over l plus
a(i) times the envelope of l. The result is [the recursive envelope of the weighted product telescope, which is nonnegative whenever both families are nonnegative](goal). -/
noncomputable def weightedProductTelescopeAbs {I : Type*} (a b : I → ℝ) :
    List I → ℝ
  | [] => 0
  | i :: l => |a i - b i| * (l.map b).prod +
      a i * weightedProductTelescopeAbs a b l


/-- For [two nonnegative coordinate families along a list](hyp:a,b,l,ha,hb), the
absolute value of the weighted product telescope is bounded by its recursive
nonnegative envelope. The result is [the absolute weighted-telescope bound by its nonnegative envelope](goal). -/
lemma abs_weightedProductTelescope_le {I : Type*} (a b : I → ℝ) (l : List I)
    (ha : ∀ i ∈ l, 0 ≤ a i) (hb : ∀ i ∈ l, 0 ≤ b i) :
    |weightedProductTelescope a b l| ≤
      weightedProductTelescopeAbs a b l := by
  induction l with
  | nil => simp [weightedProductTelescope, weightedProductTelescopeAbs]
  | cons i l ih =>
      have hai : 0 ≤ a i := ha i (by simp)
      have hbi : 0 ≤ b i := hb i (by simp)
      have haL (j : I) (hj : j ∈ l) : 0 ≤ a j := ha j (by simp [hj])
      have hbL (j : I) (hj : j ∈ l) : 0 ≤ b j := hb j (by simp [hj])
      have hprodB : 0 ≤ (l.map b).prod := by
        exact List.prod_nonneg (by simpa using hbL)
      have hrec := ih haL hbL
      simp only [weightedProductTelescope, weightedProductTelescopeAbs]
      calc
        |(a i - b i) * (l.map b).prod +
            a i * weightedProductTelescope a b l| ≤
          |(a i - b i) * (l.map b).prod| +
            |a i * weightedProductTelescope a b l| := abs_add_le _ _
        _ = |a i - b i| * (l.map b).prod +
            a i * |weightedProductTelescope a b l| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hprodB, abs_of_nonneg hai]
        _ ≤ |a i - b i| * (l.map b).prod +
            a i * weightedProductTelescopeAbs a b l := by
          gcongr
        _ = weightedProductTelescopeAbs a b (i :: l) := by rfl


/-- For [two nonnegative families on a finite coordinate type](hyp:I,a,b,ha,hb),
the absolute difference of their products is bounded by the weighted telescope
envelope along the canonical list of all coordinates. The result is [the finite-product gap bound by the canonical weighted telescope](goal). -/
lemma abs_fintype_prod_sub_prod_le_weighted {I : Type*} [Fintype I]
    (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    |(∏ i : I, a i) - ∏ i : I, b i| ≤
      weightedProductTelescopeAbs a b (Finset.univ.toList) := by
  classical
  have hprod (f : I → ℝ) :
      (Finset.univ.toList.map f).prod = ∏ i : I, f i := by
    rw [Finset.prod_list_map_count]
    simp only [Finset.toList_toFinset]
    apply Finset.prod_congr rfl
    intro i _
    rw [List.count_eq_one_of_mem (Finset.univ : Finset I).nodup_toList]
    · simp
    · exact Finset.mem_toList.mpr (Finset.mem_univ i)
  rw [← hprod a, ← hprod b,
    list_prod_sub_prod_eq_weightedProductTelescope a b Finset.univ.toList]
  apply abs_weightedProductTelescope_le
  · intro i _
    exact ha i
  · intro i _
    exact hb i

end Causalean.Mathlib.Algebra.BigOperators.Ring

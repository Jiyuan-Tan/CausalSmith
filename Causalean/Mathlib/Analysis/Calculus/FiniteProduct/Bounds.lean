module
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Elementary fourth mixed-jet bound

An ordered-hit term has at most four affected factors. Each is bounded by four,
and the untouched factors are bounded by two. There are exactly card(I)^4 ordered
quadruples. The proof uses only elementary finite-product and finite-sum bounds;
it includes the empty set and singleton without positive-cardinality hypotheses.
-/

public section

open scoped BigOperators
noncomputable section

namespace Causalean.Mathlib.Analysis.Calculus.FiniteProduct

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- If [the factor jets J of a finite index set I satisfy the factor envelopes at a point
(a, u)](hyp:I,J,a,u,h), then for [every index i of I](hyp:i,hi) and [all derivative orders p and
q](hyp:p,q), [the selected factor jet of i at orders (p, q) has absolute value at most four](goal).
The selector's zero extensions make this true at arbitrary orders. -/
theorem factorJet_abs_le_four (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : FactorBoundsAt I J a u) (i : ι) (hi : i ∈ I) (p q : ℕ) :
    |factorJet J i p q a u| ≤ 4 := by
  rcases p with _ | _ | _ | p <;> rcases q with _ | _ | _ | q <;>
    simp only [factorJet]
  all_goals first
    | exact (h.bound00 i hi).trans (by norm_num)
    | exact h.bound10 i hi
    | exact h.bound20 i hi
    | exact h.bound01 i hi
    | exact h.bound11 i hi
    | exact h.bound21 i hi
    | exact h.bound22 i hi
    | norm_num

/-- If [the factor jets J of a finite index set I satisfy the factor envelopes at a point
(a, u)](hyp:I,J,a,u,h), and [a first-coordinate hit list](hyp:xs) has [at most two
entries](hyp:hxs) and [a second-coordinate hit list](hyp:ys) has [at most two entries](hyp:hys),
then [the corresponding ordered-hit Leibniz summand has absolute value at most 256 times two to
the number of factors](goal). -/
theorem leibnizTerm_abs_le (I : Finset ι) (J : FactorJets ι)
    (xs ys : List ι) (a u : ℝ) (h : FactorBoundsAt I J a u)
    (hxs : xs.length ≤ 2) (hys : ys.length ≤ 2) :
    |leibnizTerm I J xs ys a u| ≤ 256 * (2 : ℝ) ^ I.card := by
  let T := I ∩ (xs ++ ys).toFinset
  have hTI : T ⊆ I := Finset.inter_subset_left
  have hTcard : T.card ≤ 4 := calc
    T.card ≤ (xs ++ ys).toFinset.card :=
      Finset.card_le_card Finset.inter_subset_right
    _ ≤ (xs ++ ys).length := List.toFinset_card_le (xs ++ ys)
    _ ≤ 4 := by simp only [List.length_append]; omega
  have hT : (∏ i ∈ T, |factorJet J i (xs.count i) (ys.count i) a u|) ≤
      (4 : ℝ) ^ T.card := by
    calc
      _ ≤ ∏ _i ∈ T, (4 : ℝ) := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun i hi => factorJet_abs_le_four I J a u h i
          (hTI hi) _ _)
      _ = _ := by simp
  have hU : (∏ i ∈ I \ T, |factorJet J i (xs.count i) (ys.count i) a u|) ≤
      (2 : ℝ) ^ (I \ T).card := by
    calc
      _ ≤ ∏ _i ∈ I \ T, (2 : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro i hi
        have hiI := (Finset.mem_sdiff.mp hi).1
        have hnot : i ∉ xs ∧ i ∉ ys := by
          simpa [T, hiI] using (Finset.mem_sdiff.mp hi).2
        simpa [List.count_eq_zero_of_not_mem hnot.1,
          List.count_eq_zero_of_not_mem hnot.2, factorJet] using h.bound00 i hiI
      _ = _ := by simp
  calc
    |leibnizTerm I J xs ys a u| =
        (∏ i ∈ I \ T, |factorJet J i (xs.count i) (ys.count i) a u|) *
          (∏ i ∈ T, |factorJet J i (xs.count i) (ys.count i) a u|) := by
      rw [leibnizTerm, Finset.abs_prod, Finset.prod_sdiff hTI]
    _ ≤ (2 : ℝ) ^ (I \ T).card * (4 : ℝ) ^ T.card :=
      mul_le_mul hU hT (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
    _ ≤ (2 : ℝ) ^ I.card * (4 : ℝ) ^ 4 :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        Finset.sdiff_subset)) (pow_le_pow_right₀ (by norm_num) hTcard)
        (by positivity) (by positivity)
    _ = 256 * (2 : ℝ) ^ I.card := by norm_num; ring

/-- If [the factor jets J of a finite index set I satisfy the factor envelopes at a point
(a, u)](hyp:I,J,a,u,h), then [the mixed (2,2) jet of the finite product has absolute value at
most 256·|I|⁴·2^|I|, where |I| is the number of factors](goal). -/
theorem productJet22_abs_le (I : Finset ι) (J : FactorJets ι) (a u : ℝ)
    (h : FactorBoundsAt I J a u) :
    |productJet22 I J a u| ≤
      256 * (I.card : ℝ) ^ 4 * (2 : ℝ) ^ I.card := by
  unfold productJet22
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, ∑ k ∈ I, ∑ l ∈ I,
        (256 * (2 : ℝ) ^ I.card) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro i hi
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro j hj
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro k hk
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro l hl
      exact leibnizTerm_abs_le I J [i, j] [k, l] a u h (by simp) (by simp)
    _ = 256 * (I.card : ℝ) ^ 4 * (2 : ℝ) ^ I.card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- If [the factor jets J of a finite index set I](hyp:I,J) [satisfy the factor envelopes at every
point of the closed rectangle from a₀ to a₁ in the first coordinate and from u₀ to u₁ in the
second](hyp:a₀,a₁,u₀,u₁,h), then [at every point of that rectangle the mixed (2,2) jet of the
finite product has absolute value at most 256·|I|⁴·2^|I|](goal). -/
theorem productJet22_abs_le_on_rectangle (I : Finset ι) (J : FactorJets ι)
    (a₀ a₁ u₀ u₁ : ℝ)
    (h : ∀ a ∈ Set.Icc a₀ a₁, ∀ u ∈ Set.Icc u₀ u₁, FactorBoundsAt I J a u) :
    ∀ a ∈ Set.Icc a₀ a₁, ∀ u ∈ Set.Icc u₀ u₁,
      |productJet22 I J a u| ≤
        256 * (I.card : ℝ) ^ 4 * (2 : ℝ) ^ I.card := by
  intro a ha u hu
  exact productJet22_abs_le I J a u (h a ha u hu)

end Causalean.Mathlib.Analysis.Calculus.FiniteProduct

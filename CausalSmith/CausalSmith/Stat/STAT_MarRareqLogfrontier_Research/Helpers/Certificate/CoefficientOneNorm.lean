module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm

/-! Coefficient one-norm transport lemmas for the rescaled Chebyshev needle. -/

public section

noncomputable section

open Polynomial
open scoped BigOperators

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Analysis.Approximation.Chebyshev

private lemma coefficientOneNorm_range (p : Polynomial ℝ) {m : ℕ}
    (hp : p.natDegree < m) :
    polynomialCoeffOneNorm p = ∑ i ∈ Finset.range m, |p.coeff i| := by
  change p.sum (fun _ c => |c|) = _
  exact p.sum_over_range' (fun _ => abs_zero) m hp

/-- Given [the specified inputs and assumptions](hyp:p), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialCoeffOneNorm p := by
  change 0 ≤ p.sum (fun _ c => |c|)
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Given [the specified inputs and assumptions](hyp:p,s), [the stated mathematical conclusion holds](goal). -/
lemma sum_abs_coeff_le_polynomialCoeffOneNorm (p : Polynomial ℝ) (s : Finset ℕ) :
    (∑ i ∈ s, |p.coeff i|) ≤ polynomialCoeffOneNorm p := by
  classical
  change (∑ i ∈ s, |p.coeff i|) ≤ ∑ i ∈ p.support, |p.coeff i|
  have heq : (∑ i ∈ s ∩ p.support, |p.coeff i|) =
      ∑ i ∈ s, |p.coeff i| := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i his hi
    have hnmem : i ∉ p.support := by
      intro hiSupport
      exact hi (Finset.mem_inter.mpr ⟨his, hiSupport⟩)
    simp only [mem_support_iff, ne_eq, not_not] at hnmem
    simp [hnmem]
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun i _ _ => abs_nonneg (p.coeff i))

/-- Given [the specified inputs and assumptions](hyp:p,q), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_add_le (p q : Polynomial ℝ) :
    polynomialCoeffOneNorm (p + q) ≤
      polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
  let m := max p.natDegree q.natDegree + 1
  rw [coefficientOneNorm_range (p + q)
      (lt_of_le_of_lt (natDegree_add_le _ _) (Nat.lt_succ_self _)),
    coefficientOneNorm_range p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    coefficientOneNorm_range q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [coeff_add] using abs_add_le (p.coeff i) (q.coeff i)

/-- Given [the specified inputs and assumptions](hyp:p,q), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_sub_le (p q : Polynomial ℝ) :
    polynomialCoeffOneNorm (p - q) ≤
      polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
  let m := max p.natDegree q.natDegree + 1
  rw [coefficientOneNorm_range (p - q)
      (lt_of_le_of_lt (natDegree_sub_le _ _) (Nat.lt_succ_self _)),
    coefficientOneNorm_range p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    coefficientOneNorm_range q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [coeff_sub] using abs_sub (p.coeff i) (q.coeff i)

/-- Given [the specified inputs and assumptions](hyp:c), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_C (c : ℝ) :
    polynomialCoeffOneNorm (C c) = |c| := by
  by_cases hc : c = 0
  · simp [hc, polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [coefficientOneNorm_range (C c) (m := 1) (by simp)]
    simp

/-- Given [the specified inputs and assumptions](hyp:ι,s,f), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial ℝ) :
    polynomialCoeffOneNorm (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, polynomialCoeffOneNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (polynomialCoeffOneNorm_add_le _ _).trans (add_le_add_right ih _)

/-- Given [the specified inputs and assumptions](hyp:p,m), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_pow_le (p : Polynomial ℝ) (m : ℕ) :
    polynomialCoeffOneNorm (p ^ m) ≤ polynomialCoeffOneNorm p ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, show (1 : Polynomial ℝ) = C 1 by simp,
        polynomialCoeffOneNorm_C]
      norm_num
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact (polynomialCoeffOneNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (polynomialCoeffOneNorm_nonneg p))

/-- Given [the specified inputs and assumptions](hyp:p,q,hq), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_comp_le (p q : Polynomial ℝ)
    (hq : 1 ≤ polynomialCoeffOneNorm q) :
    polynomialCoeffOneNorm (p.comp q) ≤
      polynomialCoeffOneNorm p * polynomialCoeffOneNorm q ^ p.natDegree := by
  classical
  rw [Polynomial.comp_eq_sum_left]
  calc
    polynomialCoeffOneNorm
        (p.sum fun e a => C a * q ^ e) ≤
        ∑ e ∈ p.support, polynomialCoeffOneNorm (C (p.coeff e) * q ^ e) := by
          simpa only [Polynomial.sum] using
            polynomialCoeffOneNorm_sum_le p.support
              (fun e => C (p.coeff e) * q ^ e)
    _ ≤ ∑ e ∈ p.support, |p.coeff e| * polynomialCoeffOneNorm q ^ e := by
          apply Finset.sum_le_sum
          intro e he
          calc
            polynomialCoeffOneNorm (C (p.coeff e) * q ^ e) ≤
                polynomialCoeffOneNorm (C (p.coeff e)) *
                  polynomialCoeffOneNorm (q ^ e) :=
              polynomialCoeffOneNorm_mul_le _ _
            _ = |p.coeff e| * polynomialCoeffOneNorm (q ^ e) := by
              rw [polynomialCoeffOneNorm_C]
            _ ≤ |p.coeff e| * polynomialCoeffOneNorm q ^ e := by
              gcongr
              exact polynomialCoeffOneNorm_pow_le q e
    _ ≤ ∑ e ∈ p.support,
        |p.coeff e| * polynomialCoeffOneNorm q ^ p.natDegree := by
          apply Finset.sum_le_sum
          intro e he
          gcongr
          exact le_natDegree_of_ne_zero (mem_support_iff.mp he)
    _ = polynomialCoeffOneNorm p *
        polynomialCoeffOneNorm q ^ p.natDegree := by
          change (∑ e ∈ p.support,
            |p.coeff e| * polynomialCoeffOneNorm q ^ p.natDegree) =
            (∑ e ∈ p.support, |p.coeff e|) *
              polynomialCoeffOneNorm q ^ p.natDegree
          rw [Finset.sum_mul]

/-- Given [the specified inputs and assumptions](hyp:p), [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_divX_le (p : Polynomial ℝ) :
    polynomialCoeffOneNorm p.divX ≤ polynomialCoeffOneNorm p := by
  by_cases hp : p = 0
  · simp [hp, polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [coefficientOneNorm_range p.divX
      (lt_of_le_of_lt natDegree_divX_le (Nat.lt_succ_self _)),
    coefficientOneNorm_range p (Nat.lt_succ_self _)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [coeff_divX]
    have htop : p.coeff (p.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    simp only [htop, abs_zero, add_zero]
    exact le_add_of_nonneg_right (abs_nonneg (p.coeff 0))

/-- [the stated mathematical conclusion holds](goal). -/
lemma polynomialCoeffOneNorm_one_sub_two_X :
    polynomialCoeffOneNorm (C 1 - C 2 * X : Polynomial ℝ) = 3 := by
  rw [coefficientOneNorm_range (C 1 - C 2 * X : Polynomial ℝ) (m := 2) (by
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (by norm_num))]
  norm_num [Finset.sum_range_succ, coeff_sub, coeff_one, coeff_C_mul, coeff_X]

/-- Given [the specified inputs and assumptions](hyp:p,B), [the stated mathematical conclusion holds](goal). -/
lemma C_mul_divX_comp_scale (p : Polynomial ℝ) (B : ℝ) :
    C B * (p.divX.comp (C B * X)) = (p.comp (C B * X)).divX := by
  ext i
  simp only [coeff_C_mul, coeff_divX, comp_C_mul_X_coeff]
  rw [pow_succ]
  ring

end CausalSmith.Stat.MarRareqLogfrontier

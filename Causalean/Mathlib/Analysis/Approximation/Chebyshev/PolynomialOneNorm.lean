module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Real.Basic

/-!
# Coefficient one-norm of real polynomials

The finite sum of absolute monomial coefficients is submultiplicative. This gives the
quantitative algebraic input for equispaced Lagrange basis bounds.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A real polynomial](hyp:p) determines [its coefficient one-norm](goal).

The coefficient one-norm of a real polynomial is the sum of the absolute values of all
its monomial coefficients, using the established Causalean definition.
-/
abbrev polynomialCoeffOneNorm (p : Polynomial ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1 p

/-- [Two real polynomials](hyp:p,q) have [a coefficient one-norm for their product no larger than the product of their coefficient one-norms](goal).

The coefficient one-norm of a product is at most the product of the coefficient one-norms.

Expand each coefficient of the product as a finite convolution and apply the triangle inequality;
finite reindexing then gives the product of the two coefficient sums.
-/
theorem polynomialCoeffOneNorm_mul_le (p q : Polynomial ℝ) :
    polynomialCoeffOneNorm (p * q) ≤
      polynomialCoeffOneNorm p * polynomialCoeffOneNorm q := by
  classical
  have hadd (r s : Polynomial ℝ) :
      polynomialCoeffOneNorm (r + s) ≤
        polynomialCoeffOneNorm r + polynomialCoeffOneNorm s := by
    let m := max r.natDegree s.natDegree + 1
    have hrange (t : Polynomial ℝ) (ht : t.natDegree < m) :
        polynomialCoeffOneNorm t = ∑ k ∈ Finset.range m, |t.coeff k| := by
      change t.sum (fun _ c => |c|) = _
      exact t.sum_over_range' (fun _ => abs_zero) m ht
    rw [hrange (r + s)
        (lt_of_le_of_lt (natDegree_add_le _ _) (Nat.lt_succ_self _)),
      hrange r (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
      hrange s (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [coeff_add] using abs_add_le (r.coeff i) (s.coeff i)
  have hzero : polynomialCoeffOneNorm (0 : Polynomial ℝ) = 0 := by
    simp [polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  have hsum (s : Finset ℕ) (f : ℕ → Polynomial ℝ) :
      polynomialCoeffOneNorm (∑ i ∈ s, f i) ≤
        ∑ i ∈ s, polynomialCoeffOneNorm (f i) := by
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hadd _ _).trans (add_le_add_right ih _)
  have hmono (n : ℕ) (a : ℝ) :
      polynomialCoeffOneNorm (monomial n a) = |a| := by
    by_cases ha : a = 0
    · simp [ha, polynomialCoeffOneNorm,
        Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
    · simp [polynomialCoeffOneNorm,
        Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1,
        support_monomial n ha]
  rw [Polynomial.mul_eq_sum_sum]
  calc
    polynomialCoeffOneNorm
        (∑ i ∈ p.support, q.sum fun j a ↦ monomial (i + j) (p.coeff i * a))
        ≤ ∑ i ∈ p.support,
            polynomialCoeffOneNorm
              (q.sum fun j a ↦ monomial (i + j) (p.coeff i * a)) := by
            exact hsum p.support
              (fun i ↦ q.sum fun j a ↦ monomial (i + j) (p.coeff i * a))
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
          polynomialCoeffOneNorm (monomial (i + j) (p.coeff i * q.coeff j)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Polynomial.sum] using
          (hsum q.support (fun j ↦ monomial (i + j) (p.coeff i * q.coeff j)))
    _ = polynomialCoeffOneNorm p * polynomialCoeffOneNorm q := by
        simp only [hmono, abs_mul]
        change (∑ i ∈ p.support, ∑ j ∈ q.support,
            |p.coeff i| * |q.coeff j|) =
          (∑ i ∈ p.support, |p.coeff i|) *
            (∑ j ∈ q.support, |q.coeff j|)
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]

/-- A linear factor `X - x` with `x` in the unit interval has coefficient one-norm at most two. -/
theorem polynomialCoeffOneNorm_X_sub_C_le_two (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    polynomialCoeffOneNorm (X - C x : Polynomial ℝ) ≤ 2 := by
  have hd : (X - C x : Polynomial ℝ).natDegree < 2 := by
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  rw [show polynomialCoeffOneNorm (X - C x : Polynomial ℝ) =
      ∑ k ∈ Finset.range 2, |(X - C x : Polynomial ℝ).coeff k| from
      (X - C x : Polynomial ℝ).sum_over_range' (fun _ => abs_zero) 2 hd]
  simp [Finset.sum_range_succ, abs_of_nonneg hx0]
  linarith

end Causalean.Mathlib.Analysis.Approximation.Chebyshev



namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- For a [natural degree](hyp:r), define the shifted first-kind Chebyshev
polynomial by reflecting its argument from the unit interval. The result is [the shifted first-kind Chebyshev polynomial](goal). -/
noncomputable def shiftedCheb (r : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (r : ℤ)).comp
    (1 - Polynomial.C (2 : ℝ) * Polynomial.X)

/-- For [a real polynomial and truncation length](hyp:p,m), if [the degree lies below that length](hyp:hp),
its [coefficient one-norm is the corresponding finite range sum](goal). -/
lemma polynomialCoeffOneNorm_range (p : ℝ[X]) {m : ℕ}
    (hp : p.natDegree < m) :
    polynomialCoeffOneNorm p = ∑ i ∈ Finset.range m, |p.coeff i| := by
  change p.sum (fun _ c => |c|) = _
  exact p.sum_over_range' (fun _ => abs_zero) m hp

/-- [The coefficient one-norm of a difference](goal) is at most the sum of the
coefficient one-norms of [the two real polynomials](hyp:p,q). -/
lemma polynomialCoeffOneNorm_sub_le (p q : ℝ[X]) :
    polynomialCoeffOneNorm (p - q) ≤ polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
  let m := max p.natDegree q.natDegree + 1
  rw [polynomialCoeffOneNorm_range (p - q)
      (lt_of_le_of_lt (natDegree_sub_le _ _) (Nat.lt_succ_self _)),
    polynomialCoeffOneNorm_range p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    polynomialCoeffOneNorm_range q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [coeff_sub] using abs_sub (p.coeff i) (q.coeff i)

private lemma shiftFactor_natDegree_le :
    (1 - Polynomial.C (2 : ℝ) * Polynomial.X : ℝ[X]).natDegree ≤ 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact natDegree_mul_le.trans (by norm_num)

private lemma polynomialCoeffOneNorm_two_shift_factor :
    polynomialCoeffOneNorm
      (2 * (1 - Polynomial.C (2 : ℝ) * Polynomial.X) : ℝ[X]) = 6 := by
  rw [polynomialCoeffOneNorm_range _ (m := 2) (by
    apply lt_of_le_of_lt natDegree_mul_le
    calc
      (2 : ℝ[X]).natDegree +
          (1 - Polynomial.C (2 : ℝ) * Polynomial.X : ℝ[X]).natDegree ≤
          0 + 1 := Nat.add_le_add (by norm_num) shiftFactor_natDegree_le
      _ < 2 := by norm_num)]
  norm_num [Finset.sum_range_succ, coeff_sub, coeff_one, coeff_C_mul, coeff_X]

/-- For a [natural degree](hyp:r), the shifted Chebyshev polynomials satisfy the
stated two-step recurrence, which controls their coefficient growth. The result is [the two-step recurrence for shifted Chebyshev polynomials](goal). -/
lemma shiftedCheb_recurrence (r : ℕ) :
    shiftedCheb (r + 2) =
      2 * (1 - Polynomial.C (2 : ℝ) * Polynomial.X) *
        shiftedCheb (r + 1) - shiftedCheb r := by
  unfold shiftedCheb
  push_cast
  rw [Polynomial.Chebyshev.T_add_two, Polynomial.sub_comp, Polynomial.mul_comp]
  simp

/-- For a [natural degree](hyp:r), the coefficient one-norm of the shifted
Chebyshev polynomial is at most `7 ^ r`. The result is [the `7 ^ r` coefficient one-norm bound](goal). -/
lemma shiftedCheb_coeffL1_le (r : ℕ) :
    polynomialCoeffOneNorm (shiftedCheb r) ≤ (7 : ℝ) ^ r := by
  induction r using Nat.twoStepInduction with
  | zero =>
      rw [polynomialCoeffOneNorm_range _ (m := 1) (by simp [shiftedCheb])]
      norm_num [shiftedCheb]
  | one =>
      rw [polynomialCoeffOneNorm_range _ (m := 2) (by
        simpa [shiftedCheb] using
          (lt_of_le_of_lt shiftFactor_natDegree_le (by norm_num : 1 < 2)))]
      norm_num [shiftedCheb, Finset.sum_range_succ, coeff_sub,
        coeff_one, coeff_C_mul, coeff_X]
  | more r hr hr1 =>
      rw [shiftedCheb_recurrence]
      calc
        polynomialCoeffOneNorm
            (2 * (1 - Polynomial.C (2 : ℝ) * Polynomial.X) *
              shiftedCheb (r + 1) - shiftedCheb r) ≤
            polynomialCoeffOneNorm
                (2 * (1 - Polynomial.C (2 : ℝ) * Polynomial.X) *
                  shiftedCheb (r + 1)) +
              polynomialCoeffOneNorm (shiftedCheb r) :=
          polynomialCoeffOneNorm_sub_le _ _
        _ ≤ polynomialCoeffOneNorm
              (2 * (1 - Polynomial.C (2 : ℝ) * Polynomial.X) : ℝ[X]) *
              polynomialCoeffOneNorm (shiftedCheb (r + 1)) +
            polynomialCoeffOneNorm (shiftedCheb r) := by
          gcongr
          exact polynomialCoeffOneNorm_mul_le _ _
        _ = 6 * polynomialCoeffOneNorm (shiftedCheb (r + 1)) +
            polynomialCoeffOneNorm (shiftedCheb r) := by
          rw [polynomialCoeffOneNorm_two_shift_factor]
        _ ≤ 6 * (7 : ℝ) ^ (r + 1) + (7 : ℝ) ^ r := by
          gcongr
        _ ≤ (7 : ℝ) ^ (r + 2) := by
          have hp : 0 ≤ (7 : ℝ) ^ r := pow_nonneg (by norm_num) _
          calc
            6 * (7 : ℝ) ^ (r + 1) + 7 ^ r = 43 * 7 ^ r := by
              rw [pow_succ]
              ring
            _ ≤ 49 * 7 ^ r := mul_le_mul_of_nonneg_right (by norm_num) hp
            _ = (7 : ℝ) ^ (r + 2) := by
              rw [pow_add]
              norm_num
              ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev

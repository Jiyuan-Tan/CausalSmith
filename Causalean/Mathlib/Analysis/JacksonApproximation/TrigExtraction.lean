import Causalean.Mathlib.Analysis.JacksonApproximation.Kernel

/-!
# Extracting algebraic polynomials from even trigonometric polynomials

This module converts finite even trigonometric polynomials into ordinary polynomials in the
cosine coordinate, proves the converse construction, and controls coefficient growth in the
Chebyshev basis.
-/

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open Real Polynomial
open scoped BigOperators
open scoped BigOperators
/-- [A frequency limit](hyp:n) and [a real-valued function](hyp:f) determine [the assertion that
the function is a real trigonometric polynomial within that limit](goal).
-/

abbrev IsTrigPolyLE :=
  Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE

/-- [A real polynomial](hyp:p) determines [its coefficient one-norm](goal), the sum of the
absolute values of its nonzero coefficients.
-/
noncomputable def polyCoeffL1 (p : Polynomial ℝ) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

private lemma polyCoeffL1_eq_sum_range_of_natDegree_lt (p : Polynomial ℝ) {m : ℕ}
    (hp : p.natDegree < m) :
    polyCoeffL1 p = ∑ k ∈ Finset.range m, |p.coeff k| := by
  change p.sum (fun _ c => |c|) = _
  exact p.sum_over_range' (fun _ => abs_zero) m hp

private lemma polyCoeffL1_zero : polyCoeffL1 (0 : Polynomial ℝ) = 0 := by
  simp [polyCoeffL1]

private lemma polyCoeffL1_add_le (p q : Polynomial ℝ) :
    polyCoeffL1 (p + q) ≤ polyCoeffL1 p + polyCoeffL1 q := by
  -- Put all three coefficient sums over one range, then use the scalar triangle inequality.
  let m := max p.natDegree q.natDegree + 1
  rw [polyCoeffL1_eq_sum_range_of_natDegree_lt (p + q)
      (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (Nat.lt_succ_self _)),
    polyCoeffL1_eq_sum_range_of_natDegree_lt p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    polyCoeffL1_eq_sum_range_of_natDegree_lt q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [Polynomial.coeff_add] using abs_add_le (p.coeff i) (q.coeff i)

private lemma polyCoeffL1_sub_le (p q : Polynomial ℝ) :
    polyCoeffL1 (p - q) ≤ polyCoeffL1 p + polyCoeffL1 q := by
  let m := max p.natDegree q.natDegree + 1
  rw [polyCoeffL1_eq_sum_range_of_natDegree_lt (p - q)
      (lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (Nat.lt_succ_self _)),
    polyCoeffL1_eq_sum_range_of_natDegree_lt p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    polyCoeffL1_eq_sum_range_of_natDegree_lt q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [sub_eq_add_neg, Polynomial.coeff_add, Polynomial.coeff_neg, abs_neg] using
      abs_add_le (p.coeff i) (-q.coeff i)

private lemma polyCoeffL1_smul (c : ℝ) (p : Polynomial ℝ) :
    polyCoeffL1 (c • p) = |c| * polyCoeffL1 p := by
  rw [polyCoeffL1_eq_sum_range_of_natDegree_lt (c • p)
      (lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) (Nat.lt_succ_self _)),
    polyCoeffL1_eq_sum_range_of_natDegree_lt p (Nat.lt_succ_self _)]
  simp only [Polynomial.coeff_smul, smul_eq_mul, abs_mul, Finset.mul_sum]

private lemma polyCoeffL1_X_mul (p : Polynomial ℝ) :
    polyCoeffL1 (Polynomial.X * p) = polyCoeffL1 p := by
  by_cases hp : p = 0
  · simp [hp, polyCoeffL1]
  · rw [polyCoeffL1_eq_sum_range_of_natDegree_lt (Polynomial.X * p)
        (m := p.natDegree + 2) (by rw [Polynomial.natDegree_X_mul hp]; omega),
      polyCoeffL1_eq_sum_range_of_natDegree_lt p (Nat.lt_succ_self _)]
    -- Multiplication by `X` merely shifts every coefficient index up by one.
    rw [show p.natDegree + 2 = (p.natDegree + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp only [Polynomial.coeff_X_mul_zero, abs_zero, add_zero, Nat.succ_eq_add_one,
      Polynomial.coeff_X_mul]

private lemma polyCoeffL1_sum_le {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial ℝ) :
    polyCoeffL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyCoeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyCoeffL1_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (polyCoeffL1_add_le _ _).trans (add_le_add_right ih _)

/-- Given [a frequency limit](hyp:n) and [a real function](hyp:q), if [the function is a
trigonometric polynomial within that limit](hyp:hq) and [is symmetric about zero](hyp:heven),
then [it is an ordinary polynomial in the cosine coordinate with degree at most that
limit](goal).
-/
theorem even_trigPoly_exists_polynomial {n : ℕ} {q : ℝ → ℝ}
    (hq : IsTrigPolyLE n q) (heven : Function.Even q) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ ∀ t : ℝ, p.eval (Real.cos t) = q t := by
  classical
  rcases hq with ⟨a, b, hq⟩
  let p : Polynomial ℝ :=
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (a k) * Polynomial.Chebyshev.T ℝ (k : ℤ)
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · intro t
    have ht := hq t
    have hnt := hq (-t)
    rw [heven t] at hnt
    simp only [mul_neg, Real.cos_neg, Real.sin_neg] at hnt
    have hnt' : q t = ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * t) - b k * Real.sin ((k : ℝ) * t)) := by
      simpa [sub_eq_add_neg] using hnt
    -- Averaging the identities at `t` and `-t` cancels every sine term.
    have hcos : q t = ∑ k ∈ Finset.range (n + 1),
        a k * Real.cos ((k : ℝ) * t) := by
      calc
        q t = (q t + q t) / 2 := by ring
        _ = ((∑ k ∈ Finset.range (n + 1),
                (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t))) +
              (∑ k ∈ Finset.range (n + 1),
                (a k * Real.cos ((k : ℝ) * t) - b k * Real.sin ((k : ℝ) * t)))) / 2 := by
              rw [← ht, ← hnt']
        _ = ∑ k ∈ Finset.range (n + 1), a k * Real.cos ((k : ℝ) * t) := by
              rw [← Finset.sum_add_distrib, Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k _
              ring
    rw [hcos]
    dsimp [p]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_C_mul, Polynomial.Chebyshev.T_real_cos]
    norm_num

/-- Given [a frequency limit](hyp:n) and [a real polynomial](hyp:p) whose [degree is at most that
limit](hyp:hp), [composition with cosine is an even trigonometric polynomial within the same
frequency limit](goal).
-/
theorem polynomial_cos_is_even_trigPoly {n : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) :
    IsTrigPolyLE n (fun t => p.eval (Real.cos t)) ∧
      Function.Even (fun t => p.eval (Real.cos t)) := by
  refine ⟨Causalean.Mathlib.Analysis.BernsteinSzegoTrig.cosComp_isTrigPolyLE p n hp, ?_⟩
  intro t
  simp

/-- For [a nonnegative integer index](hyp:n), [the coefficient one-norm of the corresponding
first-kind Chebyshev polynomial is at most three to that index](goal).
-/
theorem chebyshev_coeffL1_le (n : ℕ) :
    polyCoeffL1 (Polynomial.Chebyshev.T ℝ (n : ℤ)) ≤ (3 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change polyCoeffL1 (Polynomial.Chebyshev.T ℝ 0) ≤ 1
      rw [Polynomial.Chebyshev.T_zero,
        polyCoeffL1_eq_sum_range_of_natDegree_lt (1 : Polynomial ℝ) (m := 1) (by simp)]
      simp
  | one =>
      norm_num only [Nat.cast_one, pow_one]
      rw [Polynomial.Chebyshev.T_one,
        polyCoeffL1_eq_sum_range_of_natDegree_lt Polynomial.X (m := 2) (by simp)]
      norm_num [Finset.sum_range_succ, Polynomial.coeff_X]
  | more n hn hn1 =>
      have hT :
          Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
            (2 : ℝ) • (Polynomial.X *
              Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) -
              Polynomial.Chebyshev.T ℝ (n : ℤ) := by
        convert Polynomial.Chebyshev.T_add_two ℝ (n : ℤ) using 1
        · norm_num
        · simp only [Polynomial.smul_eq_C_mul]
          norm_num
          rw [Polynomial.C_ofNat]
          ring
      rw [hT]
      calc
        polyCoeffL1 ((2 : ℝ) • (Polynomial.X *
              Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) -
              Polynomial.Chebyshev.T ℝ (n : ℤ))
            ≤ polyCoeffL1 ((2 : ℝ) • (Polynomial.X *
                Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ))) +
                polyCoeffL1 (Polynomial.Chebyshev.T ℝ (n : ℤ)) :=
              polyCoeffL1_sub_le _ _
        _ = 2 * polyCoeffL1 (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) +
                polyCoeffL1 (Polynomial.Chebyshev.T ℝ (n : ℤ)) := by
              rw [polyCoeffL1_smul, polyCoeffL1_X_mul]
              norm_num
        _ ≤ 2 * (3 : ℝ) ^ (n + 1) + (3 : ℝ) ^ n := by gcongr
        _ = 7 * (3 : ℝ) ^ n := by
              rw [pow_succ]
              ring
        _ ≤ 9 * (3 : ℝ) ^ n := by
              gcongr
              norm_num
        _ = (3 : ℝ) ^ (n + 2) := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
              ring

/-- Given [a frequency limit](hyp:n) and [real cosine coefficients](hyp:a), [the finite cosine sum
has an ordinary polynomial representation of bounded degree whose coefficient one-norm is
bounded by the stated weighted sum](goal).
-/
theorem cosine_sum_exists_polynomial (n : ℕ) (a : ℕ → ℝ) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ n ∧
      (∀ t : ℝ,
        p.eval (Real.cos t) = ∑ k ∈ Finset.range (n + 1), a k * Real.cos ((k : ℝ) * t)) ∧
      polyCoeffL1 p ≤ ∑ k ∈ Finset.range (n + 1), |a k| * (3 : ℝ) ^ k := by
  classical
  let p : Polynomial ℝ :=
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (a k) * Polynomial.Chebyshev.T ℝ (k : ℤ)
  refine ⟨p, ?_, ?_, ?_⟩
  · dsimp [p]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · intro t
    dsimp [p]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_C_mul, Polynomial.Chebyshev.T_real_cos]
    norm_num
  · dsimp [p]
    calc
      polyCoeffL1 (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (a k) * Polynomial.Chebyshev.T ℝ (k : ℤ))
          ≤ ∑ k ∈ Finset.range (n + 1),
              polyCoeffL1 (Polynomial.C (a k) *
                Polynomial.Chebyshev.T ℝ (k : ℤ)) := polyCoeffL1_sum_le _ _
      _ = ∑ k ∈ Finset.range (n + 1),
              |a k| * polyCoeffL1 (Polynomial.Chebyshev.T ℝ (k : ℤ)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Polynomial.C_mul', polyCoeffL1_smul]
      _ ≤ ∑ k ∈ Finset.range (n + 1), |a k| * (3 : ℝ) ^ k := by
            exact Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (chebyshev_coeffL1_le k) (abs_nonneg (a k))

end Causalean.Mathlib.Analysis.JacksonApproximation

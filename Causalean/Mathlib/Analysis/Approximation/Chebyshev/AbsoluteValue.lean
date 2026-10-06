module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Rate
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit Chebyshev truncation for absolute value

This module exposes the fixed even Chebyshev polynomial that approximates absolute value on the
unit interval, together with its exact error, monomial-coefficient, and even-degree bounds.
The Fourier-series proof is reused from the general absolute-value approximation infrastructure.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue

open Polynomial

/-- [A truncation length](hyp:m) determines [the explicit even Chebyshev polynomial approximating absolute value](goal), [given by the existing exact Fourier truncation](step:1). -/
abbrev absChebPoly (m : ℕ) : Polynomial ℝ :=
  Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.absChebPoly m

/-- [A truncation length](hyp:m) gives [the constant two over π followed by its first even Chebyshev modes with their exact alternating coefficients](goal). -/
theorem absChebPoly_eq (m : ℕ) :
    absChebPoly m = C (2 / Real.pi) +
      ∑ j ∈ Finset.range m,
        C ((4 / Real.pi) * (-1 : ℝ) ^ j /
          (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)) *
          Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ) := by
  simp only [absChebPoly, Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.absChebPoly,
    Polynomial.smul_eq_C_mul]

/-- [A truncation length and argument](hyp:m,x) give [the value of the explicit truncation as its finite even Chebyshev expansion](goal). -/
theorem absChebPoly_eval (m : ℕ) (x : ℝ) :
    (absChebPoly m).eval x = 2 / Real.pi +
      ∑ j ∈ Finset.range m,
        (4 / Real.pi) * (-1 : ℝ) ^ j *
          (Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)).eval x /
            (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1) := by
  exact Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.absChebPoly_eval m x

/-- [A truncation length](hyp:m) gives [a polynomial whose degree is at most twice that length](goal). -/
theorem absChebPoly_natDegree_le (m : ℕ) : (absChebPoly m).natDegree ≤ 2 * m :=
  Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.absChebPoly_natDegree_le m

/-- [A truncation length](hyp:m), evaluated [at a point in the closed unit interval](hyp:hx), has [absolute approximation error at most two divided by π times twice the length plus one](goal). -/
theorem absChebPoly_error_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    abs ((absChebPoly m).eval x - abs x) ≤ 2 / (Real.pi * (2 * (m : ℝ) + 1)) := by
  rw [abs_sub_comm]
  exact Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.absChebPoly_error_le m hx

/-- [A truncation length](hyp:m) gives [the same explicit polynomial written with one-based Chebyshev mode indices](goal). -/
theorem absChebPoly_eq_sum_Icc (m : ℕ) :
    absChebPoly m = C (2 / Real.pi) +
      ∑ v ∈ Finset.Icc 1 m,
        C ((4 / Real.pi) * (-1 : ℝ) ^ (v + 1) / (4 * (v : ℝ) ^ 2 - 1)) *
          Polynomial.Chebyshev.T ℝ (2 * v : ℕ) := by
  rw [absChebPoly_eq]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    have hsign : (-1 : ℝ) ^ (m + 1 + 1) = (-1 : ℝ) ^ m := by
      rw [pow_succ, pow_succ]
      ring
    simp only [hsign]

/-- [A positive truncation length](hyp:m,hm) gives [a polynomial whose monomial coefficient one-norm is at most two to the power three times that length](goal). -/
theorem absChebPoly_coeffOneNorm_le (m : ℕ) (hm : 1 ≤ m) :
    polynomialCoeffOneNorm (absChebPoly m) ≤ (2 : ℝ) ^ (3 * m) := by
  classical
  have hadd (p q : Polynomial ℝ) :
      polynomialCoeffOneNorm (p + q) ≤
        polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
    let n := max p.natDegree q.natDegree + 1
    rw [polynomialCoeffOneNorm_range (p + q) (m := n)
        (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (Nat.lt_succ_self _)),
      polynomialCoeffOneNorm_range p
        (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
      polynomialCoeffOneNorm_range q
        (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [Polynomial.coeff_add] using abs_add_le (p.coeff i) (q.coeff i)
  have hC (c : ℝ) : polynomialCoeffOneNorm (Polynomial.C c) = |c| := by
    rw [polynomialCoeffOneNorm_range _ (m := 1) (by simp)]
    simp
  have hmode (j : ℕ) :
      polynomialCoeffOneNorm
        (Polynomial.C ((4 / Real.pi) * (-1 : ℝ) ^ j /
          (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)) *
          Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)) ≤ 3 * (8 : ℝ) ^ j := by
    have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hd : 3 ≤ 4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1 := by nlinarith
    have hdpos : 0 < 4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1 := by linarith
    have hc : |(4 / Real.pi) * (-1 : ℝ) ^ j /
        (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)| ≤ (1 / 2 : ℝ) := by
      rw [abs_div, abs_mul, abs_pow]
      norm_num only [abs_neg, abs_one, one_pow, mul_one]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi), abs_of_pos hdpos]
      apply (div_le_iff₀ hdpos).2
      have hpi : 4 / Real.pi ≤ (4 / 3 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
      linarith
    have hs : (1 + Real.sqrt 2) ^ 2 ≤ (6 : ℝ) := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      have hroot : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by nlinarith
      nlinarith
    have hpow : (1 + Real.sqrt 2) ^ (2 * (j + 1)) ≤ (6 : ℝ) ^ (j + 1) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hs _
    calc
      polynomialCoeffOneNorm _ ≤
          polynomialCoeffOneNorm (Polynomial.C ((4 / Real.pi) * (-1 : ℝ) ^ j /
            (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1))) *
          polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)) :=
        polynomialCoeffOneNorm_mul_le _ _
      _ ≤ (1 / 2 : ℝ) * (1 + Real.sqrt 2) ^ (2 * (j + 1)) := by
        rw [hC]
        apply mul_le_mul hc (polynomialCoeffOneNorm_chebyshev_le (2 * (j + 1)))
        · change 0 ≤ ∑ k ∈ (Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)).support,
            |(Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)).coeff k|
          exact Finset.sum_nonneg fun _ _ => abs_nonneg _
        · norm_num
      _ ≤ (1 / 2 : ℝ) * 6 ^ (j + 1) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ 3 * (8 : ℝ) ^ j := by
        rw [pow_succ]
        have hp : (6 : ℝ) ^ j ≤ (8 : ℝ) ^ j :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        linarith
  have hall (n : ℕ) : polynomialCoeffOneNorm (absChebPoly n) ≤ (8 : ℝ) ^ n := by
    induction n with
    | zero =>
      rw [absChebPoly_eq]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, hC]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
      apply (div_le_iff₀ Real.pi_pos).2
      linarith [Real.pi_gt_three]
    | succ n ih =>
      have heq : absChebPoly (n + 1) = absChebPoly n +
          Polynomial.C ((4 / Real.pi) * (-1 : ℝ) ^ n /
            (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)) *
            Polynomial.Chebyshev.T ℝ (2 * (n + 1) : ℕ) := by
        rw [absChebPoly_eq, absChebPoly_eq, Finset.sum_range_succ]
        exact (add_assoc _ _ _).symm
      rw [heq]
      calc
        polynomialCoeffOneNorm _ ≤ polynomialCoeffOneNorm (absChebPoly n) +
            polynomialCoeffOneNorm _ := hadd _ _
        _ ≤ (8 : ℝ) ^ n + 3 * (8 : ℝ) ^ n := add_le_add ih (hmode n)
        _ ≤ (8 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) n]
  calc
    polynomialCoeffOneNorm (absChebPoly m) ≤ (8 : ℝ) ^ m := hall m
    _ = (2 : ℝ) ^ (3 * m) := by rw [pow_mul]; norm_num

/-- [A positive truncation length](hyp:m,hm) and [a monomial index](hyp:k) give [an absolute coefficient bound of two to the power three times the length](goal). -/
theorem absChebPoly_coeff_le (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    |(absChebPoly m).coeff k| ≤ (2 : ℝ) ^ (3 * m) := by
  classical
  have hb : |(absChebPoly m).coeff k| ≤ polynomialCoeffOneNorm (absChebPoly m) := by
    change |(absChebPoly m).coeff k| ≤
      ∑ j ∈ (absChebPoly m).support, |(absChebPoly m).coeff j|
    by_cases hk : k ∈ (absChebPoly m).support
    · exact Finset.single_le_sum (fun j _ => abs_nonneg ((absChebPoly m).coeff j)) hk
    · have hzero : (absChebPoly m).coeff k = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hk
      rw [hzero, abs_zero]
      exact Finset.sum_nonneg (fun j _ => abs_nonneg ((absChebPoly m).coeff j))
  exact hb.trans (absChebPoly_coeffOneNorm_le m hm)

/-- [An even natural degree](hyp:D,hD) has [degree equal to twice its half-degree](goal). -/
theorem two_mul_halfDegree (D : ℕ) (hD : Even D) : 2 * (D / 2) = D := by
  obtain ⟨m, hm⟩ := hD
  omega

/-- [A natural degree at least two](hyp:D,hD2) has [a positive half-degree](goal). -/
theorem halfDegree_pos (D : ℕ) (hD2 : 2 ≤ D) : 1 ≤ D / 2 := by
  omega

/-- [An even natural degree](hyp:D,hD) has [equal natural-power and real-power forms of the coefficient constant](goal). -/
theorem coefficientConstant_eq_rpow (D : ℕ) (hD : Even D) :
    (2 : ℝ) ^ (3 * (D / 2)) = (2 : ℝ) ^ ((3 : ℝ) * (D : ℝ) / 2) := by
  have hn := two_mul_halfDegree D hD
  have hr : (2 : ℝ) * (D / 2 : ℕ) = (D : ℝ) := by exact_mod_cast hn
  rw [show (3 : ℝ) * (D : ℝ) / 2 = ((3 * (D / 2) : ℕ) : ℝ) by
    push_cast
    linarith, Real.rpow_natCast]

/-- [An even natural degree](hyp:D,hD) gives [a half-degree truncation whose degree is at most that degree](goal). -/
theorem absChebPoly_halfDegree_natDegree_le (D : ℕ) (hD : Even D) :
    (absChebPoly (D / 2)).natDegree ≤ D := by
  simpa only [two_mul_halfDegree D hD] using absChebPoly_natDegree_le (D / 2)

/-- [An even natural degree](hyp:D,hD), evaluated [at a point in the closed unit interval](hyp:hx), has [absolute approximation error at most two divided by π times the degree plus one](goal). -/
theorem absChebPoly_halfDegree_error_le (D : ℕ) (hD : Even D)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    abs ((absChebPoly (D / 2)).eval x - abs x) ≤ 2 / (Real.pi * ((D : ℝ) + 1)) := by
  have hr : (2 : ℝ) * (D / 2 : ℕ) = (D : ℝ) := by
    exact_mod_cast two_mul_halfDegree D hD
  simpa only [hr] using absChebPoly_error_le (D / 2) hx

/-- [An even degree at least two](hyp:D,hD,hD2) and [a monomial index](hyp:k) give [an absolute coefficient bound with real-power exponent three halves of the degree](goal). -/
theorem absChebPoly_halfDegree_coeff_le (D : ℕ) (hD : Even D) (hD2 : 2 ≤ D) (k : ℕ) :
    |(absChebPoly (D / 2)).coeff k| ≤ (2 : ℝ) ^ ((3 : ℝ) * (D : ℝ) / 2) := by
  rw [← coefficientConstant_eq_rpow D hD]
  exact absChebPoly_coeff_le (D / 2) (halfDegree_pos D hD2) k

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue

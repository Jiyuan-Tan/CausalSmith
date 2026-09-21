module
public import CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability.Coefficient
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Certified finite Taylor approximation for Gaussian moment recovery

This module defines the polynomial truncation of `r² exp (r²)`, proves its
degree, and bounds its factorial-series remainder uniformly on `[0,5]`.
-/

@[expose] public section

open Set
open scoped BigOperators Polynomial

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability

/-- The polynomial consisting of the first `N + 1` terms of the power series
for `r² exp (r²)`, namely the terms `r^(2k+2) / k!` for `0 ≤ k ≤ N`. -/
def secondMomentTaylorPolynomial (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.monomial (2 * k + 2) (1 / (k.factorial : ℝ))

/-- Evaluating the recovery polynomial gives the corresponding finite sum of
even powers. -/
theorem secondMomentTaylorPolynomial_eval (N : ℕ) (r : ℝ) :
    (secondMomentTaylorPolynomial N).eval r =
      ∑ k ∈ Finset.range (N + 1), r ^ (2 * k + 2) / (k.factorial : ℝ) := by
  rw [secondMomentTaylorPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_monomial]
  ring

/-- The truncation with indices zero through one hundred has polynomial degree
exactly `202`. -/
theorem secondMomentTaylorPolynomial_natDegree_oneHundred :
    (secondMomentTaylorPolynomial 100).natDegree = 202 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    rw [Polynomial.natDegree_monomial]
    split_ifs
    · omega
    · have hk' : k < 101 := Finset.mem_range.mp hk
      omega
  · set_option maxRecDepth 10000 in
    rw [secondMomentTaylorPolynomial]
    -- The public coefficient API avoids unfolding Mathlib's opaque polynomial addition instance.
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single 100]
    · norm_num
    · intro b hb hne
      split_ifs with h
      · omega
      · rfl
    · simp

private lemma factorial_mul_pow_le_factorial_add (N j : ℕ) :
    (N + 1).factorial * (N + 2) ^ j ≤ (N + 1 + j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        (N + 1).factorial * (N + 2) ^ (j + 1) =
            ((N + 1).factorial * (N + 2) ^ j) * (N + 2) := by
              simp [pow_succ, Nat.mul_assoc]
        _ ≤ (N + 1 + j).factorial * (N + 1 + j + 1) :=
          Nat.mul_le_mul ih (by omega)
        _ = (N + 1 + (j + 1)).factorial := by
          conv_rhs =>
            rw [show N + 1 + (j + 1) = (N + 1 + j) + 1 by omega,
              Nat.factorial_succ]
          ac_rfl

/-- Once the first omitted exponential-series denominator exceeds `x`, the
tail after index `N` is bounded by its first term times the indicated geometric
factor. -/
theorem exp_series_tail_le_geometric
    (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hden : x < N + 2) :
    Real.exp x - ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ) ≤
      (x ^ (N + 1) / ((N + 1).factorial : ℝ)) *
        ((N + 2 : ℝ) / ((N + 2 : ℝ) - x)) := by
  let f : ℕ → ℝ := fun k => x ^ k / (k.factorial : ℝ)
  have hf : Summable f := by
    simpa [f] using NormedSpace.expSeries_div_summable x
  have hsplit := hf.sum_add_tsum_nat_add (N + 1)
  have hexp : Real.exp x = ∑' k, f k := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [f] using (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq.symm
  have htail :
      Real.exp x - ∑ k ∈ Finset.range (N + 1),
          x ^ k / (k.factorial : ℝ) =
        ∑' j : ℕ, f (j + (N + 1)) := by
    rw [hexp]
    change (∑' k, f k) - ∑ k ∈ Finset.range (N + 1), f k = _
    linarith
  rw [htail]
  let a : ℝ := x ^ (N + 1) / ((N + 1).factorial : ℝ)
  let q : ℝ := x / (N + 2 : ℝ)
  have hq : |q| < 1 := by
    rw [abs_of_nonneg (div_nonneg hx (by positivity))]
    exact (div_lt_one (by positivity)).2 hden
  have hfshift : Summable (fun j : ℕ => f (j + (N + 1))) := by
    exact hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hg : Summable (fun j : ℕ => a * q ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs] using hq)).mul_left a
  calc
    (∑' j : ℕ, f (j + (N + 1))) ≤ ∑' j : ℕ, a * q ^ j := by
      apply Summable.tsum_le_tsum _ hfshift hg
      intro j
      dsimp [f, a, q]
      have hfac : ((N + 1).factorial : ℝ) * (N + 2 : ℝ) ^ j ≤
          ((N + 1 + j).factorial : ℝ) := by
        exact_mod_cast factorial_mul_pow_le_factorial_add N j
      have hpos : 0 < ((N + 1).factorial : ℝ) * (N + 2 : ℝ) ^ j := by
        positivity
      have hnum : 0 ≤ x ^ (N + 1 + j) := by positivity
      rw [show j + (N + 1) = N + 1 + j by omega]
      calc
        x ^ (N + 1 + j) / ((N + 1 + j).factorial : ℝ) ≤
            x ^ (N + 1 + j) /
              (((N + 1).factorial : ℝ) * (N + 2 : ℝ) ^ j) :=
          div_le_div_of_nonneg_left hnum hpos hfac
        _ = (x ^ (N + 1) / ((N + 1).factorial : ℝ)) *
              (x / (N + 2 : ℝ)) ^ j := by
          rw [div_pow, pow_add]
          field_simp
    _ = a * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hq]
    _ = (x ^ (N + 1) / ((N + 1).factorial : ℝ)) *
        ((N + 2 : ℝ) / ((N + 2 : ℝ) - x)) := by
      dsimp [a, q]
      have hn : (N + 2 : ℝ) ≠ 0 := by positivity
      have hd : (N + 2 : ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hden)
      field_simp

/-- On `[0,5]`, the degree-202 polynomial approximates `r² exp (r²)` with
uniform error at most the explicit factorial-tail certificate. -/
theorem abs_secondMoment_exp_sub_taylor_oneHundred_le
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 5) :
    |r ^ 2 * Real.exp (r ^ 2) -
        (secondMomentTaylorPolynomial 100).eval r| ≤
      25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) := by
  have hr0 : 0 ≤ r := hr.1
  have hr5 : r ≤ 5 := hr.2
  have hx0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx25 : r ^ 2 ≤ 25 := by nlinarith
  rw [secondMomentTaylorPolynomial_eval]
  have hsum :
      ∑ k ∈ Finset.range 101, r ^ (2 * k + 2) / (k.factorial : ℝ) =
        r ^ 2 * ∑ k ∈ Finset.range 101,
          (r ^ 2) ^ k / (k.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add, pow_mul]
    ring
  rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg hx0,
    abs_of_nonneg (sub_nonneg.mpr (Real.sum_le_exp_of_nonneg hx0 101))]
  have htail := exp_series_tail_le_geometric 100 (r ^ 2) hx0 (by
    norm_num
    linarith)
  have htail' :
      Real.exp (r ^ 2) -
          ∑ k ∈ Finset.range 101, (r ^ 2) ^ k / (k.factorial : ℝ) ≤
        (r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) *
          (102 / (102 - r ^ 2)) := by
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_add] at htail
    exact htail
  calc
    r ^ 2 * (Real.exp (r ^ 2) -
        ∑ k ∈ Finset.range 101, (r ^ 2) ^ k / (k.factorial : ℝ)) ≤
        r ^ 2 * ((r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) *
          (102 / (102 - r ^ 2))) :=
      mul_le_mul_of_nonneg_left htail' hx0
    _ ≤ 25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) := by
      have hratio : (102 : ℝ) / (102 - r ^ 2) ≤ 102 / 77 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
      have hpow : (r ^ 2) ^ 101 ≤ (25 : ℝ) ^ 101 := by
        exact pow_le_pow_left₀ hx0 hx25 101
      have hdiv :
          (r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) ≤
            25 ^ 101 / ((101 : ℕ).factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      have hfacpos : (0 : ℝ) < ((101 : ℕ).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos 101
      have hdiv0 :
          0 ≤ (r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) :=
        div_nonneg (pow_nonneg hx0 101) hfacpos.le
      have hdiv25 :
          0 ≤ (25 : ℝ) ^ 101 / ((101 : ℕ).factorial : ℝ) :=
        div_nonneg (pow_nonneg (by norm_num) 101) hfacpos.le
      have hratio0 : 0 ≤ (102 : ℝ) / (102 - r ^ 2) :=
        div_nonneg (by norm_num) (by nlinarith)
      calc
        r ^ 2 * ((r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) *
            (102 / (102 - r ^ 2))) ≤
            25 * ((r ^ 2) ^ 101 / ((101 : ℕ).factorial : ℝ) *
              (102 / (102 - r ^ 2))) :=
          mul_le_mul_of_nonneg_right hx25 (mul_nonneg hdiv0 hratio0)
        _ ≤ 25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ) *
              (102 / (102 - r ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hdiv hratio0) (by norm_num)
        _ ≤ 25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ) * (102 / 77)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hratio hdiv25) (by norm_num)
        _ = 25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) := by
          ring

/-- Multiplication by the reciprocal Gaussian weight converts the degree-202
Taylor approximation into a uniform approximation of the raw square on
`[0,5]`, with the same certified error. -/
theorem abs_sq_sub_gaussianWeightedTaylor_oneHundred_le
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 5) :
    |r ^ 2 - Real.exp (-r ^ 2) *
        (secondMomentTaylorPolynomial 100).eval r| ≤
      25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) := by
  have hx0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hprev := abs_secondMoment_exp_sub_taylor_oneHundred_le hr
  have hexp : Real.exp (-r ^ 2) * Real.exp (r ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hid :
      r ^ 2 - Real.exp (-r ^ 2) *
          (secondMomentTaylorPolynomial 100).eval r =
        Real.exp (-r ^ 2) *
          (r ^ 2 * Real.exp (r ^ 2) -
            (secondMomentTaylorPolynomial 100).eval r) := by
    calc
      r ^ 2 - Real.exp (-r ^ 2) *
          (secondMomentTaylorPolynomial 100).eval r =
          (Real.exp (-r ^ 2) * Real.exp (r ^ 2)) * r ^ 2 -
            Real.exp (-r ^ 2) *
              (secondMomentTaylorPolynomial 100).eval r := by rw [hexp]; ring
      _ = _ := by ring
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-r ^ 2) *
        |r ^ 2 * Real.exp (r ^ 2) -
          (secondMomentTaylorPolynomial 100).eval r| ≤
        1 * |r ^ 2 * Real.exp (r ^ 2) -
          (secondMomentTaylorPolynomial 100).eval r| :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (by linarith)) (abs_nonneg _)
    _ ≤ 25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) := by
      simpa using hprev

/-- Twice the uniform degree-202 approximation error, accounting for two
probability laws, is at most the rational remainder `10⁻¹⁵`. -/
theorem two_taylorRemainder_oneHundred_le :
    2 * (25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77)) ≤
      (1 / 10 ^ 15 : ℝ) := by
  norm_num [Nat.factorial]

end CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability

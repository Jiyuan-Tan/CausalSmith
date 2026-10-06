module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedLagrange
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor

/-!
# Fixed tensor interpolation grid

The tensor product of the equispaced one-variable Lagrange formulas recovers every coefficient
of a bounded coordinatewise degree polynomial from values at one fixed grid. The total absolute
weight is controlled by the corresponding one-variable bound.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A tensor-grid index](hyp:b) determines [the corresponding point in the unit cube](goal).

The tensor grid point indexed by `b`, with each coordinate in the unit interval.
-/
def tensorGridPoint {d D : ℕ} (b : Fin d → Fin (D + 1)) : Fin d → ℝ :=
  fun i => equispacedLagrangeNode D (b i)

/-- [a target coefficient index and a tensor-grid index](hyp:a,b) determine [the corresponding tensor interpolation weight](goal).

The tensor interpolation weight from grid point `b` to monomial coefficient `a`.
-/
def tensorGridWeight {d D : ℕ} (a b : Fin d → Fin (D + 1)) : ℝ :=
  ∏ i : Fin d, equispacedLagrangeWeight D (a i) (b i)

/-- Every fixed tensor interpolation node lies in the normalized cube. -/
theorem tensorGridPoint_mem_cube {d D : ℕ} (b : Fin d → Fin (D + 1)) :
    tensorGridPoint b ∈ normalizedCube d := by
  intro i
  change -1 ≤ (b i : ℝ) / (D + 1) ∧
    (b i : ℝ) / (D + 1) ≤ 1
  have hD : (0 : ℝ) < D + 1 := by positivity
  have hb : (b i : ℝ) ≤ D := by exact_mod_cast Nat.le_of_lt_succ (b i).isLt
  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith [show (0 : ℝ) ≤ (b i : ℝ) by positivity]
  · apply (div_le_iff₀ hD).2
    nlinarith

/-- [A multivariate polynomial](hyp:p), [a coordinatewise degree bound](hyp:hdeg), and [a monomial index](hyp:a) give [an exact recovery of that coefficient from fixed tensor-grid evaluations](goal).

A coordinatewise degree at most `D` tensor polynomial has each monomial coefficient equal
to the fixed weighted sum of its tensor-grid evaluations.

Expand in the fixed tensor monomial basis. Apply `equispacedLagrange_coeff_recovery` to each
coordinate of a monomial, then factor the grid sum with `Fintype.prod_sum`. The empty product
also handles the zero-dimensional case.
-/
theorem tensorGrid_coeff_recovery {d D : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ D) (a : Fin d → Fin (D + 1)) :
    tensorCoeffs (D := D) p a =
      ∑ b : Fin d → Fin (D + 1),
        tensorGridWeight a b * MvPolynomial.eval (tensorGridPoint b) p := by
  classical
  have hone (k m : Fin (D + 1)) :
      (∑ j : Fin (D + 1),
        equispacedLagrangeWeight D k j * equispacedLagrangeNode D j ^ (m : ℕ)) =
        if k = m then 1 else 0 := by
    have hm : (Polynomial.X ^ (m : ℕ) : Polynomial ℝ).natDegree ≤ D := by
      simpa using Nat.le_of_lt_succ m.isLt
    have h := equispacedLagrange_coeff_recovery D
      (Polynomial.X ^ (m : ℕ) : Polynomial ℝ) hm k
    simpa only [Polynomial.coeff_X_pow, Polynomial.eval_pow, Polynomial.eval_X,
      Fin.ext_iff] using h.symm
  have hmonomial (c : Fin d → Fin (D + 1)) :
      (∑ b : Fin d → Fin (D + 1), tensorGridWeight a b *
        MvPolynomial.eval (tensorGridPoint b)
          (MvPolynomial.monomial (tensorExponent c) (1 : ℝ))) =
        if a = c then 1 else 0 := by
    simp_rw [MvPolynomial.eval_monomial, one_mul,
      Finsupp.prod_pow, tensorGridWeight]
    have hpow (b : Fin d → Fin (D + 1)) :
        (∏ i : Fin d, tensorGridPoint b i ^ tensorExponent c i) =
          ∏ i : Fin d, equispacedLagrangeNode D (b i) ^ (c i : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    simp_rw [hpow, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i : Fin d =>
      fun j : Fin (D + 1) =>
        equispacedLagrangeWeight D (a i) j *
          equispacedLagrangeNode D j ^ (c i : ℕ))]
    simp_rw [hone]
    by_cases h : a = c
    · subst c
      simp
    · have hi : ∃ i : Fin d, a i ≠ c i := by
        by_contra hn
        push Not at hn
        exact h (funext hn)
      obtain ⟨i, hi⟩ := hi
      simp only [if_neg h]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp only [MvPolynomial.eval_monomial, one_mul] at hmonomial
  conv_rhs => rw [← tensorPolynomial_tensorCoeffs p hdeg]
  simp only [tensorPolynomial, MvPolynomial.eval_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [MvPolynomial.eval_monomial]
  have hswap (c : Fin d → Fin (D + 1)) :
      (∑ b : Fin d → Fin (D + 1), tensorGridWeight a b *
        (tensorCoeffs p c * (tensorExponent c).prod
          fun n e => tensorGridPoint b n ^ e)) =
        tensorCoeffs p c * (if a = c then 1 else 0) := by
    rw [← hmonomial c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hswap]
  simp

/-- The total absolute tensor interpolation weight is at most the `d`th power of the
one-variable exponential bound `2^(4D+4)`.

Rewrite the double sum of absolute products as a product of one-dimensional double sums, then
apply `equispacedLagrange_weight_oneNorm` coordinatewise. The bound also covers `d = 0`.
-/
theorem tensorGrid_weight_oneNorm_le (d D : ℕ) :
    (∑ a : Fin d → Fin (D + 1),
      ∑ b : Fin d → Fin (D + 1), |tensorGridWeight a b|) ≤
        ((2 : ℝ) ^ (4 * D + 4)) ^ d := by
  classical
  have hsum :
      (∑ a : Fin d → Fin (D + 1),
        ∑ b : Fin d → Fin (D + 1), |tensorGridWeight a b|) =
        ∏ i : Fin d, ∑ k : Fin (D + 1), ∑ j : Fin (D + 1),
          |equispacedLagrangeWeight D k j| := by
    simp_rw [tensorGridWeight, Finset.abs_prod]
    conv_lhs =>
      arg 2
      ext a
      rw [← Fintype.prod_sum (fun i : Fin d =>
        fun j : Fin (D + 1) => |equispacedLagrangeWeight D (a i) j|)]
    exact (Fintype.prod_sum (fun i : Fin d =>
      fun k : Fin (D + 1) => ∑ j : Fin (D + 1),
        |equispacedLagrangeWeight D k j|)).symm
  rw [hsum]
  calc
    (∏ i : Fin d, ∑ k : Fin (D + 1), ∑ j : Fin (D + 1),
        |equispacedLagrangeWeight D k j|) ≤
      ∏ _i : Fin d, (2 : ℝ) ^ (4 * D + 4) := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          exact equispacedLagrange_weight_oneNorm D
    _ = ((2 : ℝ) ^ (4 * D + 4)) ^ d := by simp

end Causalean.Mathlib.Analysis.Approximation.Chebyshev


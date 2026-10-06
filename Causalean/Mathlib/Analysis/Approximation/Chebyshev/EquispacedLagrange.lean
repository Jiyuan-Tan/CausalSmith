module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedDistance
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Quantitative equispaced Lagrange interpolation

Coefficients of a degree-bounded real polynomial are recovered from a fixed grid in the unit
interval. The sum of the absolute recovery weights has an exponential degree bound. These
one-variable facts are the lower layer for tensor coefficient bounds.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A grid order and node index](hyp:D,j) determine [the corresponding equally spaced unit-interval node](goal).

The `j`th point of the equally spaced interpolation grid of order `D` in `[0,1]`.
-/
def equispacedLagrangeNode (D : ℕ) (j : Fin (D + 1)) : ℝ :=
  (j : ℝ) / (D + 1)

/-- [A grid order, coefficient index, and node index](hyp:D,k,j) determine [the fixed Lagrange coefficient-recovery weight](goal).

The weight that recovers monomial coefficient `k` from the value at equispaced grid point
`j`. It is the corresponding coefficient of the fixed Lagrange basis polynomial.
-/
def equispacedLagrangeWeight (D : ℕ) (k j : Fin (D + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (equispacedLagrangeNode D) j).coeff k

/-- The absolute product of distances from one equispaced node to all the other nodes is
`j! (D-j)! / (D+1)^D`.

Split the deleted grid into indices below and above `j`; each nonzero distance is a positive
integer divided by `D+1`. The two integer products are the indicated factorials. -/
theorem equispacedLagrange_denominator_abs (D : ℕ) (j : Fin (D + 1)) :
    |∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
      (equispacedLagrangeNode D j - equispacedLagrangeNode D i)| =
      (((j : ℕ).factorial : ℝ) * ((D - (j : ℕ)).factorial : ℝ)) /
        (D + 1 : ℝ) ^ D := by
  have hden : (D + 1 : ℝ) ≠ 0 := by positivity
  have hcard : ((Finset.univ : Finset (Fin (D + 1))).erase j).card = D := by
    simp
  calc
    |∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
        (equispacedLagrangeNode D j - equispacedLagrangeNode D i)| =
        ∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
          |(j : ℝ) - (i : ℝ)| / (D + 1 : ℝ) := by
            rw [Finset.abs_prod]
            apply Finset.prod_congr rfl
            intro i _
            rw [equispacedLagrangeNode, equispacedLagrangeNode,
              ← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ D + 1)]
    _ = (∏ i ∈ (Finset.univ : Finset (Fin (D + 1))).erase j,
          |(j : ℝ) - (i : ℝ)|) / (D + 1 : ℝ) ^ D := by
            rw [Finset.prod_div_distrib, Finset.prod_const, hcard]
    _ = _ := by
      rw [equispacedDistance_erase_split,
        equispacedDistance_lower_factorial,
        equispacedDistance_upper_factorial]

/-- The sum of reciprocal factorial pairs over the equispaced grid equals `2^D / D!`.

Rewrite each summand using `D.choose j` and apply the binomial identity. -/
theorem equispacedLagrange_reciprocal_factorial_sum (D : ℕ) :
    (∑ j : Fin (D + 1),
      1 / (((j : ℕ).factorial : ℝ) * ((D - (j : ℕ)).factorial : ℝ))) =
        (2 : ℝ) ^ D / (D.factorial : ℝ) := by
  have hterm (k : ℕ) (hk : k ≤ D) :
      1 / ((k.factorial : ℝ) * ((D - k).factorial : ℝ)) =
        (D.choose k : ℝ) / (D.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hk
    have h' : (D.choose k : ℝ) * (k.factorial : ℝ) *
        ((D - k).factorial : ℝ) = (D.factorial : ℝ) := by exact_mod_cast h
    have hfac : (D.factorial : ℝ) ≠ 0 := by positivity
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hsubfac : ((D - k).factorial : ℝ) ≠ 0 := by positivity
    apply (div_eq_div_iff (mul_ne_zero hkfac hsubfac) hfac).2
    nlinarith [h']
  calc
    _ = ∑ k ∈ Finset.range (D + 1),
        1 / ((k.factorial : ℝ) * ((D - k).factorial : ℝ)) := by
          exact Fin.sum_univ_eq_sum_range
            (fun k : ℕ => (1 : ℝ) / ((k.factorial : ℝ) * ((D - k).factorial : ℝ))) (D + 1)
    _ = ∑ k ∈ Finset.range (D + 1),
        (D.choose k : ℝ) / (D.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast Nat.sum_range_choose D

/-- The factorial ratio from the equispaced grid grows at most exponentially in its degree.

An induction using `(D+2)^(D+1) / (D+1)!` and the classical bound
`(1+1/(D+1))^(D+1) ≤ 4` suffices; the case `D=0` is equality. -/
theorem equispacedLagrange_factorial_ratio_le (D : ℕ) :
    (D + 1 : ℝ) ^ D / (D.factorial : ℝ) ≤ (4 : ℝ) ^ D := by
  calc
    (D + 1 : ℝ) ^ D / (D.factorial : ℝ) ≤ ((2 * D).choose D : ℝ) := by
      have h : 2 * D + 1 - D = D + 1 := by omega
      simpa [h, Nat.cast_add] using (Nat.pow_le_choose (α := ℝ) D (2 * D))
    _ ≤ (2 : ℝ) ^ (2 * D) := by exact_mod_cast Nat.choose_le_two_pow (2 * D) D
    _ = (4 : ℝ) ^ D := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]

/-- [A grid order and a real polynomial](hyp:D,p), [a bound on its degree](hyp:hp), and [a requested coefficient index](hyp:k) give [an exact fixed-grid recovery formula for that coefficient](goal).

Every coefficient of a real polynomial of degree at most `D` is a fixed weighted sum of its
values on the `D+1` equally spaced grid points in `[0,1]`.

Use injectivity of `equispacedLagrangeNode`, `Lagrange.eq_interpolate`, and the coefficient of
the finite basis expansion.
-/
theorem equispacedLagrange_coeff_recovery (D : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (k : Fin (D + 1)) :
    p.coeff k = ∑ j : Fin (D + 1),
      equispacedLagrangeWeight D k j * p.eval (equispacedLagrangeNode D j) := by
  have hnode : Function.Injective (equispacedLagrangeNode D) := by
    intro a b hab
    have hden : (D + 1 : ℝ) ≠ 0 := by positivity
    dsimp [equispacedLagrangeNode] at hab
    have hab' : (a : ℝ) = (b : ℝ) := by
      field_simp [hden] at hab
      exact hab
    exact Fin.ext (Nat.cast_injective hab')
  have hdeg : p.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_of_natDegree_le hp)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
  have hinterp := Lagrange.eq_interpolate (s := Finset.univ)
    (v := equispacedLagrangeNode D) hnode.injOn hdeg
  conv_lhs => rw [hinterp, Lagrange.interpolate_apply, finsetSum_coeff]
  simp only [coeff_C_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- At one equispaced node, the coefficient one-norm of the Lagrange basis polynomial is
bounded by the factorial denominator of its interpolation formula.

Expand `Lagrange.basis` into its `D` linear factors. The coefficient one-norm is
submultiplicative; each numerator factor has one-norm at most `2`, and the denominator is
`j! * (D-j)! / (D+1)^D`. -/
theorem equispacedLagrange_basis_oneNorm (D : ℕ) (j : Fin (D + 1)) :
    (∑ k : Fin (D + 1), |equispacedLagrangeWeight D k j|) ≤
      (2 : ℝ) ^ D * (D + 1 : ℝ) ^ D /
        (((j : ℕ).factorial : ℝ) * ((D - (j : ℕ)).factorial : ℝ)) := by
  classical
  let s := (Finset.univ : Finset (Fin (D + 1))).erase j
  let v := equispacedLagrangeNode D
  have hscale (c : ℝ) (p : Polynomial ℝ) :
      polynomialCoeffOneNorm (C c * p) = |c| * polynomialCoeffOneNorm p := by
    rw [Polynomial.C_mul']
    have hp : p.natDegree < p.natDegree + 1 := Nat.lt_succ_self _
    have hcp : (c • p).natDegree < p.natDegree + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) hp
    change Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1 (c • p) = _
    rw [show Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1 (c • p) =
        ∑ k ∈ Finset.range (p.natDegree + 1), |(c • p).coeff k| from
        (c • p).sum_over_range' (fun _ => abs_zero) _ hcp,
      show polynomialCoeffOneNorm p =
        ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k| from
        p.sum_over_range' (fun _ => abs_zero) _ hp]
    simp only [Polynomial.coeff_smul, smul_eq_mul, abs_mul, Finset.mul_sum]
  have hnonneg (p : Polynomial ℝ) : 0 ≤ polynomialCoeffOneNorm p := by
    change 0 ≤ p.sum (fun _ c => |c|)
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnode (i : Fin (D + 1)) : 0 ≤ v i ∧ v i ≤ 1 := by
    have hi : (i : ℕ) ≤ D := Nat.lt_succ_iff.mp i.isLt
    have hi' : (i : ℝ) ≤ (D : ℝ) := by exact_mod_cast hi
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < D + 1)).2
      linarith
  have hfactor (i : Fin (D + 1)) :
      polynomialCoeffOneNorm (Lagrange.basisDivisor (v j) (v i)) ≤
        2 * |v j - v i|⁻¹ := by
    rw [Lagrange.basisDivisor, hscale, abs_inv]
    calc
      |v j - v i|⁻¹ * polynomialCoeffOneNorm (X - C (v i)) ≤
          |v j - v i|⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left
          (polynomialCoeffOneNorm_X_sub_C_le_two (v i) (hnode i).1 (hnode i).2)
          (by positivity)
      _ = _ := by ring
  have hprod (t : Finset (Fin (D + 1))) :
      polynomialCoeffOneNorm (∏ i ∈ t, Lagrange.basisDivisor (v j) (v i)) ≤
        ∏ i ∈ t, (2 * |v j - v i|⁻¹) := by
    induction t using Finset.induction_on with
    | empty =>
        change polynomialCoeffOneNorm (1 : Polynomial ℝ) ≤ 1
        rw [show polynomialCoeffOneNorm (1 : Polynomial ℝ) =
            ∑ k ∈ Finset.range 1, |(1 : Polynomial ℝ).coeff k| from
            (1 : Polynomial ℝ).sum_over_range' (fun _ => abs_zero) 1 (by simp)]
        simp
    | @insert i t hi ih =>
        simp only [Finset.prod_insert hi]
        calc
          polynomialCoeffOneNorm
              (Lagrange.basisDivisor (v j) (v i) *
                ∏ k ∈ t, Lagrange.basisDivisor (v j) (v k)) ≤
              polynomialCoeffOneNorm (Lagrange.basisDivisor (v j) (v i)) *
                polynomialCoeffOneNorm
                  (∏ k ∈ t, Lagrange.basisDivisor (v j) (v k)) :=
            polynomialCoeffOneNorm_mul_le _ _
          _ ≤ (2 * |v j - v i|⁻¹) *
                (∏ k ∈ t, (2 * |v j - v k|⁻¹)) :=
            mul_le_mul (hfactor i) ih (hnonneg _)
              (by positivity)
  have hinj : Function.Injective v := by
    intro a b hab
    have hden : (D + 1 : ℝ) ≠ 0 := by positivity
    dsimp [v, equispacedLagrangeNode] at hab
    have hab' : (a : ℝ) = (b : ℝ) := by
      field_simp [hden] at hab
      exact hab
    exact Fin.ext (Nat.cast_injective hab')
  have hdeg : (Lagrange.basis Finset.univ v j).natDegree < D + 1 := by
    rw [Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ j)]
    simp
  have hsum : (∑ k : Fin (D + 1), |equispacedLagrangeWeight D k j|) =
      polynomialCoeffOneNorm (Lagrange.basis Finset.univ v j) := by
    rw [show polynomialCoeffOneNorm (Lagrange.basis Finset.univ v j) =
        ∑ k ∈ Finset.range (D + 1),
          |(Lagrange.basis Finset.univ v j).coeff k| from
        (Lagrange.basis Finset.univ v j).sum_over_range' (fun _ => abs_zero) _ hdeg]
    simpa only [equispacedLagrangeWeight, v] using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ => |(Lagrange.basis Finset.univ v j).coeff k|) (D + 1))
  rw [hsum]
  change polynomialCoeffOneNorm (∏ i ∈ s, Lagrange.basisDivisor (v j) (v i)) ≤ _
  calc
    polynomialCoeffOneNorm (∏ i ∈ s, Lagrange.basisDivisor (v j) (v i)) ≤
        ∏ i ∈ s, (2 * |v j - v i|⁻¹) := hprod s
    _ = (2 : ℝ) ^ D / |∏ i ∈ s, (v j - v i)| := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hs : s.card = D := by simp [s]
      rw [hs, Finset.prod_inv_distrib, ← Finset.abs_prod, div_eq_mul_inv]
    _ = _ := by
      rw [equispacedLagrange_denominator_abs]
      have hfac : (((j : ℕ).factorial : ℝ) *
          ((D - (j : ℕ)).factorial : ℝ)) ≠ 0 := by positivity
      have hden : (D + 1 : ℝ) ≠ 0 := by positivity
      field_simp

/-- The sum of the absolute values of all equispaced coefficient-recovery weights is at most
`2^(4D+4)`.

Sum `equispacedLagrange_basis_oneNorm` over `j` using the binomial identity, then bound
`(D+1)^D / D!` by `4^D`. The four spare powers absorb the small-degree endpoints. -/
theorem equispacedLagrange_weight_oneNorm (D : ℕ) :
    (∑ k : Fin (D + 1), ∑ j : Fin (D + 1),
      |equispacedLagrangeWeight D k j|) ≤ (2 : ℝ) ^ (4 * D + 4) := by
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin (D + 1), ∑ k : Fin (D + 1),
        |equispacedLagrangeWeight D k j|) ≤
        ∑ j : Fin (D + 1),
          (2 : ℝ) ^ D * (D + 1 : ℝ) ^ D /
            (((j : ℕ).factorial : ℝ) * ((D - (j : ℕ)).factorial : ℝ)) := by
          exact Finset.sum_le_sum (fun j _ => equispacedLagrange_basis_oneNorm D j)
    _ = (2 : ℝ) ^ D * (D + 1 : ℝ) ^ D *
          (∑ j : Fin (D + 1),
            1 / (((j : ℕ).factorial : ℝ) * ((D - (j : ℕ)).factorial : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (2 : ℝ) ^ D * (D + 1 : ℝ) ^ D *
          ((2 : ℝ) ^ D / (D.factorial : ℝ)) := by
          rw [equispacedLagrange_reciprocal_factorial_sum]
    _ = (4 : ℝ) ^ D * ((D + 1 : ℝ) ^ D / (D.factorial : ℝ)) := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
          ring
    _ ≤ (4 : ℝ) ^ D * (4 : ℝ) ^ D := by
          exact mul_le_mul_of_nonneg_left
            (equispacedLagrange_factorial_ratio_le D) (by positivity)
    _ ≤ (2 : ℝ) ^ (4 * D + 4) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          omega

end Causalean.Mathlib.Analysis.Approximation.Chebyshev


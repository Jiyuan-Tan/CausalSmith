module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ChebyshevAlgebra
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm

/-!
Coefficient bounds for the two Chebyshev continuation polynomials, using the shifted
Chebyshev recurrence and invariance of the coefficient norm under multiplication by X.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open Polynomial Causalean.Mathlib.Analysis.Approximation.Chebyshev
open scoped BigOperators

/-- [Under the stated inputs and conditions](hyp:c,p), Scalar multiplication scales the sum of absolute polynomial coefficients.  This gives [the stated result](goal).-/
-- @node: continuation_coeffNorm_smul
lemma continuation_coeffNorm_smul (c : Real) (p : Polynomial Real) :
    polynomialCoeffOneNorm (c • p) = |c| * polynomialCoeffOneNorm p := by
  rw [polynomialCoeffOneNorm_range (c • p)
      (lt_of_le_of_lt (natDegree_smul_le _ _) (Nat.lt_succ_self _)),
    polynomialCoeffOneNorm_range p (Nat.lt_succ_self _)]
  simp only [coeff_smul, smul_eq_mul, abs_mul, Finset.mul_sum]

/-- [Under the stated inputs and conditions](hyp:p), Multiplication by the variable shifts coefficients and preserves their absolute sum.  This gives [the stated result](goal).-/
-- @node: continuation_coeffNorm_X_mul
lemma continuation_coeffNorm_X_mul (p : Polynomial Real) :
    polynomialCoeffOneNorm (X * p) = polynomialCoeffOneNorm p := by
  by_cases hp : p = 0
  · simp [hp, polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [polynomialCoeffOneNorm_range (X * p) (m := p.natDegree + 2)
        (by rw [natDegree_X_mul hp]; omega),
      polynomialCoeffOneNorm_range p (Nat.lt_succ_self _)]
    rw [show p.natDegree + 2 = (p.natDegree + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp only [coeff_X_mul_zero, abs_zero, add_zero, Nat.succ_eq_add_one, coeff_X_mul]

/-- [Under the stated inputs and conditions](hyp:L,hL), The first continuation inherits the shifted Chebyshev coefficient bound after division.  This gives [the stated result](goal).-/
-- @node: chebE_coeffNorm_le
lemma chebE_coeffNorm_le (L : Nat) (hL : 0 < L) :
    polynomialCoeffOneNorm (chebE L) ≤ (7 : Real) ^ L := by
  have hLp : (1 : Real) ≤ L := by exact_mod_cast hL
  have hden : 0 < 2 * (L : Real) ^ 2 := by positivity
  have hnorm := congrArg polynomialCoeffOneNorm (chebE_mul_X L)
  rw [continuation_coeffNorm_X_mul, continuation_coeffNorm_smul,
    abs_of_pos (inv_pos.mpr hden)] at hnorm
  have hone : polynomialCoeffOneNorm (1 : Polynomial Real) = 1 := by
    rw [polynomialCoeffOneNorm_range _ (m := 1) (by simp)]
    simp
  have hshift : polynomialCoeffOneNorm
      ((Polynomial.Chebyshev.T Real L).comp (1 - 2 * X)) ≤ (7 : Real) ^ L := by
    simpa [shiftedCheb, Polynomial.C_ofNat] using shiftedCheb_coeffL1_le L
  have hnum := (polynomialCoeffOneNorm_sub_le 1
    ((Polynomial.Chebyshev.T Real L).comp (1 - 2 * X))).trans
      (add_le_add (le_of_eq hone) hshift)
  have hseven : (1 : Real) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [hnorm]
  apply (inv_mul_le_iff₀ hden).2
  nlinarith [sq_nonneg ((L : Real) - 1)]

/-- [Under the stated inputs and conditions](hyp:L,hL), The second removable division gives the coefficient sum required by the certificate.  This gives [the stated result](goal).-/
-- @node: chebG_coeff_sum_le
lemma chebG_coeff_sum_le (L : Nat) (hL : 2 ≤ L) :
    (∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h|) ≤ (14 : Real) ^ L := by
  have hLp : 0 < L := by omega
  rw [← polynomialCoeffOneNorm_range (chebG L)
    (lt_of_le_of_lt (chebG_natDegree_le L) (by omega : L - 2 < L - 1))]
  have hnorm := congrArg polynomialCoeffOneNorm (chebG_mul_X L hLp)
  rw [continuation_coeffNorm_X_mul] at hnorm
  have hone : polynomialCoeffOneNorm (1 : Polynomial Real) = 1 := by
    rw [polynomialCoeffOneNorm_range _ (m := 1) (by simp)]
    simp
  have hseven : (1 : Real) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  have htwo : (2 : Real) ≤ 2 ^ L := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2)
      (show 1 ≤ L by omega)
  calc
    polynomialCoeffOneNorm (chebG L) = polynomialCoeffOneNorm (1 - chebE L) := hnorm
    _ ≤ polynomialCoeffOneNorm (1 : Polynomial Real) +
        polynomialCoeffOneNorm (chebE L) := polynomialCoeffOneNorm_sub_le _ _
    _ ≤ 1 + (7 : Real) ^ L := by rw [hone]; exact add_le_add (le_refl 1) (chebE_coeffNorm_le L hLp)
    _ ≤ 2 * (7 : Real) ^ L := by linarith
    _ ≤ (2 : Real) ^ L * 7 ^ L := mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = (14 : Real) ^ L := by rw [← mul_pow]; norm_num

end CausalSmith.Stat.AnnotationRarearmFrontier

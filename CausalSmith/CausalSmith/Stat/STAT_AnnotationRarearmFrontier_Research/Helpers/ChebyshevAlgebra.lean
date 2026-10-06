module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Estimator
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
Algebraic degree bounds and removable-value identities for the Chebyshev continuations.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open scoped BigOperators

/-- [Under the stated inputs and conditions](hyp:L), Division by the variable removes the zero constant coefficient of the first numerator.  This gives [the stated result](goal).-/
-- @node: chebE_mul_X
lemma chebE_mul_X (L : Nat) :
    Polynomial.X * chebE L = (2 * (L : Real) ^ 2)⁻¹ •
      (1 - (Polynomial.Chebyshev.T Real L).comp (1 - 2 * Polynomial.X)) := by
  have h := Polynomial.modByMonic_add_div
    ((2 * (L : Real) ^ 2)⁻¹ •
      (1 - (Polynomial.Chebyshev.T Real L).comp (1 - 2 * Polynomial.X))) Polynomial.X
  simpa [Polynomial.modByMonic_X, Polynomial.eval_comp,
    Polynomial.Chebyshev.T_eval_one, chebE] using h

/-- [Under the stated inputs and conditions](hyp:L,hL), The removable value of the first continuation is the normalized endpoint derivative.  This gives [the stated result](goal).-/
-- @node: chebE_eval_zero
lemma chebE_eval_zero (L : Nat) (hL : 0 < L) : (chebE L).eval 0 = 1 := by
  have h := congrArg (fun p : Polynomial Real => p.derivative.eval 0) (chebE_mul_X L)
  simp [Polynomial.derivative_mul,
    Polynomial.derivative_comp, Polynomial.eval_comp,
    Polynomial.Chebyshev.derivative_T_eval_one] at h
  have hLn : (L : Real) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp at h
  nlinarith

/-- [Under the stated inputs and conditions](hyp:L,hL), The second numerator also has zero constant coefficient, so division is exact.  This gives [the stated result](goal).-/
-- @node: chebG_mul_X
lemma chebG_mul_X (L : Nat) (hL : 0 < L) :
    Polynomial.X * chebG L = 1 - chebE L := by
  have h := Polynomial.modByMonic_add_div (1 - chebE L) Polynomial.X
  simpa [Polynomial.modByMonic_X, chebE_eval_zero L hL, chebG] using h

/-- [Under the stated inputs and conditions](hyp:L,hL,z,hz), Both polynomial divisions realize the displayed removable rational expressions.  This gives [the stated result](goal).-/
-- @node: cheb_continuation_eval
lemma cheb_continuation_eval (L : Nat) (hL : 0 < L) (z : Real) (hz : z ≠ 0) :
    (chebE L).eval z = (1 - (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z)) /
      (2 * (L : Real) ^ 2 * z) ∧
    (chebG L).eval z = (1 - (chebE L).eval z) / z := by
  have hE := congrArg (Polynomial.eval z) (chebE_mul_X L)
  have hG := congrArg (Polynomial.eval z) (chebG_mul_X L hL)
  simp [Polynomial.eval_comp] at hE hG
  constructor
  · apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2
      (show (L : Real) ≠ 0 by exact_mod_cast hL.ne'))) hz)).2
    have hh := hE
    field_simp at hh
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  · apply (eq_div_iff hz).2
    nlinarith only [hG]

/-- [Under the stated inputs and conditions](hyp:L), Each exact division lowers the degree by one, giving the factorial truncation order.  This gives [the stated result](goal).-/
-- @node: chebG_natDegree_le
lemma chebG_natDegree_le (L : Nat) : (chebG L).natDegree ≤ L - 2 := by
  have hlin : (1 - 2 * (Polynomial.X : Polynomial Real)).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp
  have hcomp : ((Polynomial.Chebyshev.T Real L).comp
      (1 - 2 * Polynomial.X)).natDegree ≤ L := by
    apply Polynomial.natDegree_comp_le.trans
    simpa [Polynomial.Chebyshev.natDegree_T] using Nat.mul_le_mul_left L hlin
  have hnum : (1 - (Polynomial.Chebyshev.T Real L).comp
      (1 - 2 * Polynomial.X)).natDegree ≤ L := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simpa using hcomp)
  have hE : (chebE L).natDegree ≤ L - 1 := by
    unfold chebE
    rw [Polynomial.natDegree_divByMonic _ Polynomial.monic_X, Polynomial.natDegree_X]
    exact Nat.sub_le_sub_right ((Polynomial.natDegree_smul_le _ _).trans hnum) 1
  unfold chebG
  rw [Polynomial.natDegree_divByMonic _ Polynomial.monic_X, Polynomial.natDegree_X]
  have hsub : (1 - chebE L).natDegree ≤ L - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simpa using hE)
  have hh := Nat.sub_le_sub_right hsub 1
  omega

/-- [Under the stated inputs and conditions](hyp:L,z,hz,hz'), The Chebyshev numerator is nonnegative and bounded by both its range and endpoint slope.  This gives [the stated result](goal).-/
-- @node: cheb_numerator_bounds
lemma cheb_numerator_bounds (L : Nat) (z : Real) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    0 ≤ 1 - (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z) ∧
    1 - (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z) ≤ 2 ∧
    1 - (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z) ≤
      2 * (L : Real) ^ 2 * z := by
  let Q := Polynomial.Chebyshev.T Real L
  have hmem : 1 - 2 * z ∈ Set.Icc (-1 : Real) 1 := by
    constructor <;> linarith
  have hbound (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1) : |Q.eval x| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one L (abs_le.mpr hx)
  have hrange := abs_le.mp (hbound _ hmem)
  have hderiv (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1) :
      ‖Q.derivative.eval x‖ ≤ (L : Real) ^ 2 := by
    simpa only [Real.norm_eq_abs, mul_one] using
      MarkovPolynomial L Q 1 (by simp [Q, Polynomial.Chebyshev.natDegree_T]) hbound x hx
  have hdiff := (convex_Icc (-1 : Real) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => Q.hasDerivWithinAt x _) hderiv hmem
    (show (1 : Real) ∈ Set.Icc (-1 : Real) 1 by norm_num)
  have hone : Q.eval 1 = 1 := by simp [Q]
  rw [hone, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1 - (1 - 2 * z))] at hdiff
  refine ⟨by linarith, by linarith, ?_⟩
  have := (le_abs_self (1 - Q.eval (1 - 2 * z))).trans hdiff
  dsimp only [Q] at this
  nlinarith only [this]

/-- [Under the stated inputs and conditions](hyp:L,hL,z,hz,hz'), The first continuation lies between zero and the smaller of one and the inverse-scale bound.  This gives [the stated result](goal).-/
-- @node: chebE_approximation_bounds
lemma chebE_approximation_bounds (L : Nat) (hL : 0 < L) (z : Real)
    (hz : 0 < z) (hz' : z ≤ 1) :
    0 ≤ (chebE L).eval z ∧
      (chebE L).eval z ≤ min 1 ((L : Real) ^ 2 * z)⁻¹ := by
  obtain ⟨hzero, htwo, hslope⟩ := cheb_numerator_bounds L z hz.le hz'
  rw [(cheb_continuation_eval L hL z hz.ne').1]
  have hLp : 0 < (L : Real) := by exact_mod_cast hL
  have hden : 0 < 2 * (L : Real) ^ 2 * z := by positivity
  refine ⟨div_nonneg hzero hden.le, le_min ?_ ?_⟩
  · apply (div_le_iff₀ hden).2
    simpa only [one_mul] using hslope
  · apply (div_le_iff₀ hden).2
    have hid : ((L : Real) ^ 2 * z)⁻¹ * (2 * (L : Real) ^ 2 * z) = 2 := by
      field_simp
    rw [hid]
    exact htwo

end CausalSmith.Stat.AnnotationRarearmFrontier

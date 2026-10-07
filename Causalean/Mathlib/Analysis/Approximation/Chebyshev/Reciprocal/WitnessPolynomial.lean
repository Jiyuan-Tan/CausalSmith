module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.Parameters
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev polynomial witness for reciprocal approximation

The residual polynomial here is the one in Plonka and Tasche, Theorem 3.4.
Using the integer-indexed Chebyshev polynomial `T (-1) = T 1` makes its formula
valid at degree zero as well.  Dividing its normalized difference by `X`
produces an explicit polynomial approximant.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

open Polynomial

/-- The [interval endpoints](hyp:a,b) and [degree bound m](hyp:m) determine [the Chebyshev residual
polynomial](goal), given by [the Chebyshev polynomial of degree m + 1 divided by the interval's
decay parameter, minus twice the Chebyshev polynomial of degree m, plus the decay parameter times
the Chebyshev polynomial of degree m − 1](step:1); when m = 0 the last term uses index −1, which is
the Chebyshev polynomial of degree one. -/
noncomputable def reciprocalResidualPoly (a b : ℝ) (m : ℕ) : Polynomial ℝ :=
  C (intervalDecay a b)⁻¹ * Chebyshev.T ℝ ((m : ℤ) + 1) -
    C 2 * Chebyshev.T ℝ (m : ℤ) +
    C (intervalDecay a b) * Chebyshev.T ℝ ((m : ℤ) - 1)

/-- The [interval endpoints](hyp:a,b) and [degree bound m](hyp:m) determine [the explicit
reciprocal approximating polynomial](goal): [take the residual polynomial composed with the affine
map x ↦ v − 2x / (b − a), where v is the interval shape parameter, divide it by the residual
polynomial's value at v, subtract the result from one, and divide by x, discarding the constant
term](step:1). -/
noncomputable def reciprocalApproxPoly (a b : ℝ) (m : ℕ) : Polynomial ℝ :=
  (C 1 -
    C ((reciprocalResidualPoly a b m).eval (intervalShape a b))⁻¹ *
      (reciprocalResidualPoly a b m).comp
        (C (intervalShape a b) - C (2 / (b - a)) * X)).divX

/-- The [interval endpoints](hyp:a,b) and [degree bound](hyp:m) imply [that the
residual polynomial has degree at most one more than the bound](goal). -/
theorem reciprocalResidualPoly_degree_le (a b : ℝ) (m : ℕ) :
    (reciprocalResidualPoly a b m).natDegree ≤ m + 1 := by
  unfold reciprocalResidualPoly
  apply natDegree_add_le_of_degree_le
  · simpa using (natDegree_sub_le_of_le (m := m + 1) (n := m + 1)
      (p := C (intervalDecay a b)⁻¹ * Chebyshev.T ℝ ((m : ℤ) + 1))
      (q := C 2 * Chebyshev.T ℝ (m : ℤ)) (by
    · calc
        (C (intervalDecay a b)⁻¹ * Chebyshev.T ℝ ((m : ℤ) + 1)).natDegree ≤
            (Chebyshev.T ℝ ((m : ℤ) + 1)).natDegree := natDegree_C_mul_le _ _
        _ = m + 1 := by rw [Chebyshev.natDegree_T]; omega) (by
      calc
        (C 2 * Chebyshev.T ℝ (m : ℤ)).natDegree ≤
            (Chebyshev.T ℝ (m : ℤ)).natDegree := natDegree_C_mul_le _ _
        _ = m := by simp [Chebyshev.natDegree_T]
        _ ≤ m + 1 := by omega))
  · calc
      (C (intervalDecay a b) * Chebyshev.T ℝ ((m : ℤ) - 1)).natDegree ≤
          (Chebyshev.T ℝ ((m : ℤ) - 1)).natDegree := natDegree_C_mul_le _ _
      _ = ((m : ℤ) - 1).natAbs := Chebyshev.natDegree_T ℝ _
      _ ≤ m + 1 := by omega

private theorem reciprocalResidualPoly_recurrence (a b : ℝ) (m : ℕ) :
    reciprocalResidualPoly a b (m + 2) =
      2 * X * reciprocalResidualPoly a b (m + 1) -
        reciprocalResidualPoly a b m := by
  unfold reciprocalResidualPoly
  have h₁ := Chebyshev.T_add_two ℝ ((m : ℤ) + 1)
  have h₂ := Chebyshev.T_add_two ℝ (m : ℤ)
  have h₃ := Chebyshev.T_add_two ℝ ((m : ℤ) - 1)
  push_cast
  simp only [show (m : ℤ) + 2 + 1 = ((m : ℤ) + 1) + 2 by omega,
    show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 by omega,
    show (m : ℤ) + 2 - 1 = ((m : ℤ) - 1) + 2 by omega,
    h₁, h₂, h₃]
  ring_nf

/-- A [positive lower endpoint](hyp:a,ha), [strictly larger upper endpoint](hyp:b,hab), and [degree
bound m](hyp:m) imply [that the residual polynomial evaluated at the interval shape parameter v
equals 2 (v² − 1) divided by the m-th power of the decay parameter](goal). -/
theorem reciprocalResidualPoly_at_shape {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    (reciprocalResidualPoly a b m).eval (intervalShape a b) =
      2 * ((intervalShape a b) ^ 2 - 1) / intervalDecay a b ^ m := by
  let ρ := intervalDecay a b
  let v := intervalShape a b
  have hρ : ρ ≠ 0 := ne_of_gt (intervalDecay_mem_Ioo ha hab).1
  have hsum : ρ + ρ⁻¹ = 2 * v := intervalDecay_add_inv ha hab
  have hquad : ρ ^ 2 - 2 * v * ρ + 1 = 0 := by
    field_simp at hsum ⊢
    nlinarith
  change (reciprocalResidualPoly a b m).eval v = 2 * (v ^ 2 - 1) / ρ ^ m
  induction m using Nat.twoStepInduction with
  | zero =>
      simp only [reciprocalResidualPoly, Nat.cast_zero, zero_add, zero_sub,
        Chebyshev.T_zero, Chebyshev.T_one, Chebyshev.T_neg_one,
        eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, pow_zero, div_one]
      change ρ⁻¹ * v - 2 * 1 + ρ * v = 2 * (v ^ 2 - 1)
      field_simp [hρ] at hsum ⊢
      linear_combination v * hsum
  | one =>
      simp only [reciprocalResidualPoly, Nat.cast_one, one_add_one_eq_two,
        sub_self, Chebyshev.T_zero, Chebyshev.T_one, Chebyshev.T_two,
        eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one,
        eval_ofNat, pow_one]
      change ρ⁻¹ * (2 * v ^ 2 - 1) - 2 * v + ρ * 1 =
        2 * (v ^ 2 - 1) / ρ
      field_simp [hρ]
      linear_combination hquad
  | more n ih₀ ih₁ =>
      rw [reciprocalResidualPoly_recurrence]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, ih₀, ih₁]
      rw [← hsum]
      simp only [pow_succ]
      field_simp [hρ]
      ring

/-- For any two endpoints and any [degree bound](hyp:m), [the explicit
reciprocal approximant has degree at most that bound](goal). -/
theorem reciprocalApproxPoly_degree_le {a b : ℝ}
    (m : ℕ) :
    (reciprocalApproxPoly a b m).natDegree ≤ m := by
  let R := reciprocalResidualPoly a b m
  let Q := C (intervalShape a b) - C (2 / (b - a)) * X
  have hQ : Q.natDegree ≤ 1 := by
    apply (natDegree_sub_le_iff_left (n := 1)
      ((natDegree_C_mul_le (2 / (b - a)) X).trans natDegree_X_le)).2
    simp
  have hR : R.natDegree ≤ m + 1 := reciprocalResidualPoly_degree_le a b m
  have hnum : (C 1 - C (R.eval (intervalShape a b))⁻¹ * R.comp Q).natDegree ≤
      m + 1 := by
    apply (natDegree_sub_le_iff_right (n := m + 1) (by simp)).2
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_comp_le).trans (by nlinarith))
  change (C 1 - C (R.eval (intervalShape a b))⁻¹ * R.comp Q).divX.natDegree ≤ m
  rw [natDegree_divX_eq_natDegree_tsub_one]
  omega

/-- [Positive interval endpoints](hyp:a,b,ha,hab), a [nonzero evaluation
point](hyp:z,hz), and a [degree bound](hyp:m) imply [the shifted-residual
identity for the explicit reciprocal approximant](goal). -/
theorem reciprocalApproxPoly_residual {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : z ≠ 0) (m : ℕ) :
    z⁻¹ - (reciprocalApproxPoly a b m).eval z =
      (reciprocalResidualPoly a b m).eval
        (intervalShape a b - 2 * z / (b - a)) /
        (z * (reciprocalResidualPoly a b m).eval (intervalShape a b)) := by
  let v := intervalShape a b
  let R := reciprocalResidualPoly a b m
  let Q : Polynomial ℝ := C v - C (2 / (b - a)) * X
  let P : Polynomial ℝ := C 1 - C (R.eval v)⁻¹ * R.comp Q
  have hv : 1 < v := intervalShape_gt_one ha hab
  have hρ : 0 < intervalDecay a b := (intervalDecay_mem_Ioo ha hab).1
  have hRv : R.eval v ≠ 0 := by
    change (reciprocalResidualPoly a b m).eval (intervalShape a b) ≠ 0
    rw [reciprocalResidualPoly_at_shape ha hab]
    have hsq : 0 < v ^ 2 - 1 := by nlinarith
    exact ne_of_gt (div_pos (by positivity) (pow_pos hρ m))
  have hQ0 : Q.eval 0 = v := by simp [Q]
  have hP0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [P, eval_sub, eval_mul, eval_C, eval_comp, hQ0]
    field_simp [hRv]
    ring
  have hP : X * P.divX = P := by
    have h := X_mul_divX_add P
    rwa [hP0, map_zero, add_zero] at h
  have hEval := congrArg (eval z) hP
  simp only [P, eval_mul, eval_X, eval_sub, eval_C, eval_comp] at hEval
  have hQz : Q.eval z = v - 2 * z / (b - a) := by
    simp [Q]
    ring
  rw [hQz] at hEval
  change z * P.divX.eval z =
    1 - (R.eval v)⁻¹ * R.eval (v - 2 * z / (b - a)) at hEval
  change z⁻¹ - P.divX.eval z = R.eval (v - 2 * z / (b - a)) / (z * R.eval v)
  field_simp [hz, hRv] at hEval ⊢
  linear_combination -hEval

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

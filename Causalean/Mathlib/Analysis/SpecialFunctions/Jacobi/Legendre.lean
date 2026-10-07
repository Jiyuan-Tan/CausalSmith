module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Beta
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Calculus

/-!
# Shifted Legendre identities on the unit interval

This module identifies the zero-parameter shifted Jacobi polynomial with
Mathlib's shifted Legendre polynomial and proves its Rodrigues formula,
endpoint vanishing, exact squared norm, and orthogonality on `[0,1]`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

/-- The [degree](hyp:n) and [evaluation point](hyp:x) give [equality between the normalized zero-parameter shifted Jacobi polynomial and Mathlib's shifted Legendre polynomial](goal). -/
lemma jacobiShifted_zero_zero_eq_shiftedLegendre (n : ℕ) (x : ℝ) :
    jacobiShifted n 0 0 x =
      Polynomial.aeval x (Polynomial.shiftedLegendre n) := by
  unfold jacobiShifted rising Polynomial.shiftedLegendre
  simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show (n : ℝ) + 0 + 0 + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
    show (0 : ℝ) + 1 = ((1 : ℕ) : ℝ) by norm_num,
    ascPochhammer_nat_eq_natCast_ascFactorial,
    ascPochhammer_nat_eq_natCast_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.one_ascFactorial]
  norm_cast
  field_simp
  rw [Nat.choose_symm_add (a := n) (b := m)]
  push_cast
  ring

/-- For an [integer polynomial](hyp:p) and [derivative order](hyp:n), [iterating the real derivative after evaluation agrees with evaluating the iterated polynomial derivative](goal). -/
lemma iter_deriv_aeval_int (p : Polynomial ℤ) (n : ℕ) :
    deriv^[n] (fun x : ℝ => Polynomial.aeval x p) =
      fun x : ℝ => Polynomial.aeval x (Polynomial.derivative^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext x
      exact Polynomial.deriv_aeval _

/-- The [degree](hyp:n) and [evaluation point](hyp:x) satisfy [the shifted-Legendre Rodrigues identity: n! times the shifted Legendre polynomial of degree n at x equals the n-th derivative of y^n·(1−y)^n at x](goal). -/
lemma shiftedLegendre_rodrigues_eval (n : ℕ) (x : ℝ) :
    (n.factorial : ℝ) * Polynomial.aeval x (Polynomial.shiftedLegendre n) =
      (deriv^[n] (fun y : ℝ => y^n * (1-y)^n)) x := by
  have h := congrArg (fun p : Polynomial ℤ => (Polynomial.aeval x p : ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  rw [map_mul] at h
  simp only [map_natCast] at h
  have hi := congrFun (iter_deriv_aeval_int
    (Polynomial.X^n * (1-Polynomial.X)^n : Polynomial ℤ) n) x
  have hfun : (fun y : ℝ => Polynomial.aeval y
      (Polynomial.X^n * (1-Polynomial.X)^n : Polynomial ℤ)) =
      (fun y : ℝ => y^n * (1-y)^n) := by
    funext y
    simp
  rw [hfun] at hi
  exact h.trans hi.symm

/-- For a [power](hyp:k) and [derivative order](hyp:i), if [the derivative order is below the power](hyp:hi), then [the corresponding derivative of the symmetric power bump vanishes at zero](goal). -/
lemma rod_boundary_zero (k i : ℕ) (hi : i < k) :
    (deriv^[i] (fun x : ℝ => x^k * (1-x)^k)) 0 = 0 := by
  rw [← iteratedDeriv_eq_iterate]
  have hp : ContDiffAt ℝ i (fun x : ℝ => x^k) 0 := by fun_prop
  have hq : ContDiffAt ℝ i (fun x : ℝ => (1-x)^k) 0 := by fun_prop
  change iteratedDeriv i ((fun x : ℝ => x^k) * (fun x : ℝ => (1-x)^k)) 0 = 0
  rw [iteratedDeriv_mul hp hq]
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ i := by simpa using Finset.mem_range.mp hj
  have hjk : j < k := lt_of_le_of_lt hjle hi
  have hpow : iteratedDeriv j (fun x : ℝ => x^k) 0 = 0 := by
    simp [iteratedDeriv_pow, zero_pow (Nat.sub_ne_zero_of_lt hjk)]
  rw [hpow]
  ring

/-- If the [first degree](hyp:j) is [strictly below the second degree](hyp:k,hjk), then [the two shifted Legendre polynomials are orthogonal on the unit interval](goal). -/
lemma shiftedLegendre_orthogonal_unit_of_lt {j k : ℕ} (hjk : j < k) :
    (∫ x in (0 : ℝ)..1, Polynomial.aeval x (Polynomial.shiftedLegendre j) *
      Polynomial.aeval x (Polynomial.shiftedLegendre k)) = 0 := by
  let p : ℝ → ℝ := fun x => Polynomial.aeval x (Polynomial.shiftedLegendre j)
  let f : ℝ → ℝ := fun x => x^k * (1-x)^k
  have hibp := integral_mul_iterated_deriv_eq k 0 1 p f
    (by
      intro x hx
      exact ((Polynomial.shiftedLegendre j).contDiff_aeval ⊤).contDiffAt)
    (by intro x hx; dsimp [f]; fun_prop)
    (by
      intro i hi
      refine ⟨rod_boundary_zero k i hi, ?_⟩
      exact iter_deriv_mul_one_sub_pow_at_one (fun x : ℝ => x^k) k i (by fun_prop) hi)
    (by norm_num)
  have hpzero : deriv^[k] p = 0 := by
    change deriv^[k] (fun x : ℝ => Polynomial.aeval x
      (Polynomial.shiftedLegendre j)) = 0
    rw [iter_deriv_aeval_int,
      Polynomial.iterate_derivative_eq_zero (by simpa using hjk)]
    funext x
    simp
  rw [hpzero] at hibp
  simp only [Pi.zero_apply, zero_mul, intervalIntegral.integral_zero, mul_zero] at hibp
  have hscale : (k.factorial : ℝ) *
      (∫ x in (0 : ℝ)..1, Polynomial.aeval x (Polynomial.shiftedLegendre j) *
        Polynomial.aeval x (Polynomial.shiftedLegendre k)) =
      ∫ x in (0 : ℝ)..1, p x * (deriv^[k] f) x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (k.factorial : ℝ) *
          (Polynomial.aeval x (Polynomial.shiftedLegendre j) *
            Polynomial.aeval x (Polynomial.shiftedLegendre k)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (k.factorial : ℝ) *
            (Polynomial.aeval x (Polynomial.shiftedLegendre j) *
              Polynomial.aeval x (Polynomial.shiftedLegendre k)) =
          Polynomial.aeval x (Polynomial.shiftedLegendre j) *
            (deriv^[k] (fun y : ℝ => y^k * (1-y)^k)) x
        rw [← shiftedLegendre_rodrigues_eval k x]
        ring
  rw [hibp] at hscale
  exact (mul_eq_zero.mp hscale).resolve_left (by positivity)

/-- For a [degree](hyp:k), [the derivative of that order of the shifted Legendre polynomial is the stated constant polynomial](goal). -/
lemma iterate_derivative_shiftedLegendre (k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.shiftedLegendre k) =
      Polynomial.C ((k.factorial : ℤ) * ((-1 : ℤ)^k * ((2*k).choose k : ℤ))) := by
  calc
    _ = Polynomial.C ((Polynomial.derivative^[k]
        (Polynomial.shiftedLegendre k)).coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero
        ((Polynomial.natDegree_iterate_derivative _ _).trans (by simp))
    _ = _ := by
      congr 1
      rw [Polynomial.coeff_iterate_derivative]
      simp [Polynomial.coeff_shiftedLegendre, Nat.descFactorial_self]
      all_goals ring
      all_goals simp

/-- For a [degree](hyp:k), [the integral of the squared shifted Legendre polynomial over the unit interval is the reciprocal of twice the degree plus one](goal). -/
lemma shiftedLegendre_sq_integral_unit (k : ℕ) :
    (∫ x in (0 : ℝ)..1, (Polynomial.aeval x (Polynomial.shiftedLegendre k) : ℝ) ^ 2) =
      1 / (2 * (k : ℝ) + 1) := by
  let p : ℝ → ℝ := fun x => Polynomial.aeval x (Polynomial.shiftedLegendre k)
  let f : ℝ → ℝ := fun x => x^k * (1-x)^k
  have hibp := integral_mul_iterated_deriv_eq k 0 1 p f
    (by
      intro x hx
      exact ((Polynomial.shiftedLegendre k).contDiff_aeval ⊤).contDiffAt)
    (by intro x hx; dsimp [f]; fun_prop)
    (by
      intro i hi
      refine ⟨rod_boundary_zero k i hi, ?_⟩
      exact iter_deriv_mul_one_sub_pow_at_one (fun x : ℝ => x^k) k i (by fun_prop) hi)
    (by norm_num)
  have hpder : deriv^[k] p = fun _ : ℝ =>
      (k.factorial : ℝ) * ((-1 : ℝ)^k * ((2*k).choose k : ℝ)) := by
    change deriv^[k] (fun x : ℝ => Polynomial.aeval x
      (Polynomial.shiftedLegendre k)) = _
    rw [iter_deriv_aeval_int, iterate_derivative_shiftedLegendre]
    funext x
    simp
  rw [hpder] at hibp
  have hscale : (k.factorial : ℝ) *
      (∫ x in (0 : ℝ)..1, (Polynomial.aeval x
        (Polynomial.shiftedLegendre k) : ℝ)^2) =
      ∫ x in (0 : ℝ)..1, p x * (deriv^[k] f) x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (k.factorial : ℝ) *
          ((Polynomial.aeval x (Polynomial.shiftedLegendre k) : ℝ)^2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (k.factorial : ℝ) *
            ((Polynomial.aeval x (Polynomial.shiftedLegendre k) : ℝ)^2) =
          Polynomial.aeval x (Polynomial.shiftedLegendre k) *
            (deriv^[k] (fun y : ℝ => y^k * (1-y)^k)) x
        rw [← shiftedLegendre_rodrigues_eval k x]
        ring
  rw [hibp] at hscale
  have hbeta := integral_rpow_mul_one_sub_pow k (k + 1 : ℝ) (by positivity)
  have hbeta' : (∫ x in (0 : ℝ)..1, x^k * (1-x)^k) =
      (Nat.factorial k : ℝ) / ((k + 1 : ℝ) * rising ((k + 1 : ℝ) + 1) k) := by
    simpa only [show (k + 1 : ℝ) - 1 = (k : ℝ) by norm_num,
      Real.rpow_natCast] using hbeta
  rw [intervalIntegral.integral_const_mul] at hscale
  change (k.factorial : ℝ) *
      (∫ x in (0 : ℝ)..1, (Polynomial.aeval x
        (Polynomial.shiftedLegendre k) : ℝ)^2) =
    (-1 : ℝ)^k * ((k.factorial : ℝ) *
      ((-1 : ℝ)^k * ((2*k).choose k : ℝ)) *
      (∫ x in (0 : ℝ)..1, x^k * (1-x)^k)) at hscale
  rw [hbeta'] at hscale
  have hrising : rising ((k + 1 : ℝ) + 1) k =
      ((k + 2).ascFactorial k : ℕ) := by
    unfold rising
    rw [show (k + 1 : ℝ) + 1 = ((k + 2 : ℕ) : ℝ) by push_cast; ring,
      ascPochhammer_nat_eq_natCast_ascFactorial]
  rw [hrising] at hscale
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial
    (n := 2*k) (k := k) (by omega : k ≤ 2*k)
  rw [show 2*k-k = k by omega] at hchooseNat
  have hchoose : ((2*k).choose k : ℝ) * k.factorial * k.factorial =
      ((2*k).factorial : ℕ) := by exact_mod_cast hchooseNat
  have hascNat := Nat.factorial_mul_ascFactorial (k + 1) k
  rw [show k+1+1 = k+2 by omega, show k+1+k = 2*k+1 by omega] at hascNat
  have hasc : ((k+1).factorial : ℝ) * (k+2).ascFactorial k =
      ((2*k+1).factorial : ℕ) := by
    exact_mod_cast hascNat
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hid : ((2*k).choose k : ℝ) * k.factorial * (2*k+1) =
      (k+1) * (k+2).ascFactorial k := by
    apply (mul_left_cancel₀ hfac)
    calc
      (k.factorial : ℝ) * (((2*k).choose k : ℝ) * k.factorial * (2*k+1)) =
          (((2*k).choose k : ℝ) * k.factorial * k.factorial) * (2*k+1) := by ring
      _ = ((2*k).factorial : ℝ) * (2*k+1) := by rw [hchoose]
      _ = ((2*k+1).factorial : ℕ) := by
        rw [Nat.factorial_succ]
        norm_num
        ring
      _ = ((k+1).factorial : ℝ) * (k+2).ascFactorial k := hasc.symm
      _ = (k.factorial : ℝ) * ((k+1) * (k+2).ascFactorial k) := by
        rw [Nat.factorial_succ]
        norm_num
        ring
  have hden : (0 : ℝ) < (k+1) * (k+2).ascFactorial k := by positivity
  have hratio : ((2*k).choose k : ℝ) * k.factorial /
      ((k+1) * (k+2).ascFactorial k) = 1 / (2*k+1) := by
    apply (div_eq_iff hden.ne').2
    let B : ℝ := 2*(k:ℝ)+1
    have hB : B ≠ 0 := by dsimp [B]; positivity
    calc
      ((2*k).choose k : ℝ) * k.factorial =
          ((k+1) * (k+2).ascFactorial k) / B := by
        apply (eq_div_iff hB).2
        simpa [B] using hid
      _ = 1 / B * ((k+1) * (k+2).ascFactorial k) := by
        field_simp
      _ = _ := by rfl
  have hsign : (-1 : ℝ)^k * (-1 : ℝ)^k = 1 := by
    rw [← pow_add]
    have : k + k = 2*k := by omega
    rw [this, pow_mul]
    norm_num
  have hcancel : (∫ x in (0 : ℝ)..1, (Polynomial.aeval x
      (Polynomial.shiftedLegendre k) : ℝ)^2) =
      ((2*k).choose k : ℝ) * k.factorial /
        ((k+1) * (k+2).ascFactorial k) := by
    apply (mul_left_cancel₀ hfac)
    rw [hscale]
    field_simp
    nlinarith only [hsign]
  rw [hcancel, hratio]

/-- For [two degrees](hyp:j,k), [the integral over the unit interval of the product of the two shifted Legendre polynomials is zero when the degrees differ and one over twice the degree plus one when they agree](goal). -/
lemma shiftedLegendre_orthogonal_unit (j k : ℕ) :
    (∫ x in (0 : ℝ)..1, Polynomial.aeval x (Polynomial.shiftedLegendre j) *
      Polynomial.aeval x (Polynomial.shiftedLegendre k)) =
      if j = k then 1 / (2 * (j : ℝ) + 1) else 0 := by
  by_cases h : j = k
  · subst k
    rw [if_pos rfl]
    simpa only [pow_two] using shiftedLegendre_sq_integral_unit j
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hjk | hkj
    · exact shiftedLegendre_orthogonal_unit_of_lt hjk
    · calc
        _ = ∫ x in (0 : ℝ)..1, Polynomial.aeval x (Polynomial.shiftedLegendre k) *
            Polynomial.aeval x (Polynomial.shiftedLegendre j) := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
        _ = 0 := shiftedLegendre_orthogonal_unit_of_lt hkj


end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi


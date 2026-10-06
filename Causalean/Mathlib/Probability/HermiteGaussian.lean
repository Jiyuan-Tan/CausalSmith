module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Tactic.NormNum

/-!
# Gaussian orthogonality of probabilists’ Hermite polynomials

This module develops polynomial Gaussian integrability, a polynomial Stein
identity, and factorial-normalized orthogonality for Mathlib’s probabilists’
Hermite polynomials under the variance-one Gaussian law.
-/

public section

open Filter MeasureTheory Polynomial ProbabilityTheory
open scoped NNReal Topology

namespace Causalean.Mathlib.Probability


/-- [A real polynomial](hyp:p), multiplied by a Gaussian weight with
[positive precision](hyp:b,hb), [is integrable on the real line](goal).

Expand the polynomial as a finite sum of monomials. For each monomial reuse
`integrable_rpow_mul_exp_neg_mul_sq` with the exponent a natural number,
converting real powers by `Real.rpow_natCast`. Integrable finite sums and
constant multiples then give the polynomial statement.
-/
theorem integrable_eval_mul_gaussian (p : ℝ[X]) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [eval_add, add_mul]
      exact hp.add hq
  | monomial n a =>
      have hn : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
      simpa only [eval_monomial, Real.rpow_natCast, mul_assoc] using
        (integrable_rpow_mul_exp_neg_mul_sq hb hn).const_mul a

/-- [A real polynomial](hyp:p), multiplied by a Gaussian weight with
[positive precision](hyp:b,hb), [tends to zero at both ends of the real line](goal).

Expand into monomials and use
`tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact`; pass from absolute powers
to signed monomials by a norm squeeze, then use finite-sum continuity.
The cocompact filter supplies both boundary limits required by improper IBP.
-/
theorem tendsto_eval_mul_gaussian_cocompact (p : ℝ[X]) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2))
      (cocompact ℝ) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [eval_add, add_mul, zero_add] using hp.add hq
  | monomial n a =>
      have hn : Tendsto (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2))
          (cocompact ℝ) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_pos (Real.exp_pos _), Real.rpow_natCast] using
          tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : ℝ)
      simpa only [eval_monomial, mul_assoc, mul_zero] using hn.const_mul a

/-- The variance-one, mean-zero Gaussian density [at a real point](hyp:x)
[is the normalized exponential of minus half the squared point](goal). -/
theorem gaussianPDFReal_standard (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [gaussianPDFReal, neg_div]

/-- [Every real polynomial](hyp:p) [is integrable under the standard Gaussian law](goal).

Use the polynomial Gaussian-weight integrability with precision one half,
then the `withDensity` integrability equivalence for `gaussianReal 0 1`.
Alternatively, Mathlib's Gaussian exponential moments imply all monomial
moments; a finite polynomial expansion finishes. No Hermite facts enter here.
-/
theorem integrable_eval_gaussianReal (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).2
  have h := (integrable_eval_mul_gaussian p (1 / 2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  apply h.congr
  filter_upwards [] with x
  rw [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_standard]
  have hexp : -(x ^ 2 / 2) = -(1 / 2 : ℝ) * x ^ 2 := by ring
  rw [hexp]
  ring

/-- Integrating [a real function](hyp:f) under the standard Gaussian law
[equals its Lebesgue integral against the normalized Gaussian weight](goal). -/
theorem integral_gaussianReal_standard (f : ℝ → ℝ) :
    (∫ x, f x ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, f x * Real.exp (-(x ^ 2 / 2)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp_rw [gaussianPDFReal_standard, smul_eq_mul, mul_assoc,
    mul_comm (Real.exp _)]
  rw [integral_const_mul]


/-- Evaluating [a successor Hermite polynomial](hyp:n) at [a real point](hyp:x)
[gives the point times the preceding polynomial minus its polynomial derivative](goal). -/
theorem hermite_eval_succ (n : ℕ) (x : ℝ) :
    (aeval x (hermite (n + 1)) : ℝ) =
      x * aeval x (hermite n) - aeval x (derivative (hermite n)) := by
  rw [hermite_succ, map_sub, map_mul, aeval_X]

/-- Differentiating [a successor Hermite polynomial](hyp:n)
[gives its order times the preceding Hermite polynomial](goal).

Prove by induction from `hermite_succ`, `derivative_mul`, and `derivative_X`.
At the induction step, differentiate the defining recurrence and use the
previous derivative identity inside the remaining recurrence. This is an
identity over the integers, before any evaluation or Gaussian analysis.
-/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = C (n + 1 : ℤ) * hermite n := by
  induction n with
  | zero => simp [hermite_succ, hermite_zero]
  | succ n ih =>
    rw [hermite_succ, derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermite_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- At [a real point](hyp:x), [a successor Hermite polynomial](hyp:n)
[has derivative equal to its order times the preceding evaluation](goal). -/
theorem hasDerivAt_hermite_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (aeval y (hermite (n + 1)) : ℝ))
      ((n + 1 : ℝ) * aeval x (hermite n)) x := by
  have h := (hermite (n + 1)).hasDerivAt_aeval x
  rw [derivative_hermite_succ, map_mul, aeval_C] at h
  simpa only [map_add, map_natCast, map_one] using h

/-- The analytic derivative of [a successor Hermite evaluation](hyp:n)
[at a real point](hyp:x) [is its order times the preceding evaluation](goal). -/
theorem deriv_hermite_succ (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => (aeval y (hermite (n + 1)) : ℝ)) x =
      (n + 1 : ℝ) * aeval x (hermite n) :=
  (hasDerivAt_hermite_succ n x).deriv



/-- At [a real point](hyp:x), [the unnormalized standard Gaussian weight has
derivative equal to minus the point times the weight](goal). -/
theorem hasDerivAt_standardGaussianWeight (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      (-x * Real.exp (-(x ^ 2 / 2))) x := by
  simpa [id_eq, pow_one, mul_comm] using
    (((hasDerivAt_id x).pow 2).div_const 2).neg.exp

/-- For [a real polynomial](hyp:p), [its derivative integrated against the
unnormalized standard Gaussian weight equals its evaluation multiplied by the
variable and integrated against the same weight](goal).

Apply `integral_mul_deriv_eq_deriv_mul` to `p.eval` and
`fun x => Real.exp (-(x^2/2))`, with derivative functions
`p.derivative.eval` and `fun x => -x * Real.exp (-(x^2/2))`.
Use `p.hasDerivAt` and `hasDerivAt_standardGaussianWeight` on the required
topological supports. Both differentiated products are integrable by
`integrable_eval_mul_gaussian` applied to `X * p` and `p.derivative`
at precision `1/2`; use `Integrable.congr` and pointwise ring normalization
to convert the exponent and sign. Both boundary products tend to zero by
`tendsto_eval_mul_gaussian_cocompact` and `atBot_le_cocompact` /
`atTop_le_cocompact`. The IBP conclusion has zero boundary terms and a minus
sign on each integral; remove those using `integral_neg` and `neg_injective`.
The wrapper below transfers this identity to the normalized Gaussian law.
-/
theorem integral_mul_eval_mul_gaussian (p : ℝ[X]) :
    (∫ x : ℝ, (x * p.eval x) * Real.exp (-(x ^ 2 / 2))) =
      ∫ x : ℝ, p.derivative.eval x * Real.exp (-(x ^ 2 / 2)) := by
  have hexp (x : ℝ) : -(x ^ 2 / 2) = -(1 / 2 : ℝ) * x ^ 2 := by ring
  have huv' : Integrable (fun x : ℝ =>
      p.eval x * (-x * Real.exp (-(x ^ 2 / 2)))) := by
    apply (integrable_eval_mul_gaussian (X * p) (1 / 2) (by norm_num)).neg.congr
    filter_upwards [] with x
    simp only [Pi.neg_apply, eval_mul, eval_X, hexp]
    ring
  have hu'v : Integrable (fun x : ℝ =>
      p.derivative.eval x * Real.exp (-(x ^ 2 / 2))) := by
    simpa only [hexp] using
      integrable_eval_mul_gaussian p.derivative (1 / 2) (by norm_num)
  have hlim : Tendsto (fun x : ℝ => p.eval x * Real.exp (-(x ^ 2 / 2)))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [hexp] using
      tendsto_eval_mul_gaussian_cocompact p (1 / 2) (by norm_num)
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (u := p.eval) (u' := p.derivative.eval)
    (v := fun x : ℝ => Real.exp (-(x ^ 2 / 2)))
    (v' := fun x : ℝ => -x * Real.exp (-(x ^ 2 / 2)))
    (fun x _ => p.hasDerivAt x) (fun x _ => hasDerivAt_standardGaussianWeight x)
    huv' hu'v (hlim.mono_left atBot_le_cocompact)
    (hlim.mono_left atTop_le_cocompact)
  have hsign (x : ℝ) : p.eval x * (-x * Real.exp (-(x ^ 2 / 2))) =
      -((x * p.eval x) * Real.exp (-(x ^ 2 / 2))) := by ring
  simp only [hsign, integral_neg, sub_self, zero_sub] at hibp
  exact neg_injective hibp

/-- For [a real polynomial](hyp:p), [the standard Gaussian expectation of the
variable times its evaluation equals the expectation of its derivative](goal).

Multiply the unnormalized polynomial integration-by-parts identity by the
standard Gaussian normalizer using `integral_gaussianReal_standard`.
-/
theorem integral_mul_eval_gaussianReal (p : ℝ[X]) :
    (∫ x, x * p.eval x ∂gaussianReal 0 1) =
      ∫ x, p.derivative.eval x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_standard, integral_gaussianReal_standard,
    integral_mul_eval_mul_gaussian]



/-- Products of [two real Hermite evaluations](hyp:j,k)
[are integrable under the standard Gaussian law](goal). -/
theorem integrable_hermite_mul (j k : ℕ) :
    Integrable (fun x : ℝ => (aeval x (hermite j) : ℝ) * aeval x (hermite k))
      (gaussianReal 0 1) := by
  simpa [Polynomial.eval_mul, Polynomial.eval_map, Polynomial.aeval_def] using
    integrable_eval_gaussianReal
      ((hermite j).map (Int.castRingHom ℝ) * (hermite k).map (Int.castRingHom ℝ))

/-- Every [positive-order Hermite polynomial](hyp:n)
[has zero standard Gaussian expectation](goal).

Apply the polynomial Stein identity to the real coefficient map of `hermite n`,
and subtract using the defining Hermite recurrence and polynomial integrability.
For the map/evaluation conversion use `Polynomial.eval_map`,
`Polynomial.aeval_def`, and `Polynomial.derivative_map`. Obtain integrability
of the two subtracted functions from `integrable_eval_gaussianReal` applied
to `X * (hermite n).map (Int.castRingHom ℝ)` and the derivative of that map.
Rewrite pointwise with `hermite_eval_succ`, then use `integral_sub` and Stein;
the two resulting integrals agree, including when `n = 0`.
-/
theorem integral_hermite_succ (n : ℕ) :
    (∫ x, (aeval x (hermite (n + 1)) : ℝ) ∂gaussianReal 0 1) = 0 := by
  have hx : Integrable (fun x : ℝ => x * aeval x (hermite n))
      (gaussianReal 0 1) := by
    apply (integrable_eval_gaussianReal
      (X * (hermite n).map (Int.castRingHom ℝ))).congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_map,
      Polynomial.aeval_def, algebraMap_int_eq]
  have hd : Integrable (fun x : ℝ => (aeval x (derivative (hermite n)) : ℝ))
      (gaussianReal 0 1) := by
    simpa only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def,
      algebraMap_int_eq] using
      integrable_eval_gaussianReal ((hermite n).map (Int.castRingHom ℝ)).derivative
  have hs : (∫ x, x * (aeval x (hermite n) : ℝ) ∂gaussianReal 0 1) =
      ∫ x, (aeval x (derivative (hermite n)) : ℝ) ∂gaussianReal 0 1 := by
    simpa only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def,
      algebraMap_int_eq] using
      integral_mul_eval_gaussianReal ((hermite n).map (Int.castRingHom ℝ))
  simp_rw [hermite_eval_succ]
  rw [integral_sub hx hd, hs, sub_self]

/-- Raising both [Hermite orders](hyp:j,k) by one
[multiplies their standard Gaussian inner product by the second raised order](goal).

Apply Stein to the product of the real coefficient maps of `hermite j` and
`hermite (k+1)`. Expand the derivative of the product. The term differentiating
the first factor cancels against the derivative term in `hermite_eval_succ`;
`derivative_hermite_succ` identifies the surviving factor. Every integral
linearity step uses `integrable_eval_gaussianReal` for the relevant polynomial.
In detail, write `p = (hermite j).map (Int.castRingHom ℝ)` and
`q = (hermite (k + 1)).map (Int.castRingHom ℝ)`. Stein on `p * q` gives
`E[x * p(x) * q(x)] = E[p'(x) * q(x)] + E[p(x) * q'(x)]`.
The raised first factor subtracts precisely the first term on the right.
Use integrability of `X * (p * q)`, `p.derivative * q`, and
`p * q.derivative` before invoking `integral_sub` or `integral_add`.
After `derivative_hermite_succ`, `integral_const_mul` extracts the order.
Pointwise `ring` normalizes product association; `integral_congr_ae`
can transport these equalities without unfolding the Gaussian measure.
-/
theorem integral_hermite_succ_mul_succ (j k : ℕ) :
    (∫ x, (aeval x (hermite (j + 1)) : ℝ) * aeval x (hermite (k + 1))
      ∂gaussianReal 0 1) =
      (k + 1 : ℝ) * ∫ x, (aeval x (hermite j) : ℝ) * aeval x (hermite k)
        ∂gaussianReal 0 1 := by
  let p := (hermite j).map (Int.castRingHom ℝ)
  let q := (hermite (k + 1)).map (Int.castRingHom ℝ)
  have hx : Integrable (fun x : ℝ => x * (p.eval x * q.eval x))
      (gaussianReal 0 1) := by
    apply (integrable_eval_gaussianReal (X * (p * q))).congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hpq : Integrable (fun x : ℝ => p.derivative.eval x * q.eval x)
      (gaussianReal 0 1) := by
    apply (integrable_eval_gaussianReal (p.derivative * q)).congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul]
  have hqp : Integrable (fun x : ℝ => p.eval x * q.derivative.eval x)
      (gaussianReal 0 1) := by
    apply (integrable_eval_gaussianReal (p * q.derivative)).congr
    filter_upwards [] with x
    simp only [Polynomial.eval_mul]
  have hs : (∫ x, x * (p.eval x * q.eval x) ∂gaussianReal 0 1) =
      (∫ x, p.derivative.eval x * q.eval x ∂gaussianReal 0 1) +
        ∫ x, p.eval x * q.derivative.eval x ∂gaussianReal 0 1 := by
    have h := integral_mul_eval_gaussianReal (p * q)
    simp only [Polynomial.eval_mul, Polynomial.derivative_mul, Polynomial.eval_add] at h
    rw [integral_add hpq hqp] at h
    exact h
  calc
    _ = ∫ x, x * (p.eval x * q.eval x) - p.derivative.eval x * q.eval x
        ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hermite_eval_succ j x]
      simp only [p, q, Polynomial.derivative_map,
        Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
      ring
    _ = ∫ x, p.eval x * q.derivative.eval x ∂gaussianReal 0 1 := by
      rw [integral_sub hx hpq, hs]
      ring
    _ = ∫ x, (k + 1 : ℝ) * ((aeval x (hermite j) : ℝ) * aeval x (hermite k))
        ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [p, q, Polynomial.derivative_map, Polynomial.eval_map,
        derivative_hermite_succ, Polynomial.aeval_def,
        algebraMap_int_eq, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Int.coe_castRingHom, Int.cast_add, Int.cast_natCast, Int.cast_one]
      ring
    _ = _ := integral_const_mul _ _

/-- [Two probabilists' Hermite polynomials](hyp:j,k) [have standard Gaussian
inner product equal to the order factorial when their orders agree and zero otherwise](goal).

Induct on the first index, generalizing the second. If either index is zero,
use `hermite_zero`, `integral_hermite_succ`, and probability normalization.
The successor/successor case follows from `integral_hermite_succ_mul_succ` and
`Nat.factorial_succ`, splitting on equality of the preceding indices.
-/
theorem integral_hermite_mul (j k : ℕ) :
    (∫ x, (aeval x (hermite j) : ℝ) * aeval x (hermite k) ∂gaussianReal 0 1) =
      if j = k then (Nat.factorial j : ℝ) else 0 := by
  induction j generalizing k with
  | zero =>
      cases k with
      | zero => simp
      | succ k =>
          simp only [hermite_zero, map_one, one_mul]
          rw [integral_hermite_succ]
          simp
  | succ j ih =>
      cases k with
      | zero =>
          simp only [hermite_zero, map_one, mul_one]
          rw [integral_hermite_succ]
          simp
      | succ k =>
          rw [integral_hermite_succ_mul_succ, ih]
          by_cases h : j = k
          · subst k
            simp [Nat.factorial_succ]
          · simp [h]


end Causalean.Mathlib.Probability

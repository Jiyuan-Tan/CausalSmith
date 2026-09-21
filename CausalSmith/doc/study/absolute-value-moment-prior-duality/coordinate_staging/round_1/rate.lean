/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Basic
import Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Fejer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Universal `1 / K` bounds for approximation of absolute value

This module proves explicit, non-sharp universal upper and lower bounds for the
best degree-`K` uniform approximation error of `x ↦ |x|` on `[-1,1]`.  The
upper bound comes from a truncated Chebyshev expansion, while the lower bound
uses a bounded de la Vallée--Poussin Fourier certificate at the cusp.  No
sharp Bernstein constant is needed.
-/

namespace Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

open scoped Real ComplexConjugate
open Set MeasureTheory intervalIntegral
open FejerCertificate

noncomputable section

private local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private noncomputable def sinCircle : C(AddCircle Real.pi, ℂ) :=
  ⟨AddCircle.liftIoc Real.pi 0 (fun t : ℝ => (Real.sin t : ℂ)), by
    apply AddCircle.liftIoc_continuous
    · simp
    · fun_prop⟩

private lemma fourierCoeff_sinCircle (n : ℤ) :
    fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) n =
      (-2 : ℂ) / (Real.pi * ((4 : ℤ) * n ^ 2 - 1)) := by
  change fourierCoeff (AddCircle.liftIoc Real.pi 0
    (fun t : ℝ => (Real.sin t : ℂ))) n = _
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, smul_eq_mul]
  have hden : ((1 : ℂ) - 4 * (n : ℂ) ^ 2) ≠ 0 := by
    rw [show ((1 : ℂ) - 4 * (n : ℂ) ^ 2) = ((1 - 4 * n ^ 2 : ℤ) : ℂ) by
      push_cast; ring]
    exact_mod_cast (show (1 - 4 * n ^ 2 : ℤ) ≠ 0 by omega)
  have hden' : (4 * (n : ℂ) ^ 2 - 1) ≠ 0 := by
    rw [show (4 : ℂ) * (n : ℂ) ^ 2 - 1 = -(1 - 4 * (n : ℂ) ^ 2) by ring,
      neg_ne_zero]
    exact hden
  let F : ℝ → ℂ := fun x =>
    Complex.exp ((-2 * Complex.I * (n : ℂ)) * x) *
      (((-2 * Complex.I * (n : ℂ)) * Real.sin x - Real.cos x) /
        (1 - 4 * (n : ℂ) ^ 2))
  have hderiv : ∀ x : ℝ, HasDerivAt F
      (Complex.exp ((-2 * Complex.I * (n : ℂ)) * x) * Real.sin x) x := by
    intro x
    have hd := (((((hasDerivAt_id x).ofReal_comp.const_mul
      (-2 * Complex.I * (n : ℂ)))).cexp).mul
        (((((Real.hasDerivAt_sin x).ofReal_comp.const_mul
          (-2 * Complex.I * (n : ℂ))).sub (Real.hasDerivAt_cos x).ofReal_comp).div_const
            (1 - 4 * (n : ℂ) ^ 2))))
    apply hd.congr_deriv
    try simp only [id_eq, Pi.sub_apply, map_one, map_neg]
    field_simp [hden]
    ring_nf
    rw [Complex.I_sq]
    have hden_nf : (1 - (n : ℂ) ^ 2 * 4) ≠ 0 := by
      convert hden using 1 <;> ring
    field_simp [hden_nf]
    norm_num <;> ring
  have hint : IntervalIntegrable
      (fun x : ℝ => Complex.exp ((-2 * Complex.I * (n : ℂ)) * x) * Real.sin x)
      volume 0 Real.pi :=
    (show Continuous (fun x : ℝ =>
        Complex.exp ((-2 * Complex.I * (n : ℂ)) * x) * Real.sin x) by fun_prop).intervalIntegrable
      0 Real.pi
  simp_rw [fourier_coe_apply]
  simp only [zero_add, sub_zero, Int.cast_neg]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hintegrand : (fun x : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(n : ℂ)) * x / Real.pi) *
        Real.sin x) =
      (fun x : ℝ => Complex.exp ((-2 * Complex.I * (n : ℂ)) * x) * Real.sin x) := by
    funext x
    congr 2
    field_simp
  rw [hintegrand]
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  dsimp [F]
  rw [show Complex.exp ((-2 * Complex.I * (n : ℂ)) * Real.pi) = 1 by
    convert Complex.exp_int_mul_two_pi_mul_I (-n) using 1 <;> push_cast <;> ring]
  simp only [Real.sin_pi, map_zero, mul_zero, Real.cos_pi, map_neg, map_one,
    neg_one_mul, sub_neg_eq_add, zero_add, one_mul, Real.sin_zero, Real.cos_zero, sub_zero,
    Complex.exp_zero]
  push_cast
  simp only [mul_zero, sub_neg_eq_add, sub_zero]
  rw [show (4 : ℂ) * (n : ℂ) ^ 2 - 1 = -(1 - 4 * (n : ℂ) ^ 2) by ring]
  field_simp [hpi, hden]
  ring

private lemma summable_fourierCoeff_sinCircle :
    Summable (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ)) := by
  have hbound : ∀ j : ℕ,
      ‖fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) ((j : ℤ) + 1)‖ ≤
        1 / ((j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j
    rw [fourierCoeff_sinCircle, norm_div, norm_neg]
    norm_num
    have hj : (0 : ℝ) < j + 1 := by positivity
    have hdenpos : 0 < 4 * ((j : ℝ) + 1) ^ 2 - 1 := by
      nlinarith [sq_nonneg (j : ℝ)]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [show (4 * ((j : ℂ) + 1) ^ 2 - 1) =
        ((4 * ((j : ℝ) + 1) ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]
    simp only [inv_eq_one_div, Nat.cast_add, Nat.cast_one]
    change 2 / (Real.pi * (4 * ((j : ℝ) + 1) ^ 2 - 1)) ≤
      1 / ((j : ℝ) + 1) ^ 2
    apply (le_div_iff₀ (sq_pos_of_pos hj)).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos Real.pi_pos hdenpos)).2
    nlinarith [Real.two_le_pi, sq_nonneg ((j : ℝ) + 1)]
  have hpossum : Summable (fun j : ℕ =>
      fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) ((j : ℤ) + 1)) := by
    apply Summable.of_norm_bounded
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
    exact hbound
  apply Summable.of_add_one_of_neg_add_one hpossum
  exact hpossum.congr (fun j => by
    rw [fourierCoeff_sinCircle, fourierCoeff_sinCircle]
    congr 2
    push_cast
    ring)

private lemma sinCircle_apply_add_half_pi {theta : ℝ}
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    sinCircle (theta + Real.pi / 2 : ℝ) = (|Real.cos theta| : ℝ) := by
  by_cases hle : theta + Real.pi / 2 ≤ Real.pi
  · rw [show sinCircle (theta + Real.pi / 2 : ℝ) =
        (Real.sin (theta + Real.pi / 2) : ℝ) by
      change AddCircle.liftIoc Real.pi 0 (fun t : ℝ => (Real.sin t : ℂ))
        (theta + Real.pi / 2 : ℝ) = _
      apply AddCircle.liftIoc_coe_apply
      exact ⟨add_pos_of_nonneg_of_pos htheta.1 (half_pos Real.pi_pos), by simpa using hle⟩]
    rw [Real.sin_add_pi_div_two, abs_of_nonneg]
    exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [htheta.1])
  · have hrep : ((theta + Real.pi / 2 : ℝ) : AddCircle Real.pi) =
        ((theta + Real.pi / 2 - Real.pi : ℝ) : AddCircle Real.pi) := by
      calc
        ((theta + Real.pi / 2 : ℝ) : AddCircle Real.pi) =
            (((theta + Real.pi / 2 - Real.pi) + Real.pi : ℝ) : AddCircle Real.pi) := by
              congr 1 <;> ring
        _ = ((theta + Real.pi / 2 - Real.pi : ℝ) : AddCircle Real.pi) :=
          AddCircle.coe_add_period Real.pi _
    rw [show sinCircle (theta + Real.pi / 2 : ℝ) =
        (Real.sin (theta + Real.pi / 2 - Real.pi) : ℝ) by
      rw [hrep]
      change AddCircle.liftIoc Real.pi 0 (fun t : ℝ => (Real.sin t : ℂ))
        (theta + Real.pi / 2 - Real.pi : ℝ) = _
      apply AddCircle.liftIoc_coe_apply
      constructor <;> linarith [htheta.2, Real.pi_pos]]
    rw [show theta + Real.pi / 2 - Real.pi = theta - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two, abs_of_nonpos]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by
      linarith [htheta.2, Real.pi_pos])

private noncomputable def absChebTerm (j : ℕ) (x : ℝ) : ℝ :=
  (4 / Real.pi) * (-1 : ℝ) ^ j *
    (Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)).eval x /
      (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)

private lemma pairedFourierTerm (j : ℕ) (theta : ℝ) :
    let z : AddCircle Real.pi := (theta + Real.pi / 2 : ℝ)
    fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) ((j + 1 : ℕ) : ℤ) •
        fourier ((j + 1 : ℕ) : ℤ) z +
      fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (-((j + 1 : ℕ) : ℤ)) •
        fourier (-((j + 1 : ℕ) : ℤ)) z =
      (absChebTerm j (Real.cos theta) : ℝ) := by
  dsimp only
  rw [fourierCoeff_sinCircle, fourierCoeff_sinCircle]
  simp_rw [fourier_coe_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [smul_eq_mul, Int.cast_natCast, Int.cast_neg]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((j : ℂ) + 1) *
          ((theta : ℂ) + Real.pi / 2) / Real.pi) =
        ((2 * ((j : ℝ) + 1) * (theta + Real.pi / 2) : ℝ) : ℂ) * Complex.I by
      field_simp; push_cast; ring,
    show (2 * (Real.pi : ℂ) * Complex.I * (-((j : ℂ) + 1)) *
          ((theta : ℂ) + Real.pi / 2) / Real.pi) =
        (-((2 * ((j : ℝ) + 1) * (theta + Real.pi / 2) : ℝ) : ℂ)) * Complex.I by
      field_simp; push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  rw [show (-((j : ℂ) + 1)) ^ 2 = ((j : ℂ) + 1) ^ 2 by ring]
  ring_nf
  rw [← Complex.ofReal_cos]
  rw [show (j : ℝ) * theta * 2 + (j : ℝ) * Real.pi + theta * 2 + Real.pi =
      2 * ((j + 1 : ℕ) : ℝ) * theta + ((j + 1 : ℕ) : ℝ) * Real.pi by push_cast; ring,
    Real.cos_add_nat_mul_pi]
  simp [absChebTerm, Polynomial.Chebyshev.T_real_cos]
  push_cast
  have hd : (3 + (j : ℂ) * 8 + (j : ℂ) ^ 2 * 4) ≠ 0 := by
    exact_mod_cast (show (3 + (j : ℝ) * 8 + (j : ℝ) ^ 2 * 4) ≠ 0 by positivity)
  rw [show Complex.cos (2 * ((j : ℂ) + 1) * theta) =
      Complex.cos ((j : ℂ) * theta * 2 + theta * 2) by congr 1 <;> ring]
  rw [pow_succ]
  field_simp [hpi, hd]
  rw [show Complex.cos ((theta : ℂ) * 2 * ((j : ℂ) + 1)) =
      Complex.cos ((j : ℂ) * theta * 2 + theta * 2) by congr 1 <;> ring]
  rw [show (4 : ℂ) * ((j : ℂ) + 1) ^ 2 - 1 =
      3 + (j : ℂ) * 8 + (j : ℂ) ^ 2 * 4 by ring]
  field_simp [hd]

private lemma hasSum_absChebTerm {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun j : ℕ => (absChebTerm j x : ℂ))
      ((|x| - 2 / Real.pi : ℝ) : ℂ) := by
  let theta := Real.arccos x
  have htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hcos : Real.cos theta = x := Real.cos_arccos (abs_le.mp hxabs).1 (abs_le.mp hxabs).2
  let z : AddCircle Real.pi := (theta + Real.pi / 2 : ℝ)
  let g : ℤ → ℂ := fun n =>
    fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) n • fourier n z
  have hg : HasSum g (sinCircle z) :=
    has_pointwise_sum_fourier_series_of_summable summable_fourierCoeff_sinCircle z
  have hpair := hg.nat_add_neg
  have htail : HasSum (fun n : ℕ => g ((n + 1 : ℕ) : ℤ) + g (-((n + 1 : ℕ) : ℤ)))
      (sinCircle z - g 0) := by
    change HasSum (fun n => (fun k : ℕ => g (k : ℤ) + g (-(k : ℤ))) (n + 1))
      (sinCircle z - g 0)
    apply (hasSum_nat_add_iff (f := fun k : ℕ => g (k : ℤ) + g (-(k : ℤ)))
      (g := sinCircle z - g 0) 1).mpr
    rw [show sinCircle z - g 0 +
        ∑ i ∈ Finset.range 1, (g (i : ℤ) + g (-(i : ℤ))) =
        sinCircle z + g 0 by
      rw [Finset.sum_range_one]
      norm_num]
    exact hpair
  convert htail using 1
  · funext j
    simpa [g, z, hcos] using (pairedFourierTerm j theta).symm
  · rw [sinCircle_apply_add_half_pi htheta]
    simp [g, fourierCoeff_sinCircle]
    rw [hcos]

private lemma hasSum_absChebTerm_real {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun j : ℕ => absChebTerm j x) (|x| - 2 / Real.pi) := by
  have h := (hasSum_absChebTerm hx).map Complex.reCLM Complex.continuous_re
  change HasSum (fun j : ℕ => (absChebTerm j x : ℂ).re)
    ((|x| - 2 / Real.pi : ℝ) : ℂ).re at h
  simpa using h

private lemma hasSum_cheb_denominator_tail (m : ℕ) :
    HasSum (fun j : ℕ => 1 / (4 * ((j + m + 1 : ℕ) : ℝ) ^ 2 - 1))
      (1 / (2 * (2 * (m : ℝ) + 1))) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => by
    apply one_div_nonneg.mpr
    have hreal : (1 : ℝ) ≤ ((j + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith) _).mpr
  let a : ℕ → ℝ := fun j => 1 / (2 * ((j + m : ℕ) : ℝ) + 1)
  have hterm (j : ℕ) :
      1 / (4 * ((j + m + 1 : ℕ) : ℝ) ^ 2 - 1) =
        (1 / 2 : ℝ) * (a j - a (j + 1)) := by
    dsimp [a]
    push_cast
    have h₁ : (2 * ((j : ℝ) + m) + 1) ≠ 0 := by positivity
    have h₂ : (2 * ((j : ℝ) + m + 1) + 1) ≠ 0 := by positivity
    have h₃ : (4 * ((j : ℝ) + m + 1) ^ 2 - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ (j : ℝ) + m + 1 := by
        exact_mod_cast (show 1 ≤ j + m + 1 by omega)
      nlinarith
    field_simp [h₁, h₂, h₃]
    ring
  have ha : Filter.Tendsto a Filter.atTop (nhds 0) := by
    dsimp [a]
    simp only [one_div]
    change Filter.Tendsto (fun j : ℕ => (2 * ((j + m : ℕ) : ℝ) + 1)⁻¹)
      Filter.atTop (nhds 0)
    apply tendsto_inv_atTop_zero.comp
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    refine ⟨N, fun n hn => ?_⟩
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith
  have ht : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (a 0 - a n))
      Filter.atTop (nhds ((1 / 2 : ℝ) * (a 0 - 0))) :=
    ((tendsto_const_nhds (x := a 0)).sub ha).const_mul (1 / 2 : ℝ)
  convert ht using 1
  · funext n
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
      Finset.sum_range_sub']
  · congr 1
    dsimp [a]
    have hm : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hm]
    ring

private noncomputable def absChebPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (2 / Real.pi) +
    ∑ j ∈ Finset.range m,
      ((4 / Real.pi) * (-1 : ℝ) ^ j / (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)) •
        Polynomial.Chebyshev.T ℝ (2 * (j + 1) : ℕ)

private lemma absChebPoly_eval (m : ℕ) (x : ℝ) :
    (absChebPoly m).eval x = 2 / Real.pi + ∑ j ∈ Finset.range m, absChebTerm j x := by
  rw [absChebPoly, Polynomial.eval_add, Polynomial.eval_C]
  simp_rw [Polynomial.eval_finset_sum]
  congr 1
  simp only [Polynomial.eval_smul]
  apply Finset.sum_congr rfl
  intro j hj
  simp [absChebTerm]
  ring

private lemma absChebPoly_natDegree_le (m : ℕ) :
    (absChebPoly m).natDegree ≤ 2 * m := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply (Polynomial.natDegree_smul_le _ _).trans
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    have hjlt : j < m := Finset.mem_range.mp hj
    omega

private lemma abs_absChebTerm_le (j : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |absChebTerm j x| ≤
      (4 / Real.pi) * (1 / (4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1)) := by
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one
    (2 * (j + 1) : ℕ) hx
  have hpi : 0 ≤ 4 / Real.pi := by positivity
  have hden : 0 < 4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1 := by
    have : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    nlinarith
  rw [absChebTerm, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, abs_of_nonneg hpi, abs_of_pos hden]
  rw [mul_div_assoc, mul_one_div]
  simpa [mul_assoc, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hT hden.le) hpi)

private lemma absChebPoly_error_le (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    abs (abs x - (absChebPoly m).eval x) ≤
      2 / (Real.pi * (2 * (m : ℝ) + 1)) := by
  have hs := hasSum_absChebTerm_real hx
  have hsplit := hs.summable.sum_add_tsum_nat_add m
  have herr : |x| - (absChebPoly m).eval x =
      ∑' j : ℕ, absChebTerm (j + m) x := by
    rw [absChebPoly_eval]
    linarith [hs.tsum_eq, hsplit]
  rw [herr]
  have hc : HasSum (fun j : ℕ =>
      (4 / Real.pi) * (1 / (4 * ((j + m + 1 : ℕ) : ℝ) ^ 2 - 1)))
      (2 / (Real.pi * (2 * (m : ℝ) + 1))) := by
    have hc' := (hasSum_cheb_denominator_tail m).mul_left (4 / Real.pi)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hm : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    rw [show (4 / Real.pi) * (1 / (2 * (2 * (m : ℝ) + 1))) =
        2 / (Real.pi * (2 * (m : ℝ) + 1)) by
      field_simp [hpi, hm]
      ring] at hc'
    exact hc'
  have hnorm : Summable (fun j : ℕ => ‖absChebTerm (j + m) x‖) := by
    apply Summable.of_norm_bounded hc.summable
    intro j
    rw [Real.norm_eq_abs]
    simpa [Nat.add_assoc] using abs_absChebTerm_le (j + m) (abs_le.mpr hx)
  calc
    |∑' j : ℕ, absChebTerm (j + m) x| = ‖∑' j : ℕ, absChebTerm (j + m) x‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖absChebTerm (j + m) x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ,
        (4 / Real.pi) * (1 / (4 * ((j + m + 1 : ℕ) : ℝ) ^ 2 - 1)) :=
      Summable.tsum_le_tsum (fun j => by
        rw [Real.norm_eq_abs]
        simpa [Nat.add_assoc] using abs_absChebTerm_le (j + m) (abs_le.mpr hx))
        hnorm hc.summable
    _ = 2 / (Real.pi * (2 * (m : ℝ) + 1)) := hc.tsum_eq

private lemma bestUniformApproxErrorAbs_le_explicit {K : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ K) :
    bestUniformApproxErrorAbs K ≤ uniformApproxErrorAbs p := by
  rw [bestUniformApproxErrorAbs_eq_sInf]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro e ⟨q, -, rfl⟩
    have h := ((uniformApproxErrorAbs_le_iff
      (p := q) (e := uniformApproxErrorAbs q)).mp (le_refl _)) 0 (by norm_num)
    exact (abs_nonneg _).trans h
  · exact ⟨p, hp, rfl⟩

/-- For [a positive polynomial degree](hyp:K,hK), [the best absolute-value approximation error is at most one divided by that degree](goal).

 Every positive degree admits an absolute-value approximating polynomial
with best error at most `1 / K`. -/
theorem bestUniformApproxErrorAbs_upper (K : ℕ) (hK : 0 < K) :
    bestUniformApproxErrorAbs K ≤ 1 / (K : ℝ) := by
  let m := K / 2
  have hmdeg : 2 * m ≤ K := by
    dsimp [m]
    omega
  calc
    bestUniformApproxErrorAbs K ≤ uniformApproxErrorAbs (absChebPoly m) :=
      bestUniformApproxErrorAbs_le_explicit (absChebPoly_natDegree_le m |>.trans hmdeg)
    _ ≤ 2 / (Real.pi * (2 * (m : ℝ) + 1)) := by
      apply uniformApproxErrorAbs_le_iff.mpr
      intro x hx
      exact absChebPoly_error_le m hx
    _ ≤ 1 / (K : ℝ) := by
      have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
      have hmreal : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
      have hnat : K ≤ 2 * m + 1 := by
        dsimp [m]
        omega
      have hnatreal : (K : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hnat
      have hprod : 2 * (K : ℝ) ≤ Real.pi * (2 * (m : ℝ) + 1) := calc
        2 * (K : ℝ) ≤ 2 * (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hnatreal (by norm_num)
        _ ≤ Real.pi * (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right Real.two_le_pi hmreal.le
      exact (div_le_div_iff₀ (mul_pos Real.pi_pos hmreal) hKreal).mpr (by
        simpa using hprod)

private lemma sinCircle_apply_eq_abs_sin (t : ℝ) :
    sinCircle (t : AddCircle Real.pi) = (|Real.sin t| : ℝ) := by
  obtain ⟨y, hy, heq⟩ := AddCircle.eq_coe_Ioc (t : AddCircle Real.pi)
  rw [← heq]
  change AddCircle.liftIoc Real.pi 0 (fun s : ℝ => (Real.sin s : ℂ))
      (y : AddCircle Real.pi) = _
  rw [AddCircle.liftIoc_coe_apply (by simpa using hy)]
  have hsin : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1.le hy.2
  rw [← abs_of_nonneg hsin]
  have hperiod : Function.Periodic (fun s : ℝ => |Real.sin s|) Real.pi := by
    intro s
    dsimp
    rw [Real.sin_add_pi]
    simp
  have he := congrArg hperiod.lift heq
  simpa only [Function.Periodic.lift_coe] using congrArg Complex.ofReal he

private noncomputable def doubleSinCircle : C(AddCircle Real.pi, ℂ) :=
  sinCircle.comp circleDouble

private lemma doubleSinCircle_apply (t : ℝ) :
    doubleSinCircle (t : AddCircle Real.pi) = (|Real.sin (2 * t)| : ℝ) := by
  change sinCircle (circleDouble (t : AddCircle Real.pi)) = _
  have hdouble : circleDouble (t : AddCircle Real.pi) =
      ((2 * t : ℝ) : AddCircle Real.pi) := by
    change 2 • (t : AddCircle Real.pi) = ((2 * t : ℝ) : AddCircle Real.pi)
    rw [← QuotientAddGroup.mk_nsmul]
    congr 1
    ring
  rw [hdouble]
  exact sinCircle_apply_eq_abs_sin (2 * t)

private lemma hasSum_doubleSinCircle_fourier :
    HasSum (fun i : ℤ =>
      fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) i • fourier (2 * i))
      doubleSinCircle := by
  have hs : HasSum (fun i : ℤ =>
      fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) i • fourier i) sinCircle :=
    hasSum_fourier_series_of_summable summable_fourierCoeff_sinCircle
  have hc := (ContinuousMap.compCLM ℂ ℂ circleDouble).hasSum hs
  convert hc using 1
  · funext i
    simp only [ContinuousMap.compCLM_apply]
    rw [← fourier_comp_circleDouble i]
    ext t
    rfl
  · rfl

private noncomputable def cuspTailTerm (n : ℕ) (hn : 0 < n) (k : ℕ) : ℝ :=
  -((cuspFunctionalCLM n hn
        (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (k : ℤ) • fourier (2 * (k : ℤ))) +
      cuspFunctionalCLM n hn
        (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (-(k : ℤ)) •
          fourier (-(2 * (k : ℤ))))).re)

private lemma hasSum_cuspTailTerm (n : ℕ) (hn : 0 < n) :
    HasSum (cuspTailTerm n hn) (-(cuspFunctionalCLM n hn doubleSinCircle).re) := by
  let L := cuspFunctionalCLM n hn
  let g : ℤ → ℂ := fun i => L
    (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) i • fourier (2 * i))
  have hs : HasSum g (L doubleSinCircle) := L.hasSum hasSum_doubleSinCircle_fourier
  have hzero : g 0 = 0 := by
    simp only [g, L, mul_zero, map_smul]
    rw [show cuspFunctionalCLM n hn (fourier 0) = 0 by
      simpa using cuspFunctional_fourier_nat n 0 hn (Nat.zero_le n)]
    simp
  have hp := hs.nat_add_neg
  have hr := Complex.reCLM.hasSum hp
  have hneg := hr.neg
  change HasSum (fun k : ℕ =>
    -((cuspFunctionalCLM n hn
          (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (k : ℤ) •
            fourier (2 * (k : ℤ))) +
        cuspFunctionalCLM n hn
          (fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (-(k : ℤ)) •
            fourier (-(2 * (k : ℤ))))).re)) _
  simpa only [g, L, Function.comp_apply, map_add, Complex.add_re,
    Complex.reCLM_apply, Complex.neg_re, hzero, Complex.zero_re, add_zero, neg_add_rev, neg_neg,
    Int.cast_natCast, Int.cast_neg, mul_neg, neg_mul] using hneg

private lemma cuspTailTerm_nonneg (n : ℕ) (hn : 0 < n) (k : ℕ) :
    0 ≤ cuspTailTerm n hn k := by
  rcases k with _ | k
  · simp only [cuspTailTerm, Nat.cast_zero, mul_zero, neg_zero,
      map_smul]
    rw [show cuspFunctionalCLM n hn (fourier 0) = 0 by
      simpa using cuspFunctional_fourier_nat n 0 hn (Nat.zero_le n)]
    simp
  · have hkone : (1 : ℝ) ≤ (k + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hden : 0 < Real.pi * (4 * ((k + 1 : ℕ) : ℝ) ^ 2 - 1) := by
      apply mul_pos Real.pi_pos
      nlinarith [sq_nonneg (((k + 1 : ℕ) : ℝ) - 1)]
    let c : ℝ := (-2 : ℝ) / (Real.pi * (4 * ((k + 1 : ℕ) : ℝ) ^ 2 - 1))
    have hc : c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le
    have hp := cuspFunctional_fourier_nat_nonneg n (2 * (k + 1)) hn
    have hm := cuspFunctional_fourier_neg_nat_nonneg n (2 * (k + 1)) hn
    have hcoeff : fourierCoeff (sinCircle : AddCircle Real.pi → ℂ)
        (((k + 1 : ℕ) : ℤ)) = (c : ℂ) := by
      rw [fourierCoeff_sinCircle]
      dsimp [c]
      push_cast
      rfl
    have hcoeffneg : fourierCoeff (sinCircle : AddCircle Real.pi → ℂ)
        (-(((k + 1 : ℕ) : ℤ))) = (c : ℂ) := by
      rw [fourierCoeff_sinCircle]
      dsimp [c]
      push_cast
      congr 2
      ring
    rw [cuspTailTerm, map_smul, map_smul, hcoeff, hcoeffneg]
    simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact neg_nonneg.mpr (add_nonpos (mul_nonpos_of_nonpos_of_nonneg hc hp)
      (mul_nonpos_of_nonpos_of_nonneg hc hm))

private lemma cuspTailTerm_block_lower (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hnk : n ≤ k) (hkn : k < 2 * n) :
    1 / (16 * (n : ℝ) ^ 2) ≤ cuspTailTerm n hn k := by
  have hkpos : 0 < k := hn.trans_le hnk
  let c : ℝ := (-2 : ℝ) / (Real.pi * (4 * (k : ℝ) ^ 2 - 1))
  have hcoeff : fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (k : ℤ) =
      (c : ℂ) := by
    rw [fourierCoeff_sinCircle]
    dsimp [c]
    push_cast
    rfl
  have hcoeffneg : fourierCoeff (sinCircle : AddCircle Real.pi → ℂ) (-(k : ℤ)) =
      (c : ℂ) := by
    rw [fourierCoeff_sinCircle]
    dsimp [c]
    push_cast
    congr 2
    ring
  have hhigh : cuspFunctionalCLM n hn (fourier (2 * (k : ℤ))) = 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      cuspFunctional_fourier_nat_high n (2 * k) hn (by omega)
  have hhighneg : cuspFunctionalCLM n hn (fourier (-(2 * (k : ℤ)))) = 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      cuspFunctional_fourier_neg_nat_high n (2 * k) hn (by omega)
  have hterm : cuspTailTerm n hn k = 4 / (Real.pi * (4 * (k : ℝ) ^ 2 - 1)) := by
    rw [cuspTailTerm, map_smul, map_smul, hcoeff, hcoeffneg, hhigh, hhighneg]
    simp only [smul_eq_mul, mul_one, Complex.add_re, Complex.ofReal_re]
    dsimp [c]
    ring
  rw [hterm]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hknR : (k : ℝ) < 2 * n := by exact_mod_cast hkn
  have hfactor : 0 < 4 * (k : ℝ) ^ 2 - 1 := by
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hden : 0 < Real.pi * (4 * (k : ℝ) ^ 2 - 1) :=
    mul_pos Real.pi_pos hfactor
  have hleft : 0 < 16 * (n : ℝ) ^ 2 := by positivity
  apply (div_le_div_iff₀ hleft hden).2
  have hksq : (k : ℝ) ^ 2 < 4 * (n : ℝ) ^ 2 := by nlinarith
  calc
    1 * (Real.pi * (4 * (k : ℝ) ^ 2 - 1)) ≤
        4 * (4 * (k : ℝ) ^ 2 - 1) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right Real.pi_le_four hfactor.le
    _ ≤ 4 * (4 * (k : ℝ) ^ 2) := by nlinarith
    _ ≤ 4 * (16 * (n : ℝ) ^ 2) := by nlinarith

private lemma cuspFunctional_doubleSinCircle_lower (n : ℕ) (hn : 0 < n) :
    1 / (16 * (n : ℝ)) ≤ -(cuspFunctionalCLM n hn doubleSinCircle).re := by
  have hs := hasSum_cuspTailTerm n hn
  have hsum_le : ∑ k ∈ Finset.Ico n (2 * n), cuspTailTerm n hn k ≤
      -(cuspFunctionalCLM n hn doubleSinCircle).re := by
    have hle := hs.summable.sum_le_tsum (Finset.Ico n (2 * n))
      (fun k _ => cuspTailTerm_nonneg n hn k)
    rwa [hs.tsum_eq] at hle
  calc
    1 / (16 * (n : ℝ)) =
        ∑ _k ∈ Finset.Ico n (2 * n), 1 / (16 * (n : ℝ) ^ 2) := by
          simp only [Finset.sum_const, Nat.card_Ico]
          rw [show 2 * n - n = n by omega]
          rw [nsmul_eq_mul]
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
          change 1 / (16 * (n : ℝ)) =
            (n : ℝ) * (1 / (16 * (n : ℝ) ^ 2))
          field_simp [hnR]
    _ ≤ ∑ k ∈ Finset.Ico n (2 * n), cuspTailTerm n hn k := by
      apply Finset.sum_le_sum
      intro k hk
      exact cuspTailTerm_block_lower n hn k (Finset.mem_Ico.mp hk).1
        (Finset.mem_Ico.mp hk).2
    _ ≤ -(cuspFunctionalCLM n hn doubleSinCircle).re := hsum_le

/-- For [a positive polynomial degree](hyp:K,hK), [the cusp of absolute value forces the stated inverse-degree lower bound](goal).

 The cusp at zero forces every positive-degree polynomial approximation of
absolute value to incur error at least `(1/100) / K`. -/
theorem bestUniformApproxErrorAbs_lower (K : ℕ) (hK : 0 < K) :
    (1 / 100 : ℝ) / (K : ℝ) ≤ bestUniformApproxErrorAbs K := by
  -- Symmetrizing a best approximant and using only a Markov derivative bound
  -- gives `K⁻²`, so a genuine inverse estimate is needed.  A concrete route
  -- is the de la Vallée--Poussin certificate on `AddCircle Real.pi`.  For the
  -- normalized Fejér kernel `F_n(t) = n⁻¹ * ‖∑_{r < n} fourier r t‖²`, the
  -- kernel `V_n = 2 * F_(2*n) - F_n` has `L¹` norm at most `3` and Fourier
  -- multiplier exactly `1` on `|j| ≤ n`.  Evaluation at the cusp minus
  -- convolution with `V_n` therefore has norm at most `4` and annihilates
  -- every even polynomial mode of degree at most `2*n`.  The formula
  -- `fourierCoeff_sinCircle` makes its value on `|sin|` a positive tail;
  -- retaining only `2*n ≤ j < 4*n` gives a constant-over-`n` lower bound.
  -- Reduce odd `K` with `bestUniformApproxErrorAbs_two_mul_add_one`.
  -- Do not replace this with a coefficient-at-one-frequency estimate or with
  -- two shifted uniform grids: both give only `K⁻²` for `|cos|`.
  obtain ⟨p, hpdeg, hpbest⟩ := exists_bestPolynomialAbs K
  obtain ⟨q, hqeval, hqann⟩ := exists_fourierPoly_sinDouble p K hK hpdeg
  let residual : C(AddCircle Real.pi, ℂ) := doubleSinCircle - q
  have hresidual_norm : ‖residual‖ ≤ uniformApproxErrorAbs p := by
    apply (ContinuousMap.norm_le_of_nonempty _).mpr
    intro z
    obtain ⟨t, ht, heq⟩ := AddCircle.eq_coe_Ioc z
    rw [← heq]
    change ‖doubleSinCircle (t : AddCircle Real.pi) - q (t : AddCircle Real.pi)‖ ≤ _
    rw [doubleSinCircle_apply, hqeval]
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact ((uniformApproxErrorAbs_le_iff (p := p) (e := uniformApproxErrorAbs p)).mp
      (le_refl _)) (Real.sin (2 * t)) ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hfunctional_residual : cuspFunctionalCLM K hK residual =
      cuspFunctionalCLM K hK doubleSinCircle := by
    simp only [residual, map_sub, hqann, sub_zero]
  have hcertificate : 1 / (16 * (K : ℝ)) ≤
      ‖cuspFunctionalCLM K hK residual‖ := by
    calc
      1 / (16 * (K : ℝ)) ≤ -(cuspFunctionalCLM K hK doubleSinCircle).re :=
        cuspFunctional_doubleSinCircle_lower K hK
      _ ≤ |-(cuspFunctionalCLM K hK doubleSinCircle).re| := le_abs_self _
      _ = |(cuspFunctionalCLM K hK doubleSinCircle).re| := abs_neg _
      _ ≤ ‖cuspFunctionalCLM K hK doubleSinCircle‖ := Complex.abs_re_le_norm _
      _ = ‖cuspFunctionalCLM K hK residual‖ := by rw [hfunctional_residual]
  have herror : 1 / (16 * (K : ℝ)) ≤ 4 * uniformApproxErrorAbs p :=
    hcertificate.trans ((cuspFunctional_norm_apply_le K hK residual).trans
      (mul_le_mul_of_nonneg_left hresidual_norm (by norm_num)))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have h64 : 1 / (64 * (K : ℝ)) ≤ uniformApproxErrorAbs p := by
    have hid : 1 / (64 * (K : ℝ)) = (1 / (16 * (K : ℝ))) / 4 := by
      field_simp
      ring
    rw [hid]
    linarith
  rw [← hpbest]
  exact (by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (100 : ℝ) * K)
      (by positivity : 0 < (64 : ℝ) * K)).2
    nlinarith : (1 / 100 : ℝ) / K ≤ 1 / (64 * K)).trans h64

/-- [There are universal positive constants](goal) that sandwich the best absolute-value approximation error between constant multiples of the reciprocal degree for every positive degree.

 Universal positive constants sandwich the best approximation error between
constant multiples of `1 / K` for every positive degree. -/
theorem bestUniformApproxErrorAbs_order :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ K : ℕ, 0 < K →
        c / (K : ℝ) ≤ bestUniformApproxErrorAbs K ∧
        bestUniformApproxErrorAbs K ≤ C / (K : ℝ) := by
  refine ⟨1 / 100, 1, by norm_num, by norm_num, ?_⟩
  intro K hK
  exact ⟨bestUniformApproxErrorAbs_lower K hK,
    bestUniformApproxErrorAbs_upper K hK⟩

end

end Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

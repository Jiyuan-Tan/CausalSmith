/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.TailBounds.Bernstein
public import Causalean.Tactic.IntegralLinearity

/-!
# Sharp Bernstein inequality for independent bounded summands

This module proves the denominator-form centered MGF bound of
Boucheron--Lugosi--Massart, Lemma 2.9, and optimizes it for independent summands. Unlike the
constant-parameter sub-exponential proxy in `Bernstein`, the resulting upper tail has the textbook
constant `exp (-n * ε² / (2 * (σ² + bε/3)))`.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real Finset

private lemma exp_le_quadratic_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  set y := -x
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hseries := Real.sum_le_exp_of_nonneg hy 3
  have hpoly : 1 + y + y ^ 2 / 2 ≤ Real.exp y := by
    convert hseries using 1
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : 0 < 1 + y + y ^ 2 / 2 := by positivity
  have hinv : (Real.exp y)⁻¹ ≤ (1 + y + y ^ 2 / 2)⁻¹ :=
    inv_anti₀ hpos hpoly
  rw [← Real.exp_neg] at hinv
  have hprod : 1 ≤ (1 + y + y ^ 2 / 2) * (1 - y + y ^ 2 / 2) := by
    nlinarith [sq_nonneg (y ^ 2)]
  have hquad : (1 + y + y ^ 2 / 2)⁻¹ ≤ 1 - y + y ^ 2 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    simpa [mul_comm] using hprod
  simpa [y] using hinv.trans hquad

private lemma exp_le_bernstein_series {x : ℝ} (hx : 0 ≤ x) (hx3 : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  have hdenpos : 0 < 1 - x / 3 := by linarith
  have hr : |x / 3| < 1 := by
    rw [abs_of_nonneg (div_nonneg hx (by norm_num))]
    linarith
  have hrnorm : ‖x / 3‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact hr
  have hg0 : Summable (fun j : ℕ => (x / 3) ^ j) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hgeom : Summable (fun j : ℕ => x ^ 2 / 2 * (x / 3) ^ j) :=
    Summable.mul_left _ hg0
  have hterm (j : ℕ) :
      x ^ (j + 2) / ((j + 2).factorial : ℝ) ≤ x ^ 2 / 2 * (x / 3) ^ j := by
    have hfac : 2 * 3 ^ j ≤ (j + 2).factorial := by
      simpa [add_comm] using (Nat.factorial_mul_pow_le_factorial (m := 2) (n := j))
    have hfacR : (2 * 3 ^ j : ℝ) ≤ ((j + 2).factorial : ℝ) := by exact_mod_cast hfac
    have hden : (0 : ℝ) < ((j + 2).factorial : ℝ) := by positivity
    have hsmall : (0 : ℝ) < 2 * 3 ^ j := by positivity
    have heq : x ^ 2 / 2 * (x / 3) ^ j = x ^ (j + 2) / (2 * 3 ^ j) := by
      rw [div_pow]
      field_simp
      ring
    rw [heq]
    exact (div_le_div_iff₀ hden hsmall).2
      (mul_le_mul_of_nonneg_left hfacR (pow_nonneg hx _))
  have hexpSumm := Real.summable_pow_div_factorial x
  have htail : (∑' j : ℕ, x ^ (j + 2) / ((j + 2).factorial : ℝ)) ≤
      ∑' j : ℕ, x ^ 2 / 2 * (x / 3) ^ j :=
    ((summable_nat_add_iff 2).2 hexpSumm).tsum_le_tsum hterm hgeom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr] at htail
  have htail' : (∑' j : ℕ, x ^ (j + 2) / ((j + 2).factorial : ℝ)) ≤
      x ^ 2 / (2 * (1 - x / 3)) := by
    calc
      _ ≤ x ^ 2 / 2 * (1 - x / 3)⁻¹ := htail
      _ = _ := by field_simp [ne_of_gt hdenpos]
  have hsplit := hexpSumm.sum_add_tsum_nat_add 2
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change (∑' i : ℕ, x ^ i / (i.factorial : ℝ)) ≤ _
  rw [← hsplit]
  norm_num [Finset.sum_range_succ, Nat.factorial]
  simpa [Nat.factorial_succ] using htail'

private lemma exp_le_bernstein_quadratic {x u : ℝ} (hu : 0 ≤ u) (hu3 : u < 3)
    (hxu : x ≤ u) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - u / 3)) := by
  have hdu : 0 < 1 - u / 3 := by linarith
  rcases le_total x 0 with hx | hx
  · refine (exp_le_quadratic_of_nonpos hx).trans ?_
    have hcoef : x ^ 2 / 2 ≤ x ^ 2 / (2 * (1 - u / 3)) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (mul_pos (by norm_num) hdu)]
      nlinarith [sq_nonneg x]
    linarith
  · refine (exp_le_bernstein_series hx (lt_of_le_of_lt hxu hu3)).trans ?_
    have hcoef : x ^ 2 / (2 * (1 - x / 3)) ≤
        x ^ 2 / (2 * (1 - u / 3)) := by
      gcongr
    linarith

/-- **Centered bounded-summand MGF bound (Boucheron--Lugosi--Massart, Lemma 2.9).**
For [a probability law](hyp:μ), [an a.e.-measurable summand](hyp:hXmeas) that is
[integrable with integrable square](hyp:hXint,hXsqint), [mean zero](hyp:hmean), [bounded above by
`b` almost everywhere](hyp:hupper), and has [second moment at most `v`](hyp:hsecond), if [the
envelope is nonnegative](hyp:hb), [the MGF argument is nonnegative](hyp:hlam), and
[`lam*b < 3`](hyp:hlamb), then [the MGF is at most
`exp (lam² v / (2(1-lam*b/3)))`](goal). -/
theorem centered_bounded_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b v lam : ℝ}
    (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hlamb : lam * b < 3)
    (hXmeas : AEMeasurable X μ) (hXint : Integrable X μ)
    (hXsqint : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (hupper : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ ≤ v) :
    mgf X μ lam ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3))) := by
  have hden : 0 < 2 * (1 - lam * b / 3) := by linarith
  have hexpint : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * b)))
      ((Real.measurable_exp.comp_aemeasurable
        (hXmeas.const_mul lam)).aestronglyMeasurable) ?_
    filter_upwards [hupper] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hlam)
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (lam * X ω) ≤
      1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3)) := by
    filter_upwards [hupper] with ω hω
    exact exp_le_bernstein_quadratic (mul_nonneg hlam hb) hlamb
      (mul_le_mul_of_nonneg_left hω hlam)
  have hsqint : Integrable
      (fun ω => (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3))) μ := by
    have h := hXsqint.const_mul (lam ^ 2 / (2 * (1 - lam * b / 3)))
    exact h.congr (ae_of_all _ fun ω => by ring)
  have hrhsint : Integrable
      (fun ω => 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3))) μ :=
    ((integrable_const 1).add (hXint.const_mul lam)).add hsqint
  have hint := integral_mono_ae hexpint hrhsint hpoint
  have heqfun : ∀ ω, 1 + lam * X ω +
      (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3)) =
      1 + lam * X ω + (lam ^ 2 / (2 * (1 - lam * b / 3))) * X ω ^ 2 := by
    intro ω
    ring
  have heval : (∫ ω, 1 + lam * X ω +
      (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3)) ∂μ) =
      1 + lam ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / (2 * (1 - lam * b / 3)) := by
    rw [integral_congr_ae (ae_of_all _ heqfun)]
    integral_linearity
    rw [hmean]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
    ring
  change (∫ ω, Real.exp (lam * X ω) ∂μ) ≤ _
  calc
    (∫ ω, Real.exp (lam * X ω) ∂μ) ≤
        1 + lam ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / (2 * (1 - lam * b / 3)) :=
      hint.trans_eq heval
    _ ≤ 1 + lam ^ 2 * v / (2 * (1 - lam * b / 3)) := by gcongr
    _ ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * b / 3))) := by
      simpa [add_comm] using Real.add_one_le_exp
        (lam ^ 2 * v / (2 * (1 - lam * b / 3)))

/-- **Sharp Bernstein inequality for independent centered summands.** Given [a positive number of
summands](hyp:hn), [independent measurable summands](hyp:hindep,hmeas) that are [integrable with
integrable squares](hyp:hint,hsqint), [centered](hyp:hmean), [bounded above by the nonnegative
envelope `b`](hyp:hb,hupper), and have [second moments at most the positive proxy
`σ²`](hyp:hsigma2,hsecond), then for [a nonnegative deviation `ε`](hyp:heps), [their sum exceeds
`nε` with probability at most `exp (-nε²/(2(σ²+bε/3)))`](goal). -/
theorem bernstein_sum_ge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {b sigma2 eps : ℝ}
    (hb : 0 ≤ b) (hsigma2 : 0 < sigma2) (heps : 0 ≤ eps)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hsqint : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hupper : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ ≤ sigma2) :
    μ.real {ω | (n : ℝ) * eps ≤ ∑ i, X i ω} ≤
      Real.exp (-(n : ℝ) * eps ^ 2 / (2 * (sigma2 + b * eps / 3))) := by
  classical
  set d : ℝ := sigma2 + b * eps / 3 with hd
  have hdpos : 0 < d := by dsimp [d]; positivity
  set t : ℝ := eps / d with ht
  have ht0 : 0 ≤ t := div_nonneg heps hdpos.le
  have htb : t * b < 3 := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hdpos]
    nlinarith [mul_nonneg hb heps]
  have hexp (i : Fin n) : Integrable (fun ω => Real.exp (t * X i ω)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (t * b)))
      ((Real.measurable_exp.comp ((hmeas i).const_mul t)).aestronglyMeasurable) ?_
    filter_upwards [hupper i] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω ht0)
  have hmgfi (i : Fin n) :
      mgf (X i) μ t ≤ Real.exp (t ^ 2 * sigma2 / (2 * (1 - t * b / 3))) :=
    centered_bounded_mgf_le hb ht0 htb (hmeas i).aemeasurable (hint i) (hsqint i)
      (hmean i) (hupper i) (hsecond i)
  have hmgfsum : mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp ((n : ℝ) * (t ^ 2 * sigma2 / (2 * (1 - t * b / 3)))) := by
    simp only [← Finset.sum_apply]
    rw [hindep.mgf_sum hmeas Finset.univ]
    calc
      ∏ i : Fin n, mgf (X i) μ t ≤
          ∏ _i : Fin n, Real.exp (t ^ 2 * sigma2 / (2 * (1 - t * b / 3))) := by
            apply Finset.prod_le_prod
            · intro _i _
              exact mgf_nonneg
            · intro i _
              exact hmgfi i
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hsumint : Integrable (fun ω => Real.exp (t * (∑ i, X i ω))) μ := by
    simp only [← Finset.sum_apply]
    exact hindep.integrable_exp_mul_sum hmeas (s := Finset.univ) (fun i _ => hexp i)
  have hchernoff := measure_ge_le_exp_mul_mgf ((n : ℝ) * eps) ht0 hsumint
  calc
    μ.real {ω | (n : ℝ) * eps ≤ ∑ i, X i ω} ≤
        Real.exp (-t * ((n : ℝ) * eps)) * mgf (fun ω => ∑ i, X i ω) μ t := hchernoff
    _ ≤ Real.exp (-t * ((n : ℝ) * eps)) *
        Real.exp ((n : ℝ) * (t ^ 2 * sigma2 / (2 * (1 - t * b / 3)))) :=
      mul_le_mul_of_nonneg_left hmgfsum (Real.exp_pos _).le
    _ = Real.exp (-t * ((n : ℝ) * eps) +
        (n : ℝ) * (t ^ 2 * sigma2 / (2 * (1 - t * b / 3)))) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ) * eps ^ 2 / (2 * (sigma2 + b * eps / 3))) := by
      apply (Real.exp_le_exp).2
      rw [ht, hd]
      field_simp [ne_of_gt hsigma2]
      nlinarith

end Causalean.Stat.Concentration

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.Basic
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Analytic ingredients for Bousquet's inequality

This file proves the signed-increment estimates at the heart of Bousquet's variance-sensitive
concentration inequality for empirical-process suprema: Boucheron--Lugosi--Massart (2013),
Lemma 12.6, the conditional half-square consequence of Lemma 11.11, and the resulting
one-coordinate tilted Bennett-cost estimate used in Lemma 12.8.
-/

@[expose] public section

open Filter Real Set
open scoped Topology

namespace Causalean.Stat.Concentration.EntropyMethod

/-- For [a real argument `x`](hyp:x), [the Bennett entropy function](goal) is
`exp x - x - 1`. -/
noncomputable def blmPhi (x : ℝ) : ℝ := Real.exp x - x - 1

private lemma exp_sub_one_sq_ge (y : ℝ) :
    y ^ 2 * Real.exp y ≤ (Real.exp y - 1) ^ 2 := by
  have habs : |y / 2| ≤ |Real.sinh (y / 2)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hsq : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    exact sq_le_sq.mpr habs
  have hexp : 0 < Real.exp (y / 2) := Real.exp_pos _
  rw [Real.sinh_eq] at hsq
  have he : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hident :
      (Real.exp y - 1) ^ 2 =
        4 * Real.exp y * (((Real.exp (y / 2) - Real.exp (-(y / 2))) / 2) ^ 2) := by
    rw [show Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) by
      rw [← Real.exp_add]
      congr 1 <;> ring]
    nlinarith
  rw [hident]
  have hscaled := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos y).le)
  nlinarith

private lemma mul_q_nonneg (y : ℝ) :
    0 ≤ y * (Real.exp y * (y ^ 2 - 2 * y + 2) - 2) := by
  let q : ℝ → ℝ := fun z => Real.exp z * (z ^ 2 - 2 * z + 2) - 2
  have hqdiff : Differentiable ℝ q := by
    intro z
    dsimp [q]
    fun_prop
  have hqderiv : ∀ z, deriv q z = z ^ 2 * Real.exp z := by
    intro z
    have h := ((Real.hasDerivAt_exp z).mul
      (((hasDerivAt_id z).pow 2).sub ((hasDerivAt_id z).const_mul 2) |>.add_const 2)).sub_const 2
    have h' : HasDerivAt (fun z => Real.exp z * (z ^ 2 - 2 * z + 2) - 2)
        (z ^ 2 * Real.exp z) z := by
      have h0 : HasDerivAt (fun z => Real.exp z * (z ^ 2 - 2 * z + 2) - 2)
          (Real.exp z * (z ^ 2 - 2 * z + 2) +
            Real.exp z * (2 * z * 1 - 2 * 1)) z := by
        simpa only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq,
          Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul] using h
      convert h0 using 1
      ring
    exact h'.deriv
  have hqmono : Monotone q := monotone_of_deriv_nonneg hqdiff (fun z => by
    rw [hqderiv]
    positivity)
  have hq0 : q 0 = 0 := by simp [q]
  rcases le_total y 0 with hy | hy
  · have : q y ≤ 0 := by simpa [hq0] using hqmono hy
    exact mul_nonneg_of_nonpos_of_nonpos hy this
  · have : 0 ≤ q y := by simpa [hq0] using hqmono hy
    exact mul_nonneg hy this

private lemma ratio_deriv_numerator_nonneg
    {lam beta x : ℝ} (hlam : 0 ≤ lam) (hbeta : 0 ≤ beta) :
    0 ≤
      (lam ^ 2 * x * Real.exp (lam * x)) *
          (x * Real.exp (lam * x) + beta * x ^ 2 - x) -
        (lam * x * Real.exp (lam * x) - Real.exp (lam * x) + 1) *
          (Real.exp (lam * x) * (1 + lam * x) + 2 * beta * x - 1) := by
  let y := lam * x
  have hbase := exp_sub_one_sq_ge y
  have hq := mul_q_nonneg y
  have hbetaxq : 0 ≤ beta * x *
      (Real.exp y * (y ^ 2 - 2 * y + 2) - 2) := by
    have hxy : 0 ≤ x * (Real.exp y * (y ^ 2 - 2 * y + 2) - 2) := by
      rcases eq_or_lt_of_le hlam with rfl | hlam'
      · simp [y]
      · have : x = y / lam := by dsimp [y]; field_simp
        rw [this]
        simpa [div_mul_eq_mul_div, mul_assoc] using div_nonneg hq hlam'.le
    rw [mul_assoc]
    exact mul_nonneg hbeta hxy
  dsimp [y] at hbase hbetaxq ⊢
  nlinarith

private lemma blm_g_pos {lam beta x : ℝ} (hlam : 0 < lam) (hbeta : 0 ≤ beta)
    (hx : x ≠ 0) :
    0 < x * Real.exp (lam * x) + beta * x ^ 2 - x := by
  have hprod : 0 < x * (Real.exp (lam * x) - 1) := by
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hy : lam * x < 0 := mul_neg_of_pos_of_neg hlam hxneg
      have he : Real.exp (lam * x) < 1 := Real.exp_lt_one_iff.mpr hy
      exact mul_pos_of_neg_of_neg hxneg (sub_neg.mpr he)
    · have hy : 0 < lam * x := mul_pos hlam hxpos
      have he : 1 < Real.exp (lam * x) := Real.one_lt_exp_iff.mpr hy
      exact mul_pos hxpos (sub_pos.mpr he)
  have hbetaSq : 0 ≤ beta * x ^ 2 := mul_nonneg hbeta (sq_nonneg x)
  nlinarith

private lemma blm_g_deriv_mul_pos {lam beta x : ℝ} (hlam : 0 < lam)
    (hbeta : 0 ≤ beta) (hx : x ≠ 0) :
    0 < x * (Real.exp (lam * x) * (1 + lam * x) + 2 * beta * x - 1) := by
  have hprod : 0 < x * (Real.exp (lam * x) - 1) := by
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hy : lam * x < 0 := mul_neg_of_pos_of_neg hlam hxneg
      exact mul_pos_of_neg_of_neg hxneg (sub_neg.mpr (Real.exp_lt_one_iff.mpr hy))
    · have hy : 0 < lam * x := mul_pos hlam hxpos
      exact mul_pos hxpos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hy))
  have hsquare : 0 ≤ x ^ 2 * (lam * Real.exp (lam * x) + 2 * beta) := by
    positivity
  nlinarith

/-- **BLM Lemma 12.6.** If [the quadratic coefficient `beta` is nonnegative](hyp:hbeta),
[the tilt `lam` is nonnegative](hyp:hlam), and [the signed increment `x` is at most
one](hyp:hx), then [the Bennett entropy ratio at `-lam*x` is bounded by the signed affine-
quadratic exponential ratio](goal). -/
theorem blm_phi_signed_increment_le {beta lam x : ℝ}
    (hbeta : 0 ≤ beta) (hlam : 0 ≤ lam) (hx : x ≤ 1) :
    blmPhi (-lam * x) / blmPhi (-lam) ≤
      (x + (beta * x ^ 2 - x) * Real.exp (-lam * x)) /
        (1 + (beta - 1) * Real.exp (-lam)) := by
  rcases eq_or_lt_of_le hlam with rfl | hlam
  · by_cases hbzero : beta = 0
    · simp [blmPhi, hbzero]
    · simp only [blmPhi, zero_mul, neg_zero, Real.exp_zero, sub_zero,
        sub_self, zero_div, one_mul, add_zero]
      rw [div_nonneg_iff]
      exact Or.inl ⟨by nlinarith [mul_nonneg hbeta (sq_nonneg x)], by nlinarith⟩
  let f : ℝ → ℝ := fun z =>
    lam * z * Real.exp (lam * z) - Real.exp (lam * z) + 1
  let g : ℝ → ℝ := fun z =>
    z * Real.exp (lam * z) + beta * z ^ 2 - z
  let fp : ℝ → ℝ := fun z => lam ^ 2 * z * Real.exp (lam * z)
  let gp : ℝ → ℝ := fun z =>
    Real.exp (lam * z) * (1 + lam * z) + 2 * beta * z - 1
  let fpp : ℝ → ℝ := fun z => lam ^ 2 * Real.exp (lam * z) * (1 + lam * z)
  let gpp : ℝ → ℝ := fun z =>
    lam * Real.exp (lam * z) * (2 + lam * z) + 2 * beta
  let L : ℝ := lam ^ 2 / (2 * (beta + lam))
  let rho : ℝ → ℝ := Function.update (fun z => f z / g z) 0 L
  have hf_deriv (z : ℝ) : HasDerivAt f (fp z) z := by
    dsimp [f, fp]
    apply ((((hasDerivAt_const z lam).mul (hasDerivAt_id z)).mul
      ((Real.hasDerivAt_exp (lam * z)).comp z
        ((hasDerivAt_const z lam).mul (hasDerivAt_id z)))).sub
      ((Real.hasDerivAt_exp (lam * z)).comp z
        ((hasDerivAt_const z lam).mul (hasDerivAt_id z))) |>.add_const 1).congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  have hg_deriv (z : ℝ) : HasDerivAt g (gp z) z := by
    dsimp [g, gp]
    apply ((((hasDerivAt_id z).mul
      ((Real.hasDerivAt_exp (lam * z)).comp z
        ((hasDerivAt_const z lam).mul (hasDerivAt_id z)))).add
      ((hasDerivAt_const z beta).mul ((hasDerivAt_id z).pow 2))).sub
        (hasDerivAt_id z)).congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  have hfp_deriv (z : ℝ) : HasDerivAt fp (fpp z) z := by
    dsimp [fp, fpp]
    apply (((hasDerivAt_const z (lam ^ 2)).mul (hasDerivAt_id z)).mul
      ((Real.hasDerivAt_exp (lam * z)).comp z
        ((hasDerivAt_const z lam).mul (hasDerivAt_id z)))).congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  have hgp_deriv (z : ℝ) : HasDerivAt gp (gpp z) z := by
    dsimp [gp, gpp]
    apply (((((Real.hasDerivAt_exp (lam * z)).comp z
      ((hasDerivAt_const z lam).mul (hasDerivAt_id z))).mul
      ((hasDerivAt_const z 1).add
        ((hasDerivAt_const z lam).mul (hasDerivAt_id z)))).add
      ((hasDerivAt_const z (2 * beta)).mul (hasDerivAt_id z))).sub_const 1).congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, id_eq]
    ring
  have hgp_ne (z : ℝ) (hz : z ≠ 0) : gp z ≠ 0 := by
    have h := blm_g_deriv_mul_pos hlam hbeta hz
    intro hzero
    dsimp [gp] at hzero
    rw [hzero] at h
    simp at h
  have hf0 : f 0 = 0 := by simp [f]
  have hg0 : g 0 = 0 := by simp [g]
  have hfp0 : fp 0 = 0 := by simp [fp]
  have hgp0 : gp 0 = 0 := by simp [gp]
  have hden : 0 < 2 * (beta + lam) := by positivity
  have hsecondLimit : Tendsto (fun z => fpp z / gpp z) (𝓝 0) (𝓝 L) := by
    have hfpp : Tendsto fpp (𝓝 0) (𝓝 (lam ^ 2)) := by
      have h : ContinuousAt fpp 0 := by dsimp [fpp]; fun_prop
      simpa [fpp] using h.tendsto
    have hgpp : Tendsto gpp (𝓝 0) (𝓝 (2 * (beta + lam))) := by
      have h : ContinuousAt gpp 0 := by dsimp [gpp]; fun_prop
      convert h.tendsto using 1 <;> simp [gpp] <;> ring
    change Tendsto (fpp / gpp) (𝓝 0) (𝓝 L)
    simpa only [L] using hfpp.div hgpp hden.ne'
  have hgpp_ne_event : ∀ᶠ z in 𝓝[≠] 0, gpp z ≠ 0 := by
    have hcont : ContinuousAt gpp 0 := by dsimp [gpp]; fun_prop
    have hgpp0 : 0 < gpp 0 := by simp [gpp]; positivity
    have hev : ∀ᶠ z in 𝓝 0, 0 < gpp z :=
      hcont.tendsto.eventually (Ioi_mem_nhds hgpp0)
    exact (hev.filter_mono inf_le_left).mono fun z hz => hz.ne'
  have hfirstLimit : Tendsto (fun z => fp z / gp z) (𝓝[≠] 0) (𝓝 L) := by
    apply HasDerivAt.lhopital_zero_nhdsNE (f' := fpp) (g' := gpp)
    · exact eventually_nhdsWithin_of_forall fun z _ => hfp_deriv z
    · exact eventually_nhdsWithin_of_forall fun z _ => hgp_deriv z
    · exact hgpp_ne_event
    · have h := (hfp_deriv 0).continuousAt.tendsto
      rw [hfp0] at h
      exact h.mono_left inf_le_left
    · have h := (hgp_deriv 0).continuousAt.tendsto
      rw [hgp0] at h
      exact h.mono_left inf_le_left
    · exact hsecondLimit.mono_left inf_le_left
  have hratioLimit : Tendsto (fun z => f z / g z) (𝓝[≠] 0) (𝓝 L) := by
    apply HasDerivAt.lhopital_zero_nhdsNE (f' := fp) (g' := gp)
    · exact eventually_nhdsWithin_of_forall fun z _ => hf_deriv z
    · exact eventually_nhdsWithin_of_forall fun z _ => hg_deriv z
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hgp_ne z hz
    · have h := (hf_deriv 0).continuousAt.tendsto
      rw [hf0] at h
      exact h.mono_left inf_le_left
    · have h := (hg_deriv 0).continuousAt.tendsto
      rw [hg0] at h
      exact h.mono_left inf_le_left
    · exact hfirstLimit
  have hrho_cont : Continuous rho := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst z
      change ContinuousAt (Function.update (fun z => f z / g z) 0 L) 0
      rw [continuousAt_update_same]
      exact hratioLimit
    · have hbase : ContinuousAt (fun w => f w / g w) z :=
        (hf_deriv z).continuousAt.div (hg_deriv z).continuousAt (blm_g_pos hlam hbeta hz).ne'
      apply hbase.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [rho, hw]
  have hrho_deriv (z : ℝ) (hz : z ≠ 0) : HasDerivAt rho
      ((fp z * g z - f z * gp z) / g z ^ 2) z := by
    have hbase : HasDerivAt (fun w => f w / g w)
        ((fp z * g z - f z * gp z) / g z ^ 2) z :=
      (hf_deriv z).div (hg_deriv z) (blm_g_pos hlam hbeta hz).ne'
    have heq : rho =ᶠ[𝓝 z] fun w => f w / g w := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [rho, hw]
    exact hbase.congr_of_eventuallyEq heq
  have hrho_deriv_nonneg (z : ℝ) (hz : z ≠ 0) : 0 ≤ deriv rho z := by
    rw [(hrho_deriv z hz).deriv]
    exact div_nonneg (by
      dsimp [fp, g, f, gp]
      exact ratio_deriv_numerator_nonneg hlam.le hbeta) (sq_nonneg _)
  have hmonoNeg : MonotoneOn rho (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hrho_cont.continuousOn
    · intro z hz
      exact (hrho_deriv z (ne_of_lt (by simpa using hz))).differentiableAt.differentiableWithinAt
    · intro z hz
      exact hrho_deriv_nonneg z (ne_of_lt (by simpa using hz))
  have hmonoPos : MonotoneOn rho (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hrho_cont.continuousOn
    · intro z hz
      rw [interior_Icc] at hz
      exact (hrho_deriv z (ne_of_gt hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact hrho_deriv_nonneg z (ne_of_gt hz.1)
  have hrhole : rho x ≤ rho 1 := by
    rcases le_total x 0 with hx0 | h0x
    · exact (hmonoNeg (by exact hx0) (by simp) hx0).trans
        (hmonoPos (by simp) (by simp) (by norm_num))
    · exact hmonoPos ⟨h0x, hx⟩ (by simp) hx
  have hrewrite (z : ℝ) (hz : z ≠ 0) :
      rho z = blmPhi (-lam * z) /
        (z + (beta * z ^ 2 - z) * Real.exp (-lam * z)) := by
    simp only [rho]
    rw [Function.update_of_ne hz]
    dsimp [f, g, blmPhi]
    have hepos := Real.exp_pos (lam * z)
    have hscaled :
        z + (beta * z ^ 2 - z) * Real.exp (-lam * z) =
          (z * Real.exp (lam * z) + beta * z ^ 2 - z) * Real.exp (-lam * z) := by
      rw [show -lam * z = -(lam * z) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
      ring
    have hdenScaled :
        z + (beta * z ^ 2 - z) * Real.exp (-lam * z) ≠ 0 := by
      rw [hscaled]
      exact mul_ne_zero (blm_g_pos hlam hbeta hz).ne' (Real.exp_ne_zero _)
    apply (div_eq_div_iff (blm_g_pos hlam hbeta hz).ne' hdenScaled).2
    rw [hscaled]
    rw [show -lam * z = -(lam * z) by ring, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  by_cases hxzero : x = 0
  · subst x
    simp [blmPhi]
  have hone : (1 : ℝ) ≠ 0 := one_ne_zero
  rw [hrewrite x hxzero, hrewrite 1 hone] at hrhole
  have hPhi : 0 < blmPhi (-lam) := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr hlam.ne')
    dsimp [blmPhi]
    linarith
  have hD : 0 < 1 + (beta - 1) * Real.exp (-lam) := by
    have he : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)
    have hbexp : 0 ≤ beta * Real.exp (-lam) := mul_nonneg hbeta (Real.exp_pos _).le
    nlinarith
  have hC : 0 < x + (beta * x ^ 2 - x) * Real.exp (-(lam * x)) := by
    have hgpos := blm_g_pos hlam hbeta hxzero
    have hepos := Real.exp_pos (-(lam * x))
    have hid : x + (beta * x ^ 2 - x) * Real.exp (-(lam * x)) =
        g x * Real.exp (-(lam * x)) := by
      dsimp [g]
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
      ring
    rw [hid]
    positivity
  apply (div_le_div_iff₀ hPhi hD).2
  norm_num at hrhole
  have hcross := (div_le_div_iff₀ hC hD).mp hrhole
  convert hcross using 1 <;> ring

/-- **Conditional estimate from BLM Lemma 11.11.** For [integrable increments
`Delta`](hyp:hDelta) with [integrable squares](hyp:hDeltaSq), and [integrable lower
comparators `Y`](hyp:hY) with [integrable squares](hyp:hYSq), if [`Y` lies below
`Delta`](hyp:hLower), [`Delta` is at most one](hyp:hDeltaUpper), [`Y` is at most
one](hyp:hYUpper), and [`Y` has nonnegative conditional mean](hyp:hYMean), then [the
conditional mean of `Delta^2/2-Delta` is at most half the conditional second moment of
`Y`](goal). -/
theorem blm_conditional_half_square_sub_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {Delta Y : Omega → ℝ}
    (hDelta : MeasureTheory.Integrable Delta mu)
    (hDeltaSq : MeasureTheory.Integrable (fun omega => Delta omega ^ 2) mu)
    (hY : MeasureTheory.Integrable Y mu)
    (hYSq : MeasureTheory.Integrable (fun omega => Y omega ^ 2) mu)
    (hLower : ∀ᵐ omega ∂mu, Y omega ≤ Delta omega)
    (hDeltaUpper : ∀ᵐ omega ∂mu, Delta omega ≤ 1)
    (hYUpper : ∀ᵐ omega ∂mu, Y omega ≤ 1)
    (hYMean : 0 ≤ ∫ omega, Y omega ∂mu) :
    (∫ omega, Delta omega ^ 2 / 2 - Delta omega ∂mu) ≤
      (∫ omega, Y omega ^ 2 ∂mu) / 2 := by
  have hLeftInt : MeasureTheory.Integrable
      (fun omega => Delta omega ^ 2 / 2 - Delta omega) mu :=
    (hDeltaSq.div_const 2).sub hDelta
  have hRightInt : MeasureTheory.Integrable
      (fun omega => Y omega ^ 2 / 2 - Y omega) mu :=
    (hYSq.div_const 2).sub hY
  have hpoint : (fun omega => Delta omega ^ 2 / 2 - Delta omega) ≤ᵐ[mu]
      fun omega => Y omega ^ 2 / 2 - Y omega := by
    filter_upwards [hLower, hDeltaUpper, hYUpper] with omega hl hd hy
    have hnonneg : 0 ≤ Delta omega - Y omega := sub_nonneg.mpr hl
    have hnonpos : Delta omega + Y omega - 2 ≤ 0 := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hnonneg hnonpos]
  have hint := MeasureTheory.integral_mono_ae hLeftInt hRightInt hpoint
  have hright : (∫ omega, Y omega ^ 2 / 2 - Y omega ∂mu) =
      (∫ omega, Y omega ^ 2 ∂mu) / 2 - ∫ omega, Y omega ∂mu := by
    rw [MeasureTheory.integral_sub (hYSq.div_const 2) hY,
      MeasureTheory.integral_div]
  rw [hright] at hint
  linarith

/-- **Conditional slice estimate in the proof of BLM Lemma 12.8.** Fix [a nonnegative tilt
`lam`](hyp:hlam), [a deletion value `zi`](hyp:zi), and [a nonnegative coordinate variance proxy
`sigma2`](hyp:hsigma). For [an integrable deletion increment `Delta`](hyp:hDelta) with
[integrable square](hyp:hDeltaSq), [an integrable leave-one-out maximizing coordinate `Y`](hyp:hY)
with [integrable square](hyp:hYSq), [integrability of the exponential tilt and its product with
the increment](hyp:hExp,hExpDelta), and [integrability of the tilted Bennett cost](hyp:hPhi),
suppose [`Y` lies below `Delta`](hyp:hLower),
[both variables are at most one](hyp:hDeltaUpper,hYUpper),
[`Y` has nonnegative mean](hyp:hYMean), [`Delta` has nonnegative mean](hyp:hDeltaMean), and
[`Y` has second moment at most `sigma2`](hyp:hYSecond). Then [the conditional tilted Bennett
cost is at most the BLM factor times the tilted expectation of `Delta + sigma2/2`](goal). -/
theorem blm_conditional_phi_cost_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu]
    {lam zi sigma2 : ℝ} (hlam : 0 ≤ lam) (hsigma : 0 ≤ sigma2)
    {Delta Y : Omega → ℝ}
    (hDelta : MeasureTheory.Integrable Delta mu)
    (hDeltaSq : MeasureTheory.Integrable (fun omega => Delta omega ^ 2) mu)
    (hY : MeasureTheory.Integrable Y mu)
    (hYSq : MeasureTheory.Integrable (fun omega => Y omega ^ 2) mu)
    (hExp : MeasureTheory.Integrable
      (fun omega => Real.exp (lam * (zi + Delta omega))) mu)
    (hExpDelta : MeasureTheory.Integrable
      (fun omega => Real.exp (lam * (zi + Delta omega)) * Delta omega) mu)
    (hPhi : MeasureTheory.Integrable (fun omega =>
      Real.exp (lam * (zi + Delta omega)) * blmPhi (-lam * Delta omega)) mu)
    (hLower : ∀ᵐ omega ∂mu, Y omega ≤ Delta omega)
    (hDeltaUpper : ∀ᵐ omega ∂mu, Delta omega ≤ 1)
    (hYUpper : ∀ᵐ omega ∂mu, Y omega ≤ 1)
    (hYMean : 0 ≤ ∫ omega, Y omega ∂mu)
    (hDeltaMean : 0 ≤ ∫ omega, Delta omega ∂mu)
    (hYSecond : (∫ omega, Y omega ^ 2 ∂mu) ≤ sigma2) :
    (∫ omega, Real.exp (lam * (zi + Delta omega)) *
        blmPhi (-lam * Delta omega) ∂mu) ≤
      (blmPhi (-lam) / (1 - Real.exp (-lam) / 2)) *
        ∫ omega, Real.exp (lam * (zi + Delta omega)) *
          (Delta omega + sigma2 / 2) ∂mu := by
  rcases eq_or_lt_of_le hlam with rfl | hlam
  · simp [blmPhi]
  let den := 1 - Real.exp (-lam) / 2
  let theta := blmPhi (-lam) / den
  let q : Omega → ℝ := fun omega => Delta omega ^ 2 / 2 - Delta omega
  have hden : 0 < den := by
    have he : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)
    dsimp [den]
    linarith
  have hPhiLam : 0 < blmPhi (-lam) := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr hlam.ne')
    dsimp [blmPhi]
    linarith
  have htheta : 0 ≤ theta := (div_pos hPhiLam hden).le
  have hq : MeasureTheory.Integrable q mu := hDeltaSq.div_const 2 |>.sub hDelta
  have hHalf := blm_conditional_half_square_sub_le hDelta hDeltaSq hY hYSq
    hLower hDeltaUpper hYUpper hYMean
  change (∫ omega, q omega ∂mu) ≤ (∫ omega, Y omega ^ 2 ∂mu) / 2 at hHalf
  have hqBound : (∫ omega, q omega ∂mu) ≤ sigma2 / 2 := by linarith
  have hExpOnly : MeasureTheory.Integrable
      (fun omega => Real.exp (lam * Delta omega)) mu := by
    have h := hExp.const_mul (Real.exp (-lam * zi))
    convert h using 1
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpMean : 1 ≤ ∫ omega, Real.exp (lam * Delta omega) ∂mu := by
    have hLinear : MeasureTheory.Integrable
        (fun omega => 1 + lam * Delta omega) mu :=
      MeasureTheory.integrable_const 1 |>.add (hDelta.const_mul lam)
    have hMono := MeasureTheory.integral_mono hLinear hExpOnly
      (fun omega => by simpa [add_comm] using Real.add_one_le_exp (lam * Delta omega))
    have hLinearIntegral : (∫ omega, 1 + lam * Delta omega ∂mu) =
        1 + lam * ∫ omega, Delta omega ∂mu := by
      integral_linearity
      simp
    rw [hLinearIntegral] at hMono
    nlinarith [mul_nonneg hlam.le hDeltaMean]
  have hExpFactor :
      (∫ omega, Real.exp (lam * (zi + Delta omega)) ∂mu) =
        Real.exp (lam * zi) * ∫ omega, Real.exp (lam * Delta omega) ∂mu := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with omega
    rw [← Real.exp_add]
    congr 1
    ring
  have hZiExp : Real.exp (lam * zi) ≤
      ∫ omega, Real.exp (lam * (zi + Delta omega)) ∂mu := by
    rw [hExpFactor]
    simpa using mul_le_mul_of_nonneg_left hExpMean (Real.exp_pos (lam * zi)).le
  have hPoint : (fun omega => Real.exp (lam * (zi + Delta omega)) *
      blmPhi (-lam * Delta omega)) ≤ᵐ[mu] fun omega =>
        theta * (Real.exp (lam * (zi + Delta omega)) * Delta omega +
          Real.exp (lam * zi) * q omega) := by
    filter_upwards [hDeltaUpper] with omega hUpper
    have hRatio := blm_phi_signed_increment_le
      (beta := (1 / 2 : ℝ)) (lam := lam) (x := Delta omega)
      (by norm_num) hlam.le hUpper
    have hBase : blmPhi (-lam * Delta omega) ≤
        theta * (Delta omega + q omega * Real.exp (-lam * Delta omega)) := by
      have hRaw := (div_le_iff₀ hPhiLam).mp hRatio
      calc
        blmPhi (-lam * Delta omega) ≤
            ((Delta omega + ((1 / 2 : ℝ) * Delta omega ^ 2 - Delta omega) *
              Real.exp (-lam * Delta omega)) /
                (1 + ((1 / 2 : ℝ) - 1) * Real.exp (-lam))) * blmPhi (-lam) := hRaw
        _ = theta * (Delta omega + q omega * Real.exp (-lam * Delta omega)) := by
          dsimp [theta, den, q]
          field_simp [hden.ne']
          ring
    have hMul := mul_le_mul_of_nonneg_left hBase
      (Real.exp_pos (lam * (zi + Delta omega))).le
    calc
      Real.exp (lam * (zi + Delta omega)) * blmPhi (-lam * Delta omega) ≤
          Real.exp (lam * (zi + Delta omega)) *
            (theta * (Delta omega + q omega * Real.exp (-lam * Delta omega))) := hMul
      _ = theta * (Real.exp (lam * (zi + Delta omega)) * Delta omega +
          Real.exp (lam * zi) * q omega) := by
        have hcancel : Real.exp (lam * (zi + Delta omega)) *
            Real.exp (-lam * Delta omega) = Real.exp (lam * zi) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          Real.exp (lam * (zi + Delta omega)) *
              (theta * (Delta omega + q omega * Real.exp (-lam * Delta omega))) =
              theta * (Real.exp (lam * (zi + Delta omega)) * Delta omega +
                (Real.exp (lam * (zi + Delta omega)) *
                  Real.exp (-lam * Delta omega)) * q omega) := by ring
          _ = _ := by rw [hcancel]
  have hMidInt : MeasureTheory.Integrable (fun omega =>
      theta * (Real.exp (lam * (zi + Delta omega)) * Delta omega +
        Real.exp (lam * zi) * q omega)) mu :=
    (hExpDelta.add (hq.const_mul (Real.exp (lam * zi)))).const_mul theta
  have hIntegrated := MeasureTheory.integral_mono_ae hPhi hMidInt hPoint
  have hMidIntegral :
      (∫ omega, theta * (Real.exp (lam * (zi + Delta omega)) * Delta omega +
          Real.exp (lam * zi) * q omega) ∂mu) =
        theta * ((∫ omega, Real.exp (lam * (zi + Delta omega)) * Delta omega ∂mu) +
          Real.exp (lam * zi) * ∫ omega, q omega ∂mu) := by
    integral_linearity
  rw [hMidIntegral] at hIntegrated
  have hQTerm : Real.exp (lam * zi) * (∫ omega, q omega ∂mu) ≤
      sigma2 / 2 * ∫ omega, Real.exp (lam * (zi + Delta omega)) ∂mu := by
    calc
      Real.exp (lam * zi) * (∫ omega, q omega ∂mu) ≤
          Real.exp (lam * zi) * (sigma2 / 2) :=
        mul_le_mul_of_nonneg_left hqBound (Real.exp_pos _).le
      _ ≤ sigma2 / 2 * ∫ omega, Real.exp (lam * (zi + Delta omega)) ∂mu := by
        rw [mul_comm (Real.exp (lam * zi))]
        exact mul_le_mul_of_nonneg_left hZiExp (div_nonneg hsigma (by norm_num))
  have hRightIntegral :
      (∫ omega, Real.exp (lam * (zi + Delta omega)) *
          (Delta omega + sigma2 / 2) ∂mu) =
        (∫ omega, Real.exp (lam * (zi + Delta omega)) * Delta omega ∂mu) +
          sigma2 / 2 * ∫ omega, Real.exp (lam * (zi + Delta omega)) ∂mu := by
    calc
      _ = ∫ omega, Real.exp (lam * (zi + Delta omega)) * Delta omega +
          sigma2 / 2 * Real.exp (lam * (zi + Delta omega)) ∂mu := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with omega
            ring
      _ = _ := by
        rw [MeasureTheory.integral_add hExpDelta (hExp.const_mul (sigma2 / 2)),
          MeasureTheory.integral_const_mul]
  change _ ≤ theta * _
  rw [hRightIntegral]
  apply hIntegrated.trans
  apply mul_le_mul_of_nonneg_left _ htheta
  nlinarith [hQTerm]

end Causalean.Stat.Concentration.EntropyMethod

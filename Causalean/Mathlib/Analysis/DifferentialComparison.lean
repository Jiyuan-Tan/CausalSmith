/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A differential comparison below a linear pole

This file proves the real-analysis comparison underlying the self-bounding form of the Herbst
argument.  The domain is expressed by `a * x < 1`; unlike `x < 1 / a`, this also represents the
intended unbounded nonnegative domain when `a = 0`.
-/

public section

open Filter Set
open scoped Topology

namespace Causalean.Mathlib.Analysis

/-- For [a real function `ψ`](hyp:ψ) and [nonnegative coefficients `a` and `b`](hyp:a,b), suppose
that [`ψ` is differentiable at zero](hyp:hψ0), [is differentiable at every positive point below
the linear pole](hyp:hψ), [vanishes at zero](hyp:hzero), [the coefficients are
nonnegative](hyp:ha,hb), and [its differential residual is at most `b x²`](hyp:hdiff).  Then at
[a nonnegative point `lam`](hyp:hlam0) [below the pole](hyp:hlam), [the centered value of `ψ` is
at most `(a ψ'(0) + b) lam² / (1 - a lam)`](goal). -/
theorem centered_le_of_differential_inequality
    {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ0 : DifferentiableAt ℝ ψ 0)
    (hψ : ∀ x, 0 < x → a * x < 1 → DifferentiableAt ℝ ψ x)
    (hzero : ψ 0 = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdiff : ∀ x, 0 < x → a * x < 1 →
      x * (1 - a * x) * deriv ψ x - ψ x ≤ b * x ^ 2)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : a * lam < 1) :
    ψ lam - lam * deriv ψ 0 ≤
      (a * deriv ψ 0 + b) * lam ^ 2 / (1 - a * lam) := by
  have _hb : 0 ≤ b := hb
  by_cases hlamzero : lam = 0
  · subst lam
    simp [hzero]
  have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hlamzero)
  let q : ℝ → ℝ :=
    (fun x => (1 - a * x) * (ψ x / x) - deriv ψ 0) - fun x => b * x
  have hqdiff : DifferentiableOn ℝ q (Set.Ioc 0 lam) := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hax : a * x < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hx.2 ha) hlam
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hdiv : DifferentiableAt ℝ (fun y => ψ y / y) x :=
      ((hψ x hxpos hax).hasDerivAt.fun_div (hasDerivAt_id x) hx0).differentiableAt
    have hfac : DifferentiableAt ℝ (fun y => 1 - a * y) x := by fun_prop
    have hlin : DifferentiableAt ℝ (fun y => b * y) x := by fun_prop
    exact ((hfac.mul hdiv).sub_const _).sub hlin |>.differentiableWithinAt
  have hqderiv : ∀ x ∈ interior (Set.Ioc (0 : ℝ) lam), deriv q x ≤ 0 := by
    intro x hx
    have hxmem : x ∈ Set.Ioc (0 : ℝ) lam := interior_subset hx
    have hxpos : 0 < x := hxmem.1
    have hax : a * x < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hxmem.2 ha) hlam
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hdiv := (hψ x hxpos hax).hasDerivAt.fun_div (hasDerivAt_id x) hx0
    have hfac := (hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul a)
    have hlin := (hasDerivAt_id x).const_mul b
    have hdq : HasDerivAt q
        (-a * (ψ x / x) +
          (1 - a * x) * ((deriv ψ x * x - ψ x) / x ^ 2) - b) x := by
      have hraw := ((hfac.mul hdiv).sub_const (deriv ψ 0)).sub hlin
      simpa [q] using hraw
    have halg :
        -a * (ψ x / x) +
            (1 - a * x) * ((deriv ψ x * x - ψ x) / x ^ 2) - b =
          (x * (1 - a * x) * deriv ψ x - ψ x) / x ^ 2 - b := by
      field_simp [hx0]
      ring
    rw [hdq.deriv, halg]
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
    apply sub_nonpos.mpr
    apply (div_le_iff₀ hx2).2
    simpa [mul_assoc] using hdiff x hxpos hax
  have hqanti : AntitoneOn q (Set.Ioc 0 lam) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 lam)
    · exact hqdiff.continuousOn
    · exact hqdiff.mono interior_subset
    · exact hqderiv
  have hlimSlope : Tendsto (fun x => ψ x / x) (𝓝[>] (0 : ℝ)) (𝓝 (deriv ψ 0)) := by
    have hslope := hψ0.hasDerivAt.tendsto_slope_zero_right
    simpa [hzero, div_eq_inv_mul, mul_comm] using hslope
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hfaclim : Tendsto (fun x : ℝ => 1 - a * x) (𝓝[>] 0) (𝓝 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hid) using 1
    all_goals simp
  have hlinlim : Tendsto (fun x : ℝ => b * x) (𝓝[>] 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul hid using 1
    all_goals simp
  have hconstlim : Tendsto (fun _ : ℝ => deriv ψ 0) (𝓝[>] 0) (𝓝 (deriv ψ 0)) :=
    tendsto_const_nhds
  have hlimQ : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    change Tendsto
      (fun x => (1 - a * x) * (ψ x / x) - deriv ψ 0 - b * x)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa using ((hfaclim.mul hlimSlope).sub hconstlim).sub hlinlim
  have hevent : ∀ᶠ x in 𝓝[>] (0 : ℝ), q lam ≤ q x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hlampos).filter_mono inf_le_left] with x hxpos hxlam
    exact hqanti ⟨hxpos, le_of_lt hxlam⟩ ⟨hlampos, le_rfl⟩ (le_of_lt hxlam)
  have hqle : q lam ≤ 0 := ge_of_tendsto hlimQ hevent
  dsimp [q] at hqle
  have hden : 0 < 1 - a * lam := sub_pos.mpr hlam
  apply (le_div_iff₀ hden).2
  field_simp [hlamzero] at hqle
  nlinarith [hb]

end Causalean.Mathlib.Analysis

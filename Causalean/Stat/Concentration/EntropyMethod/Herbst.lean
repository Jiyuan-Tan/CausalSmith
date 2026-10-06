/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Herbst argument

This file turns an entropy bound for every exponential tilt into a centered logarithmic
moment-generating-function bound. The proof is the classical Herbst differential argument from
Boucheron--Lugosi--Massart, Section 6.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace Causalean.Stat.Concentration.EntropyMethod

private lemma herbst_calculus
    {ψ : ℝ → ℝ} {v : ℝ}
    (hψ : Differentiable ℝ ψ) (h0 : ψ 0 = 0)
    (hdiff : ∀ x, 0 < x → x * deriv ψ x - ψ x ≤ x ^ 2 * v / 2) :
    ∀ lam, 0 < lam → ψ lam - lam * deriv ψ 0 ≤ lam ^ 2 * v / 2 := by
  let q : ℝ → ℝ := (fun x => ψ x / x) - fun x => v * x / 2
  have hqdiff : DifferentiableOn ℝ q (Set.Ioi 0) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hdiv : DifferentiableAt ℝ (fun y => ψ y / y) x :=
      ((hψ x).hasDerivAt.fun_div (hasDerivAt_id x) hx0).differentiableAt
    have hlin : DifferentiableAt ℝ (fun y => v * y / 2) x := by fun_prop
    exact (hdiv.sub hlin).differentiableWithinAt
  have hqderiv : ∀ x ∈ Set.Ioi (0 : ℝ), deriv q x ≤ 0 := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hderiv : deriv q x = (x * deriv ψ x - ψ x) / x ^ 2 - v / 2 := by
      have hdiv := (hψ x).hasDerivAt.fun_div (hasDerivAt_id x) hx0
      have hlin := ((hasDerivAt_id x).const_mul v).div_const 2
      have hdifference := hdiv.sub hlin
      have hdq : HasDerivAt q
          ((deriv ψ x * x - ψ x) / x ^ 2 - v / 2) x := by
        simpa [q] using hdifference
      rw [hdq.deriv]
      ring
    rw [hderiv]
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hdiv : (x * deriv ψ x - ψ x) / x ^ 2 ≤ v / 2 := by
      apply (div_le_iff₀ hx2).2
      nlinarith [hdiff x hx]
    linarith
  have hqanti : AntitoneOn q (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi (𝕜 := ℝ) 0)
    · exact hqdiff.continuousOn
    · simpa using hqdiff
    · simpa using hqderiv
  have hlimSlope : Tendsto (fun x => ψ x / x) (𝓝[>] (0 : ℝ)) (𝓝 (deriv ψ 0)) := by
    have hslope := (hψ 0).hasDerivAt.tendsto_slope_zero_right
    simpa [h0, div_eq_inv_mul, mul_comm] using hslope
  have hlimQ : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (deriv ψ 0)) := by
    have hzero : Tendsto (fun x : ℝ => v * x / 2) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      convert ((tendsto_const_nhds.mul hid).div_const 2) using 1
      all_goals simp
    change Tendsto (fun x => ψ x / x - v * x / 2) (𝓝[>] (0 : ℝ)) (𝓝 (deriv ψ 0))
    simpa using hlimSlope.sub hzero
  intro lam hlam
  have hevent : ∀ᶠ x in 𝓝[>] (0 : ℝ), q lam ≤ q x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hlam).filter_mono inf_le_left] with x hxpos hxlam
    exact hqanti hxpos hlam (le_of_lt hxlam)
  have hqle : q lam ≤ deriv ψ 0 := ge_of_tendsto hlimQ hevent
  dsimp [q] at hqle
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  apply (sub_le_iff_le_add).2
  have hmul := mul_le_mul_of_nonneg_left hqle hlam.le
  field_simp [hlam0] at hmul ⊢
  nlinarith

/-- Under [exponential integrability at every real tilt](hyp:hExp) and [the entropy bound at every
positive tilt](hyp:hEnt), the centered cumulant-generating function at [a positive
tilt](hyp:hlam) is at most `lam ^ 2 * v / 2` as [claimed](goal). -/
theorem herbst_cgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {v : ℝ}
    (hExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (hEnt : ∀ t : ℝ, 0 < t →
      entropy μ (fun ω => Real.exp (t * Z ω)) ≤
        t ^ 2 * v / 2 * ∫ ω, Real.exp (t * Z ω) ∂μ)
    {lam : ℝ} (hlam : 0 < lam) :
    cgf Z μ lam - lam * (∫ ω, Z ω ∂μ) ≤ lam ^ 2 * v / 2 := by
  have hset : interior (integrableExpSet Z μ) = Set.univ := by
    rw [interior_eq_univ]
    ext t
    simpa [integrableExpSet] using hExp t
  have hdiff : Differentiable ℝ (cgf Z μ) := by
    intro t
    exact (analyticAt_cgf (by simp [hset])).differentiableAt
  have hderiv0 : deriv (cgf Z μ) 0 = ∫ ω, Z ω ∂μ := by
    simpa using deriv_cgf_zero (X := Z) (μ := μ) (by simp [hset])
  have hdifferential : ∀ t : ℝ, 0 < t →
      t * deriv (cgf Z μ) t - cgf Z μ t ≤ t ^ 2 * v / 2 := by
    intro t ht
    have hmem : t ∈ interior (integrableExpSet Z μ) := by simp [hset]
    have hMpos : 0 < mgf Z μ t := mgf_pos (hExp t)
    have hidentity :
        entropy μ (fun ω => Real.exp (t * Z ω)) =
          mgf Z μ t * (t * deriv (cgf Z μ) t - cgf Z μ t) := by
      rw [entropy]
      simp_rw [Real.log_exp]
      rw [show (∫ ω, Real.exp (t * Z ω) * (t * Z ω) ∂μ) =
          t * ∫ ω, Z ω * Real.exp (t * Z ω) ∂μ by
        rw [← integral_const_mul]
        congr with ω
        ring]
      rw [show (∫ ω, Real.exp (t * Z ω) ∂μ) = mgf Z μ t by rfl]
      rw [deriv_cgf hmem]
      dsimp [cgf]
      field_simp [hMpos.ne']
    have hbound := hEnt t ht
    rw [hidentity, show (∫ ω, Real.exp (t * Z ω) ∂μ) = mgf Z μ t by rfl] at hbound
    exact (mul_le_mul_iff_of_pos_left hMpos).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)
  have hcalc := herbst_calculus hdiff cgf_zero hdifferential lam hlam
  simpa [hderiv0] using hcalc

/-- Under [exponential integrability at every real tilt](hyp:hExp) and [the entropy bound at every
positive tilt](hyp:hEnt), the moment-generating function of the centered variable at [a positive
tilt](hyp:hlam) satisfies the [sub-Gaussian bound](goal). -/
theorem herbst_mgf_centered_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {v : ℝ}
    (hExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (hEnt : ∀ t : ℝ, 0 < t →
      entropy μ (fun ω => Real.exp (t * Z ω)) ≤
        t ^ 2 * v / 2 * ∫ ω, Real.exp (t * Z ω) ∂μ)
    {lam : ℝ} (hlam : 0 < lam) :
    mgf (fun ω => Z ω - ∫ x, Z x ∂μ) μ lam ≤ Real.exp (lam ^ 2 * v / 2) := by
  let m := ∫ x, Z x ∂μ
  have hcgf := herbst_cgf_le hExp hEnt hlam
  change mgf (fun ω => Z ω + -m) μ lam ≤ Real.exp (lam ^ 2 * v / 2)
  rw [mgf_add_const, ← exp_cgf (hExp lam), ← Real.exp_add, Real.exp_le_exp]
  dsimp [m] at hcgf ⊢
  linarith

/-- Under [exponential integrability at every real tilt](hyp:hExp), [the entropy bound at every
positive tilt](hyp:hEnt), and [a positive variance proxy](hyp:hv), every [positive
deviation](hyp:ht) of the centered variable obeys the [sub-Gaussian upper-tail bound](goal). -/
theorem herbst_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {v : ℝ}
    (hExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (hEnt : ∀ t : ℝ, 0 < t →
      entropy μ (fun ω => Real.exp (t * Z ω)) ≤
        t ^ 2 * v / 2 * ∫ ω, Real.exp (t * Z ω) ∂μ)
    (hv : 0 < v) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ Z ω - ∫ x, Z x ∂μ} ≤ Real.exp (-t ^ 2 / (2 * v)) := by
  let m := ∫ x, Z x ∂μ
  let lam := t / v
  have hlam : 0 < lam := div_pos ht hv
  have hint : Integrable (fun ω => Real.exp (lam * (Z ω - m))) μ := by
    have h := (hExp lam).mul_const (Real.exp (-lam * m))
    convert h using 1
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hchernoff := measure_ge_le_exp_mul_mgf t hlam.le hint
  have hmgf : mgf (fun ω => Z ω - m) μ lam ≤ Real.exp (lam ^ 2 * v / 2) := by
    dsimp [m]
    exact herbst_mgf_centered_le hExp hEnt hlam
  calc
    μ.real {ω | t ≤ Z ω - ∫ x, Z x ∂μ} = μ.real {ω | t ≤ Z ω - m} := by rfl
    _ ≤ Real.exp (-lam * t) * mgf (fun ω => Z ω - m) μ lam := hchernoff
    _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * v / 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (2 * v)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      field_simp [hv.ne']
      ring

end Causalean.Stat.Concentration.EntropyMethod

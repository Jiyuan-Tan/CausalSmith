/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Analysis.DifferentialComparison
public import Causalean.Stat.Concentration.EntropyMethod.Bousquet
public import Causalean.Stat.Concentration.EntropyMethod.Herbst
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Differential comparison for Bousquet's entropy bound

This file proves the global differential step following Boucheron--Lugosi--Massart Lemma 12.8.
On the small-tilt interval `2λ < 1`, the exact Bennett coefficient is bounded by `2λ²`; the
generic differential comparison theorem then yields a centered sub-gamma MGF and an explicit
Bernstein upper tail.  The constants are conservative but preserve the variance-sensitive form.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace Causalean.Stat.Concentration.EntropyMethod

/-- For [a nonnegative tilt `lam`](hyp:hlam) with [`lam` at most one](hyp:hlam_one), [the BLM
Bennett coefficient is at most `2 lam²`](goal). -/
theorem blm_bennett_coefficient_le_two_sq {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_one : lam ≤ 1) :
    blmPhi (-lam) / (1 - Real.exp (-lam) / 2) ≤ 2 * lam ^ 2 := by
  have hnorm : ‖-lam‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hlam] using hlam_one
  have hphiAbs := Real.norm_exp_sub_one_sub_id_le hnorm
  have hphi : blmPhi (-lam) ≤ lam ^ 2 := by
    rw [Real.norm_eq_abs] at hphiAbs
    have hrewrite : Real.exp (-lam) - 1 - (-lam) = blmPhi (-lam) := by
      dsimp [blmPhi]
      ring
    rw [hrewrite] at hphiAbs
    exact (le_abs_self _).trans (by simpa using hphiAbs)
  have hexp : Real.exp (-lam) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlam)
  have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-lam) / 2 := by linarith
  have hdenpos : 0 < 1 - Real.exp (-lam) / 2 := lt_of_lt_of_le (by norm_num) hden
  apply (div_le_iff₀ hdenpos).2
  nlinarith [sq_nonneg lam]

private lemma integral_exp_mul_add_eq_mgf_mul
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} (hExp : ∀ t : ℝ, Integrable (fun omega => Real.exp (t * Z omega)) mu)
    (c t : ℝ) (hmem : t ∈ interior (integrableExpSet Z mu)) :
    (∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu) =
      mgf Z mu t * (deriv (cgf Z mu) t + c) := by
  have hZexp : Integrable (fun omega => Z omega * Real.exp (t * Z omega)) mu := by
    simpa using
      (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1)
  have hrewrite : (∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu) =
      (∫ omega, Z omega * Real.exp (t * Z omega) ∂mu) +
        c * ∫ omega, Real.exp (t * Z omega) ∂mu := by
    calc
      _ = ∫ omega, Z omega * Real.exp (t * Z omega) +
          c * Real.exp (t * Z omega) ∂mu := by
            apply integral_congr_ae
            filter_upwards with omega
            ring
      _ = _ := by
        rw [integral_add hZexp ((hExp t).const_mul c), integral_const_mul]
  rw [hrewrite, deriv_cgf hmem]
  dsimp [mgf]
  have hMpos : 0 < ∫ omega, Real.exp (t * Z omega) ∂mu := mgf_pos (hExp t)
  field_simp [hMpos.ne']
  simp only [mul_comm]

private lemma integral_exp_mul_add_nonneg
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hmean : 0 ≤ ∫ omega, Z omega ∂mu)
    (hExp : ∀ u : ℝ, Integrable (fun omega => Real.exp (u * Z omega)) mu) :
    0 ≤ ∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu := by
  have hset : interior (integrableExpSet Z mu) = Set.univ := by
    rw [interior_eq_univ]
    ext u
    simpa [integrableExpSet] using hExp u
  have hdiff : Differentiable ℝ (cgf Z mu) := fun u =>
    (analyticAt_cgf (by simp [hset])).differentiableAt
  have hdiffDeriv : Differentiable ℝ (deriv (cgf Z mu)) := fun u =>
    (analyticAt_cgf (by simp [hset])).deriv.differentiableAt
  have hsecond : ∀ u, 0 ≤ (deriv^[2] (cgf Z mu)) u := by
    intro u
    rw [← iteratedDeriv_eq_iterate]
    rw [iteratedDeriv_two_cgf_eq_integral (by simp [hset])]
    exact div_nonneg (integral_nonneg fun omega =>
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (mgf_pos (hExp u)).le
  have hconvex : ConvexOn ℝ Set.univ (cgf Z mu) :=
    convexOn_univ_of_deriv2_nonneg hdiff hdiffDeriv hsecond
  have hmono : MonotoneOn (deriv (cgf Z mu)) Set.univ :=
    hconvex.monotoneOn_deriv (fun u _ => hdiff u)
  have hderiv0 : deriv (cgf Z mu) 0 = ∫ omega, Z omega ∂mu := by
    simpa using deriv_cgf_zero (X := Z) (μ := mu) (by simp [hset])
  have hderiv : 0 ≤ deriv (cgf Z mu) t + c := by
    have hle := hmono (by simp) (by simp) ht
    rw [hderiv0] at hle
    linarith
  have hidentity := integral_exp_mul_add_eq_mgf_mul hExp c t (by simp [hset])
  rw [hidentity]
  exact mul_nonneg (mgf_pos (hExp t)).le hderiv

/-- **BLM Lemma 12.8, conservative differential form.** Suppose [all exponential tilts of
`Z` are integrable](hyp:hExp), [the exact BLM entropy comparison holds at every positive tilt
below one half](hyp:hEnt), [the mean of `Z` is nonnegative](hyp:hmean), and [the variance
half-proxy `c` is nonnegative](hyp:hc). Then at [a nonnegative tilt `lam`](hyp:hlam)
[below one half](hyp:hlam_half), [the centered cumulant-generating function is at most
`2 (E Z + c) lam² / (1 - 2 lam)`](goal). -/
theorem blm_cgf_centered_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Z : Omega → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hExp : ∀ t : ℝ, Integrable (fun omega => Real.exp (t * Z omega)) mu)
    (hEnt : ∀ t : ℝ, 0 < t → 2 * t < 1 →
      entropy mu (fun omega => Real.exp (t * Z omega)) ≤
        (blmPhi (-t) / (1 - Real.exp (-t) / 2)) *
          ∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu)
    (hmean : 0 ≤ ∫ omega, Z omega ∂mu)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam_half : 2 * lam < 1) :
    cgf Z mu lam - lam * (∫ omega, Z omega ∂mu) ≤
      (2 * (∫ omega, Z omega ∂mu) + 2 * c) * lam ^ 2 / (1 - 2 * lam) := by
  have hset : interior (integrableExpSet Z mu) = Set.univ := by
    rw [interior_eq_univ]
    ext t
    simpa [integrableExpSet] using hExp t
  have hdiff : Differentiable ℝ (cgf Z mu) := by
    intro t
    exact (analyticAt_cgf (by simp [hset])).differentiableAt
  have hderiv0 : deriv (cgf Z mu) 0 = ∫ omega, Z omega ∂mu := by
    simpa using deriv_cgf_zero (X := Z) (μ := mu) (by simp [hset])
  have hdifferential : ∀ t, 0 < t → 2 * t < 1 →
      t * (1 - 2 * t) * deriv (cgf Z mu) t - cgf Z mu t ≤ 2 * c * t ^ 2 := by
    intro t ht htHalf
    have htOne : t ≤ 1 := by linarith
    have hmem : t ∈ interior (integrableExpSet Z mu) := by simp [hset]
    have hMpos : 0 < mgf Z mu t := mgf_pos (hExp t)
    have hidentity :
        entropy mu (fun omega => Real.exp (t * Z omega)) =
          mgf Z mu t * (t * deriv (cgf Z mu) t - cgf Z mu t) := by
      rw [entropy]
      simp_rw [Real.log_exp]
      rw [show (∫ omega, Real.exp (t * Z omega) * (t * Z omega) ∂mu) =
          t * ∫ omega, Z omega * Real.exp (t * Z omega) ∂mu by
        rw [← integral_const_mul]
        congr with omega
        ring]
      rw [show (∫ omega, Real.exp (t * Z omega) ∂mu) = mgf Z mu t by rfl]
      rw [deriv_cgf hmem]
      dsimp [cgf]
      field_simp [hMpos.ne']
    have hweightedEq := integral_exp_mul_add_eq_mgf_mul hExp c t hmem
    have hweightedNonneg := integral_exp_mul_add_nonneg hc ht.le hmean hExp
    have hfactorNonneg : 0 ≤ deriv (cgf Z mu) t + c := by
      rw [hweightedEq] at hweightedNonneg
      exact (mul_nonneg_iff_of_pos_left hMpos).mp hweightedNonneg
    have hraw := hEnt t ht htHalf
    rw [hidentity, hweightedEq] at hraw
    have hdivided : t * deriv (cgf Z mu) t - cgf Z mu t ≤
        (blmPhi (-t) / (1 - Real.exp (-t) / 2)) *
          (deriv (cgf Z mu) t + c) := by
      exact (mul_le_mul_iff_of_pos_left hMpos).mp
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hraw)
    have htheta := blm_bennett_coefficient_le_two_sq ht.le htOne
    have hweakened : t * deriv (cgf Z mu) t - cgf Z mu t ≤
        2 * t ^ 2 * (deriv (cgf Z mu) t + c) :=
      hdivided.trans (mul_le_mul_of_nonneg_right htheta hfactorNonneg)
    nlinarith
  have hcalc := Causalean.Mathlib.Analysis.centered_le_of_differential_inequality
    (hdiff 0) (fun t _ _ => hdiff t) cgf_zero (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (by norm_num) hc) hdifferential hlam hlam_half
  simpa [hderiv0] using hcalc

/-- Under [the exponential-integrability and BLM entropy assumptions](hyp:hExp,hEnt), with [a
nonnegative mean](hyp:hmean) and [a nonnegative variance half-proxy `c`](hyp:hc), the [centered
MGF at a nonnegative tilt `lam` below one half obeys the conservative BLM bound](goal), provided
the [tilt is nonnegative and below one half](hyp:hlam,hlam_half). -/
theorem blm_mgf_centered_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Z : Omega → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hExp : ∀ t : ℝ, Integrable (fun omega => Real.exp (t * Z omega)) mu)
    (hEnt : ∀ t : ℝ, 0 < t → 2 * t < 1 →
      entropy mu (fun omega => Real.exp (t * Z omega)) ≤
        (blmPhi (-t) / (1 - Real.exp (-t) / 2)) *
          ∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu)
    (hmean : 0 ≤ ∫ omega, Z omega ∂mu)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam_half : 2 * lam < 1) :
    mgf (fun omega => Z omega - ∫ x, Z x ∂mu) mu lam ≤
      Real.exp ((2 * (∫ omega, Z omega ∂mu) + 2 * c) * lam ^ 2 /
        (1 - 2 * lam)) := by
  let m := ∫ x, Z x ∂mu
  have hcgf := blm_cgf_centered_le hc hExp hEnt hmean hlam hlam_half
  change mgf (fun omega => Z omega + -m) mu lam ≤ _
  rw [mgf_add_const, ← exp_cgf (hExp lam), ← Real.exp_add, Real.exp_le_exp]
  dsimp [m] at hcgf ⊢
  linarith

/-- Under [the exponential-integrability and BLM entropy assumptions](hyp:hExp,hEnt), with [a
nonnegative mean](hyp:hmean), [a nonnegative variance half-proxy `c`](hyp:hc), and [positive
combined scale `E Z + c`](hyp:hscale), every [positive deviation `t`](hyp:ht) satisfies [the
conservative variance-sensitive Bousquet upper tail](goal). -/
theorem blm_upper_tail
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Z : Omega → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hExp : ∀ t : ℝ, Integrable (fun omega => Real.exp (t * Z omega)) mu)
    (hEnt : ∀ t : ℝ, 0 < t → 2 * t < 1 →
      entropy mu (fun omega => Real.exp (t * Z omega)) ≤
        (blmPhi (-t) / (1 - Real.exp (-t) / 2)) *
          ∫ omega, Real.exp (t * Z omega) * (Z omega + c) ∂mu)
    (hmean : 0 ≤ ∫ omega, Z omega ∂mu)
    (hscale : 0 < (∫ omega, Z omega ∂mu) + c)
    {t : ℝ} (ht : 0 < t) :
    mu.real {omega | t ≤ Z omega - ∫ x, Z x ∂mu} ≤
      Real.exp (-t ^ 2 / (8 * ((∫ omega, Z omega ∂mu) + c) + 4 * t)) := by
  let m := ∫ x, Z x ∂mu
  let C := 2 * (m + c)
  let lam := t / (2 * C + 2 * t)
  have hC : 0 < C := by dsimp [C, m]; positivity
  have hden : 0 < 2 * C + 2 * t := by positivity
  have hlam : 0 ≤ lam := (div_pos ht hden).le
  have hlamHalf : 2 * lam < 1 := by
    dsimp [lam]
    rw [show 2 * (t / (2 * C + 2 * t)) = (2 * t) / (2 * C + 2 * t) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hint : Integrable (fun omega => Real.exp (lam * (Z omega - m))) mu := by
    have h := (hExp lam).mul_const (Real.exp (-lam * m))
    convert h using 1
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  have hchernoff := measure_ge_le_exp_mul_mgf t hlam hint
  have hmgf : mgf (fun omega => Z omega - m) mu lam ≤
      Real.exp (C * lam ^ 2 / (1 - 2 * lam)) := by
    simpa [C, m, mul_add, add_mul] using
      blm_mgf_centered_le hc hExp hEnt hmean hlam hlamHalf
  calc
    mu.real {omega | t ≤ Z omega - m} ≤
        Real.exp (-lam * t) * mgf (fun omega => Z omega - m) mu lam := hchernoff
    _ ≤ Real.exp (-lam * t) * Real.exp (C * lam ^ 2 / (1 - 2 * lam)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (4 * C + 4 * t)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      have hpole : 1 - 2 * (t / (2 * C + 2 * t)) ≠ 0 :=
        ne_of_gt (sub_pos.mpr hlamHalf)
      field_simp [hden.ne', hpole, hC.ne']
      ring
    _ = Real.exp (-t ^ 2 / (8 * (m + c) + 4 * t)) := by
      congr 2
      dsimp [C]
      ring

end Causalean.Stat.Concentration.EntropyMethod

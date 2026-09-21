/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-coordinate entropy tensorization

This file proves the two-coordinate case of sub-additivity of entropy (BLM, Theorem 4.10).
The proof first establishes the entropy chain rule and then applies the Gibbs variational
characterization to show that averaging over one coordinate cannot increase entropy beyond the
average of the section entropies.

The regularity bundle records only measurability and integrability facts used by Fubini and the
variational argument.  Bounded strictly positive measurable functions satisfy these conditions.
-/

@[expose] public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

/-- For [probability laws `μ` and `ν`](hyp:μ,ν) and [a function `f` on their product](hyp:f),
the tensorization regularity conditions require [integrability of `f`](hyp:hf), [integrability of
`f log f`](hyp:hflog), [pointwise positivity](hyp:hfpos), [positive means in almost every
second-coordinate section](hyp:hsectionMeanPos), [integrability of the first-coordinate average
times its logarithm](hyp:hAlog), [positivity of that average almost everywhere](hyp:hApos),
[positivity of the total mean](hyp:hm), [integrability of `f` times the logarithmic
optimizer](hyp:hfg), and [integrability of the second-coordinate section
entropies](hyp:hEntropy). -/
structure EntropyTensorizationIntegrable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X × Y → ℝ) : Prop where
  hf : Integrable f (μ.prod ν)
  hflog : Integrable (fun z => f z * Real.log (f z)) (μ.prod ν)
  hfpos : ∀ x y, 0 < f (x, y)
  hsectionMeanPos : ∀ᵐ x ∂μ, 0 < ∫ y, f (x, y) ∂ν
  hAlog : Integrable
    (fun y => (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ)) ν
  hApos : ∀ᵐ y ∂ν, 0 < ∫ x, f (x, y) ∂μ
  hm : 0 < ∫ y, (∫ x, f (x, y) ∂μ) ∂ν
  hfg : Integrable (fun z => f z * Real.log
    ((∫ x, f (x, z.2) ∂μ) / ∫ y, (∫ x, f (x, y) ∂μ) ∂ν)) (μ.prod ν)
  hEntropy : Integrable (fun x => entropy ν (fun y => f (x, y))) μ

private lemma entropy_prod_chain
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ)
    (hf : Integrable f (μ.prod ν))
    (hflog : Integrable (fun z => f z * Real.log (f z)) (μ.prod ν))
    (hAlog : Integrable
      (fun y => (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ)) ν) :
    entropy (μ.prod ν) f =
      (∫ y, entropy μ (fun x => f (x, y)) ∂ν) +
        entropy ν (fun y => ∫ x, f (x, y) ∂μ) := by
  have hinnerFlog : Integrable
      (fun y => ∫ x, f (x, y) * Real.log (f (x, y)) ∂μ) ν :=
    hflog.integral_prod_right
  rw [entropy]
  rw [integral_prod_symm _ hflog, integral_prod_symm _ hf]
  rw [entropy]
  change _ =
    (∫ y, (∫ x, f (x, y) * Real.log (f (x, y)) ∂μ) -
      (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ) ∂ν) + _
  rw [integral_sub hinnerFlog hAlog]
  ring

private lemma entropy_integral_le_integral_entropy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (h : EntropyTensorizationIntegrable μ ν f) :
    entropy ν (fun y => ∫ x, f (x, y) ∂μ) ≤
      ∫ x, entropy ν (fun y => f (x, y)) ∂μ := by
  let A : Y → ℝ := fun y => ∫ x, f (x, y) ∂μ
  let m : ℝ := ∫ y, A y ∂ν
  let g : Y → ℝ := fun y => Real.log (A y / m)
  have hA : Integrable A ν := h.hf.integral_prod_right
  have hAg : Integrable (fun y => A y * g y) ν := by
    have hEq : (fun y => A y * Real.log (A y / m))
        =ᵐ[ν] fun y => A y * Real.log (A y) - A y * Real.log m := by
      filter_upwards [h.hApos] with y hy
      rw [Real.log_div hy.ne' h.hm.ne']
      ring
    rw [integrable_congr hEq]
    exact h.hAlog.sub (hA.mul_const _)
  have hexp_eq : (fun y => Real.exp (g y)) =ᵐ[ν] fun y => A y / m := by
    filter_upwards [h.hApos] with y hy
    exact Real.exp_log (div_pos hy h.hm)
  have hexp : Integrable (fun y => Real.exp (g y)) ν := by
    rw [integrable_congr hexp_eq]
    exact hA.div_const m
  have hexp_mean : (∫ y, Real.exp (g y) ∂ν) = 1 := by
    rw [integral_congr_ae hexp_eq, integral_div, show (∫ y, A y ∂ν) = m by rfl]
    exact div_self h.hm.ne'
  have hfg := h.hfg
  change Integrable (fun z => f z * g z.2) (μ.prod ν) at hfg
  have hsection : (fun x => ∫ y, f (x, y) * g y ∂ν) ≤ᵐ[μ]
      fun x => entropy ν (fun y => f (x, y)) := by
    filter_upwards [h.hf.prod_right_ae, h.hflog.prod_right_ae, hfg.prod_right_ae,
      h.hsectionMeanPos] with x hfx hflogx hfgx hmx
    exact integral_mul_le_entropy hfx hflogx (ae_of_all _ (h.hfpos x)) hmx hfgx
      hexp hexp_mean.le
  have hleft : Integrable (fun x => ∫ y, f (x, y) * g y ∂ν) μ :=
    hfg.integral_prod_left
  have hbound := integral_mono_ae hleft h.hEntropy hsection
  have hFubini : (∫ x, ∫ y, f (x, y) * g y ∂ν ∂μ) = ∫ y, A y * g y ∂ν := by
    calc
      _ = ∫ z, f z * g z.2 ∂(μ.prod ν) := (integral_prod _ hfg).symm
      _ = ∫ y, ∫ x, f (x, y) * g y ∂μ ∂ν := integral_prod_symm _ hfg
      _ = _ := by
        simp_rw [integral_mul_const]
        rfl
  rw [hFubini] at hbound
  calc
    entropy ν A = ∫ y, A y * g y ∂ν :=
      entropy_eq_integral_mul_log_div hA h.hAlog h.hApos h.hm
    _ ≤ _ := hbound

/-- Under [the stated positivity and integrability conditions](hyp:h), the [entropy of a function
of two independent coordinates is at most the expected entropy in the first coordinate plus the
expected entropy in the second coordinate](goal). -/
theorem entropy_prod_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (h : EntropyTensorizationIntegrable μ ν f) :
    entropy (μ.prod ν) f ≤
      (∫ y, entropy μ (fun x => f (x, y)) ∂ν) +
        (∫ x, entropy ν (fun y => f (x, y)) ∂μ) := by
  rw [entropy_prod_chain μ ν f h.hf h.hflog h.hAlog]
  have hconvex := entropy_integral_le_integral_entropy μ ν f h
  have hadd := add_le_add_left hconvex (∫ y, entropy μ (fun x => f (x, y)) ∂ν)
  simpa [add_comm] using hadd

end Causalean.Stat.Concentration.EntropyMethod

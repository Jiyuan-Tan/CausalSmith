/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Entropy of a nonnegative random variable

This file defines the entropy functional used by the entropy method and proves its
Gibbs variational characterization for strictly positive integrable functions.  The
characterization is the elementary analytic input to entropy tensorization.

The formulation is real-valued.  Later tensorization and Herbst results impose boundedness,
which guarantees all the integrability hypotheses appearing here.
-/

@[expose] public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

/-- Given [a measure `μ`](hyp:μ) and [a real-valued function `f`](hyp:f), the [entropy of `f`
under `μ`](goal) is its expected `f log f` minus its mean times the logarithm of its mean. -/
noncomputable def entropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω, f ω * Real.log (f ω) ∂μ) -
    (∫ ω, f ω ∂μ) * Real.log (∫ ω, f ω ∂μ)

/-- Given [a probability measure `μ`](hyp:μ) and [a positive function `f`](hyp:f), the
[variational values associated with `f`](goal) are the integrals `E[f g]` over integrable
test functions whose exponential has expectation at most one.

The three clauses require integrability of `f g`, integrability of `exp g`, and the exponential
normalization, respectively. -/
def entropyDualValues {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Set ℝ :=
  {r | ∃ g : Ω → ℝ,
    Integrable (fun ω => f ω * g ω) μ ∧
    Integrable (fun ω => Real.exp (g ω)) μ ∧
    (∫ ω, Real.exp (g ω) ∂μ) ≤ 1 ∧
    r = ∫ ω, f ω * g ω ∂μ}

private lemma scaledYoung {x y m : ℝ} (hx : 0 < x) (hm : 0 < m) :
    x * y ≤ x * Real.log (x / m) - x + m * Real.exp y := by
  have hratio : 0 < x / m := div_pos hx hm
  have hratio2 : 0 < Real.exp y / (x / m) := div_pos (Real.exp_pos y) hratio
  have hlog := Real.log_le_sub_one_of_pos hratio2
  rw [Real.log_div (Real.exp_ne_zero y) hratio.ne', Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hratio.le
  have h : (x / m) * y ≤
      (x / m) * Real.log (x / m) - (x / m) + Real.exp y := by
    calc
      (x / m) * y ≤ (x / m) *
          (Real.log (x / m) + (Real.exp y / (x / m) - 1)) := by linarith
      _ = (x / m) * Real.log (x / m) - (x / m) + Real.exp y := by
        field_simp [hratio.ne']
        ring
  calc
    x * y = m * ((x / m) * y) := by field_simp [hm.ne']
    _ ≤ m * ((x / m) * Real.log (x / m) - (x / m) + Real.exp y) :=
      mul_le_mul_of_nonneg_left h hm.le
    _ = x * Real.log (x / m) - x + m * Real.exp y := by
      field_simp [hm.ne']

private lemma integrable_mul_log_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ} {m : ℝ}
    (hf : Integrable f μ)
    (hflog : Integrable (fun ω => f ω * Real.log (f ω)) μ)
    (hfpos : ∀ᵐ ω ∂μ, 0 < f ω) (hm : 0 < m) :
    Integrable (fun ω => f ω * Real.log (f ω / m)) μ := by
  have hEq : (fun ω => f ω * Real.log (f ω / m))
      =ᵐ[μ] fun ω => f ω * Real.log (f ω) - f ω * Real.log m := by
    filter_upwards [hfpos] with ω hω
    rw [Real.log_div hω.ne' hm.ne']
    ring
  rw [integrable_congr hEq]
  exact hflog.sub (hf.mul_const _)

/-- If [the function `f` is integrable](hyp:hf), [`f log f` is integrable](hyp:hflog),
[`f` is positive almost everywhere](hyp:hfpos), and [its mean is positive](hyp:hm), then
[its entropy is the integral of `f log (f / E f)`](goal). -/
theorem entropy_eq_integral_mul_log_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ)
    (hflog : Integrable (fun ω => f ω * Real.log (f ω)) μ)
    (hfpos : ∀ᵐ ω ∂μ, 0 < f ω)
    (hm : 0 < ∫ ω, f ω ∂μ) :
    entropy μ f = ∫ ω, f ω * Real.log (f ω / ∫ x, f x ∂μ) ∂μ := by
  rw [entropy]
  have hEq : (fun ω => f ω * Real.log (f ω / ∫ x, f x ∂μ))
      =ᵐ[μ] fun ω => f ω * Real.log (f ω) -
        f ω * Real.log (∫ x, f x ∂μ) := by
    filter_upwards [hfpos] with ω hω
    rw [Real.log_div hω.ne' hm.ne']
    ring
  rw [integral_congr_ae hEq]
  rw [integral_sub hflog (hf.mul_const _), integral_mul_const]

/-- Under [integrability of `f`](hyp:hf), [integrability of `f log f`](hyp:hflog),
[positivity of `f` almost everywhere](hyp:hfpos), and [positivity of its mean](hyp:hm),
every test function for which [`f g` is integrable](hyp:hfg), [`exp g` is
integrable](hyp:hexp), and [`E[exp g] ≤ 1`](hyp:hconstraint) satisfies
[`E[f g] ≤ Ent(f)`](goal). -/
theorem integral_mul_le_entropy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ}
    (hf : Integrable f μ)
    (hflog : Integrable (fun ω => f ω * Real.log (f ω)) μ)
    (hfpos : ∀ᵐ ω ∂μ, 0 < f ω)
    (hm : 0 < ∫ ω, f ω ∂μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hexp : Integrable (fun ω => Real.exp (g ω)) μ)
    (hconstraint : (∫ ω, Real.exp (g ω) ∂μ) ≤ 1) :
    (∫ ω, f ω * g ω ∂μ) ≤ entropy μ f := by
  let m := ∫ ω, f ω ∂μ
  have hlogdiv : Integrable (fun ω => f ω * Real.log (f ω / m)) μ :=
    integrable_mul_log_div hf hflog hfpos hm
  have hright : Integrable
      (fun ω => f ω * Real.log (f ω / m) - f ω + m * Real.exp (g ω)) μ :=
    (hlogdiv.sub hf).add (hexp.const_mul m)
  have hpoint : (fun ω => f ω * g ω) ≤ᵐ[μ]
      fun ω => f ω * Real.log (f ω / m) - f ω + m * Real.exp (g ω) := by
    filter_upwards [hfpos] with ω hω
    exact scaledYoung hω hm
  have hInt := integral_mono_ae hfg hright hpoint
  have hent : entropy μ f = ∫ ω, f ω * Real.log (f ω / m) ∂μ :=
    entropy_eq_integral_mul_log_div hf hflog hfpos hm
  have hright_eq :
      (∫ ω, f ω * Real.log (f ω / m) - f ω + m * Real.exp (g ω) ∂μ) =
        (∫ ω, f ω * Real.log (f ω / m) ∂μ) -
          (∫ ω, f ω ∂μ) + m * (∫ ω, Real.exp (g ω) ∂μ) := by
    calc
      _ = (∫ ω, f ω * Real.log (f ω / m) - f ω ∂μ) +
          (∫ ω, m * Real.exp (g ω) ∂μ) :=
        integral_add (hlogdiv.sub hf) (hexp.const_mul m)
      _ = _ := by rw [integral_sub hlogdiv hf, integral_const_mul]
  rw [hright_eq] at hInt
  have hm_nonneg : 0 ≤ m := hm.le
  have hmul : m * (∫ ω, Real.exp (g ω) ∂μ) ≤ m := by
    simpa using mul_le_mul_of_nonneg_left hconstraint hm_nonneg
  calc
    (∫ ω, f ω * g ω ∂μ) ≤ ∫ ω, f ω * Real.log (f ω / m) ∂μ := by
      dsimp [m] at hInt hmul ⊢
      nlinarith
    _ = entropy μ f := hent.symm

/-- If [the function `f` is integrable](hyp:hf), [`f log f` is integrable](hyp:hflog),
[`f` is positive almost everywhere](hyp:hfpos), and [its mean is positive](hyp:hm), then
[its entropy is the greatest Gibbs variational value](goal). -/
theorem entropy_isGreatest_dual
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    (hf : Integrable f μ)
    (hflog : Integrable (fun ω => f ω * Real.log (f ω)) μ)
    (hfpos : ∀ᵐ ω ∂μ, 0 < f ω)
    (hm : 0 < ∫ ω, f ω ∂μ) :
    IsGreatest (entropyDualValues μ f) (entropy μ f) := by
  let m := ∫ ω, f ω ∂μ
  let g : Ω → ℝ := fun ω => Real.log (f ω / m)
  have hlogdiv : Integrable (fun ω => f ω * g ω) μ :=
    integrable_mul_log_div hf hflog hfpos hm
  have hexp_eq : (fun ω => Real.exp (g ω)) =ᵐ[μ] fun ω => f ω / m := by
    filter_upwards [hfpos] with ω hω
    exact Real.exp_log (div_pos hω hm)
  have hexp : Integrable (fun ω => Real.exp (g ω)) μ := by
    rw [integrable_congr hexp_eq]
    exact hf.div_const m
  have hexp_mean : (∫ ω, Real.exp (g ω) ∂μ) = 1 := by
    rw [integral_congr_ae hexp_eq, integral_div, show (∫ ω, f ω ∂μ) = m by rfl]
    exact div_self hm.ne'
  have hvalue : (∫ ω, f ω * g ω ∂μ) = entropy μ f :=
    (entropy_eq_integral_mul_log_div hf hflog hfpos hm).symm
  refine ⟨?_, ?_⟩
  · exact ⟨g, hlogdiv, hexp, hexp_mean.le, hvalue.symm⟩
  · intro r hr
    rcases hr with ⟨g', hfg', hexp', hconstraint', rfl⟩
    exact integral_mul_le_entropy hf hflog hfpos hm hfg' hexp' hconstraint'

end Causalean.Stat.Concentration.EntropyMethod

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

/-!
# Conditional expectation under a change of measure

This file proves the abstract Bayes formula for conditional expectation when a
probability measure is changed by a nonnegative normalized density.  It also
specializes the formula to normalized exponential tilts by bounded measurable
functions; strict positivity of an exponential density upgrades the conclusion
from tilted-almost-everywhere to base-almost-everywhere.

Reference: Øksendal, *Stochastic Differential Equations*, 5th ed., Lemma 8.6.2,
equation (8.6.3).
-/

public section

open Filter MeasureTheory Real
open scoped ENNReal

namespace Causalean.Mathlib.MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If [a measurable density is nonnegative](hyp:hw_meas,hw_nonneg), [normalized to have
integral one](hyp:hw_norm), and [the conditioning σ-algebra is contained in the ambient
one](hyp:hm), then [its conditional expectation is strictly positive almost everywhere
under the probability measure having that density](goal). -/
theorem condExp_density_pos_ae [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {w : Ω → ℝ}
    (hw_meas : @Measurable Ω ℝ m₀ _ w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_norm : ∫ x, w x ∂μ = 1) :
    ∀ᵐ x ∂(μ.withDensity fun x => ENNReal.ofReal (w x)), 0 < μ[w | m] x := by
  have hw_int : Integrable w μ := by
    by_contra h
    have hzero := integral_undef h
    rw [hw_norm] at hzero
    norm_num at hzero
  have hden_nonneg : 0 ≤ᵐ[μ] μ[w | m] :=
    condExp_nonneg (Eventually.of_forall hw_nonneg)
  let z : Set Ω := {x | μ[w | m] x = 0}
  have hz_m : MeasurableSet[m] z := by
    exact (stronglyMeasurable_condExp (μ := μ) (m := m) (f := w)).measurable
      (measurableSet_singleton 0)
  have hz : @MeasurableSet Ω m₀ z := hm z hz_m
  have hw_zero_on_z : w =ᵐ[μ.restrict z] 0 := by
    apply (setIntegral_eq_zero_iff_of_nonneg_ae
      ((Eventually.of_forall hw_nonneg).filter_mono ae_restrict_le)
      hw_int.integrableOn).mp
    rw [← setIntegral_condExp hm hw_int hz_m]
    exact setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun x hx => hx)
  rw [ae_withDensity_iff (hw_meas.ennreal_ofReal)]
  filter_upwards [hden_nonneg,
    (ae_restrict_iff' hz).mp hw_zero_on_z] with x hden hx hweight
  rcases lt_or_eq_of_le hden with hpos | hzero
  · exact hpos
  · exfalso
    have hw0 : w x = 0 := hx (by simpa [z] using hzero.symm)
    exact hweight (by simp [hw0])

/-- **Abstract conditional Bayes formula.** If [a measurable density is
nonnegative](hyp:hw_meas,hw_nonneg), [normalized to have integral one](hyp:hw_norm),
[the conditioning σ-algebra is contained in the ambient one](hyp:hm), and [the target
function is integrable under the density-changed measure](hyp:hf), then [its conditional
expectation under that measure is the base-measure conditional expectation of the
density-weighted target divided by the conditional expectation of the density](goal),
almost everywhere under the changed measure. -/
theorem condExp_withDensity_ae_eq_div [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {w f : Ω → ℝ}
    (hw_meas : @Measurable Ω ℝ m₀ _ w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_norm : ∫ x, w x ∂μ = 1)
    (hf : Integrable f (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    @MeasureTheory.condExp Ω ℝ m m₀ _ _
      (μ.withDensity fun x => ENNReal.ofReal (w x)) f =ᵐ[
      μ.withDensity fun x => ENNReal.ofReal (w x)]
      fun x => μ[fun y => f y * w y | m] x / μ[w | m] x := by
  let ν : @Measure Ω m₀ := μ.withDensity fun x => ENNReal.ofReal (w x)
  have hw_int : Integrable w μ := by
    by_contra h
    have hzero := integral_undef h
    rw [hw_norm] at hzero
    norm_num at hzero
  have hdens_meas : @Measurable Ω ENNReal m₀ _ (fun x => ENNReal.ofReal (w x)) :=
    hw_meas.ennreal_ofReal
  have hdens_lt_top : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hν_prob : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hw_int
        (Eventually.of_forall hw_nonneg), hw_norm]
    norm_num
  let _ : IsProbabilityMeasure ν := by simpa only [ν] using hν_prob
  have hf_weight : Integrable (fun x => f x * w x) μ := by
    have h := (integrable_withDensity_iff hdens_meas hdens_lt_top).mp hf
    simpa [ν, ENNReal.toReal_ofReal, hw_nonneg] using h
  have hcond_weight : Integrable (fun x => ν[f | m] x * w x) μ := by
    have hν : Integrable (ν[f | m]) ν := integrable_condExp
    have h := (integrable_withDensity_iff hdens_meas hdens_lt_top).mp hν
    simpa [ν, ENNReal.toReal_ofReal, hw_nonneg] using h
  have hpull : μ[(fun x => ν[f | m] x * w x) | m] =ᵐ[μ]
      fun x => ν[f | m] x * μ[w | m] x := by
    exact condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_condExp (μ := ν) (m := m) (f := f)) hcond_weight hw_int
  have hcandidate_int : Integrable (fun x => ν[f | m] x * μ[w | m] x) μ :=
    integrable_condExp.congr hpull
  have hcandidate_meas : AEStronglyMeasurable[m]
      (fun x => ν[f | m] x * μ[w | m] x) μ :=
    ((stronglyMeasurable_condExp (μ := ν) (m := m) (f := f)).mul
      (stronglyMeasurable_condExp (μ := μ) (m := m) (f := w))).aestronglyMeasurable
  have hproduct : (fun x => ν[f | m] x * μ[w | m] x) =ᵐ[μ]
      μ[fun y => f y * w y | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hf_weight
      (fun _ _ _ => hcandidate_int.integrableOn) _ hcandidate_meas
    intro s hs _
    have hs₀ : @MeasurableSet Ω m₀ s := hm s hs
    calc
      ∫ x in s, ν[f | m] x * μ[w | m] x ∂μ =
          ∫ x in s, μ[(fun y => ν[f | m] y * w y) | m] x ∂μ :=
        setIntegral_congr_ae hs₀ (hpull.symm.mono fun _ h _ => h)
      _ = ∫ x in s, ν[f | m] x * w x ∂μ :=
        setIntegral_condExp hm hcond_weight hs
      _ = ∫ x in s, ν[f | m] x ∂ν := by
        symm
        rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) from rfl,
          @setIntegral_withDensity_eq_setIntegral_toReal_smul Ω ℝ m₀ μ _ _
            (fun x => ENNReal.ofReal (w x)) s hdens_meas
            (hdens_lt_top.filter_mono (@ae_restrict_le Ω m₀ μ s))
            (fun x => ν[f | m] x) hs₀]
        apply setIntegral_congr_ae (mX := m₀) hs₀
        filter_upwards with x _
        simp [ν, ENNReal.toReal_ofReal, hw_nonneg, mul_comm]
      _ = ∫ x in s, f x ∂ν := setIntegral_condExp hm hf hs
      _ = ∫ x in s, f x * w x ∂μ := by
        rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) from rfl,
          @setIntegral_withDensity_eq_setIntegral_toReal_smul Ω ℝ m₀ μ _ _
            (fun x => ENNReal.ofReal (w x)) s hdens_meas
            (hdens_lt_top.filter_mono (@ae_restrict_le Ω m₀ μ s)) f hs₀]
        apply setIntegral_congr_ae (mX := m₀) hs₀
        filter_upwards with x _
        rw [ENNReal.toReal_ofReal (hw_nonneg x)]
        simp [smul_eq_mul, mul_comm]
  have hproduct_ν : (fun x => ν[f | m] x * μ[w | m] x) =ᵐ[ν]
      μ[fun y => f y * w y | m] :=
    hproduct.filter_mono (withDensity_absolutelyContinuous μ _).ae_le
  have hpos : ∀ᵐ x ∂ν, 0 < μ[w | m] x := by
    simpa [ν] using condExp_density_pos_ae hm hw_meas hw_nonneg hw_norm
  filter_upwards [hproduct_ν, hpos] with x hprod hx
  exact (eq_div_iff (ne_of_gt hx)).2 hprod

/-- **Conditional Bayes formula for bounded exponential tilts.** If [the conditioning
σ-algebra is contained in the ambient one](hyp:hm), [the score is measurable](hyp:hs_meas)
and [bounded](hyp:hs_bound), and [the target is integrable under the normalized
exponential tilt](hyp:hf), then [the conditional Bayes ratio for the density
`exp (t s) / ∫ exp (t s) dμ` holds almost everywhere under the base measure](goal).

Boundedness makes the exponential integrable and its normalizer finite and strictly
positive.  The density is therefore strictly positive, so the tilted and base measures
have the same null sets. -/
theorem condExp_expTilt_ae_eq_div [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {s f : Ω → ℝ} (t : ℝ)
    (hs_meas : @Measurable Ω ℝ m₀ _ s) (hs_bound : ∃ C : ℝ, ∀ x, |s x| ≤ C)
    (hf : Integrable f (μ.withDensity fun x => ENNReal.ofReal
      (Real.exp (t * s x) / ∫ y, Real.exp (t * s y) ∂μ))) :
    @MeasureTheory.condExp Ω ℝ m m₀ _ _ (μ.withDensity fun x => ENNReal.ofReal
      (Real.exp (t * s x) / ∫ y, Real.exp (t * s y) ∂μ)) f =ᵐ[μ]
      fun x =>
        μ[fun y => f y * (Real.exp (t * s y) / ∫ z, Real.exp (t * s z) ∂μ) | m] x /
          μ[fun y => Real.exp (t * s y) / ∫ z, Real.exp (t * s z) ∂μ | m] x := by
  rcases hs_bound with ⟨C, hs_bound⟩
  let e : Ω → ℝ := fun x => Real.exp (t * s x)
  let c : ℝ := ∫ x, e x ∂μ
  let w : Ω → ℝ := fun x => e x / c
  have he_meas : @Measurable Ω ℝ m₀ _ e := by
    dsimp [e]
    fun_prop
  have he_int : Integrable e μ := by
    apply Integrable.of_bound (μ := μ) he_meas.aestronglyMeasurable (Real.exp (|t| * C))
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs_bound x) (abs_nonneg t))
  have hc_pos : 0 < c := by
    have hlower : ∀ x, Real.exp (-|t| * C) ≤ e x := by
      intro x
      apply Real.exp_le_exp.mpr
      calc
        -|t| * C = -(|t| * C) := by ring
        _ ≤ -|t * s x| := neg_le_neg (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hs_bound x) (abs_nonneg t))
        _ ≤ t * s x := neg_abs_le _
    calc
      0 < Real.exp (-|t| * C) := Real.exp_pos _
      _ = ∫ _ : Ω, Real.exp (-|t| * C) ∂μ := by
        rw [integral_const, probReal_univ, one_smul]
      _ ≤ c := by
        dsimp [c]
        exact integral_mono (integrable_const _) he_int hlower
  have hw_meas : @Measurable Ω ℝ m₀ _ w := by
    dsimp [w]
    fun_prop
  have hw_pos : ∀ x, 0 < w x := fun x => div_pos (Real.exp_pos _) hc_pos
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => (hw_pos x).le
  have hw_norm : ∫ x, w x ∂μ = 1 := by
    dsimp [w, c]
    rw [integral_div]
    exact div_self hc_pos.ne'
  have hbayes := condExp_withDensity_ae_eq_div hm hw_meas hw_nonneg hw_norm hf
  have hdens_meas : @Measurable Ω ENNReal m₀ _ (fun x => ENNReal.ofReal (w x)) :=
    hw_meas.ennreal_ofReal
  have hbase : @MeasureTheory.condExp Ω ℝ m m₀ _ _
      (μ.withDensity fun x => ENNReal.ofReal (w x)) f =ᵐ[μ]
      fun x => μ[fun y => f y * w y | m] x / μ[w | m] x := by
    have htilt := (ae_withDensity_iff hdens_meas).mp hbayes
    filter_upwards [htilt] with x hx
    exact hx (ENNReal.ofReal_ne_zero_iff.mpr (hw_pos x))
  simpa [w, e, c] using hbase

end Causalean.Mathlib.MeasureTheory

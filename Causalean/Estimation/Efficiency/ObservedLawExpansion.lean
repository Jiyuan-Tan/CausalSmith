/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ObservedLawATE
public import Causalean.Tactic.IntegralLinearity

/-!
# Exact doubly-robust expansion for the observed-law ATE

This module proves the conditional-expectation algebra behind the exact AIPW
remainder.  The main identity compares two observed-data laws and expresses
the failure of the base-law AIPW function to be exactly affine as a product of
the propensity and arm-regression changes.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory ProbabilityTheory
open _root_.Causalean.Estimation.ATE.BackdoorEstimationSystem

variable {γ : Type*} [MeasurableSpace γ]

/-- For [a probability law `Q`](hyp:Q) and [an arm `d`](hyp:d), [the arm indicator is
integrable](goal). -/
@[fun_prop] lemma integrable_observedArmIndicator
    (Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q] (d : Bool) :
    Integrable (observedArmIndicator d) Q := by
  apply Integrable.of_bound (measurable_observedArmIndicator d).aestronglyMeasurable 1
  filter_upwards with z
  by_cases h : projA z = d <;> simp [observedArmIndicator, h]

/-- For [a probability law `Q`](hyp:Q) and [an arm `d`](hyp:d), [the recomputed arm
propensity lies between zero and one](goal) almost everywhere. -/
lemma observedPropensity_mem_Icc_ae
    (Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q] (d : Bool) :
    ∀ᵐ z ∂Q, 0 ≤ observedPropensity Q d z ∧ observedPropensity Q d z ≤ 1 := by
  have hnonneg : 0 ≤ᵐ[Q] observedPropensity Q d :=
    condExp_nonneg (Eventually.of_forall fun z => by
      by_cases h : projA z = d <;> simp [observedArmIndicator, h])
  have hmono : observedPropensity Q d ≤ᵐ[Q] (fun _ => (1 : ℝ)) := by
    have h := condExp_mono (m := observedCovariateSigma)
      (integrable_observedArmIndicator Q d)
      (integrable_const (1 : ℝ)) (Eventually.of_forall fun z => by
        by_cases hz : projA z = d <;> simp [observedArmIndicator, hz])
    simpa [observedPropensity, condExp_const observedCovariateSigma_le (1 : ℝ)] using h
  exact hnonneg.and hmono

/-- For [a probability law `Q`](hyp:Q) and [an arm `d`](hyp:d), [the recomputed arm
propensity is integrable](goal). -/
@[fun_prop] lemma integrable_observedPropensity
    (Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q] (d : Bool) :
    Integrable (observedPropensity Q d) Q :=
  integrable_condExp

/-- If [the conditioning σ-algebra is contained in the ambient one](hyp:hm), [a weight `h`
is measurable for that σ-algebra](hyp:hh), [bounded](hyp:hh_bound), and [a target `f` is
integrable](hyp:hf), then [integrating `h f` is unchanged by replacing `f` with its
conditional expectation](goal). -/
lemma integral_mul_eq_integral_mul_condExp
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {Q : Measure Ω} [IsFiniteMeasure Q]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {h f : Ω → ℝ}
    (hh : StronglyMeasurable[m] h) (C : ℝ) (hh_bound : ∀ᵐ z ∂Q, |h z| ≤ C)
    (hf : Integrable f Q) :
    ∫ z, h z * f z ∂Q = ∫ z, h z * Q[f | m] z ∂Q := by
  have hh_norm : ∀ᵐ z ∂Q, ‖h z‖ ≤ C := by
    simpa [Real.norm_eq_abs] using hh_bound
  have hprod : Integrable (h * f) Q :=
    hf.bdd_mul (hh.mono hm).aestronglyMeasurable hh_norm
  calc
    ∫ z, h z * f z ∂Q = ∫ z, Q[h * f | m] z ∂Q :=
      (integral_condExp (μ := Q) (f := h * f) hm).symm
    _ = ∫ z, h z * Q[f | m] z ∂Q := integral_congr_ae
      (condExp_mul_of_stronglyMeasurable_left hh hprod hf)

/-- Let [the evaluation law `Q`](hyp:Q) be a probability law, fix [an arm `d`](hyp:d), and
compare [base-law nuisance functions from `Q₀`](hyp:Q₀) with the nuisances recomputed under
`Q`. If [the outcome and both arm regressions are integrable](hyp:hY,hμ0,hμ1), [the inverse
base propensity is bounded](hyp:hinv), and [the evaluation-law arm propensity is positive](hyp:hp),
then [the inverse-base-propensity residual integral equals the propensity ratio times the
arm-regression change](goal). -/
lemma integral_weighted_observed_residual
    (Q₀ Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q]
    (d : Bool) (C : ℝ)
    (hY : Integrable (projY : γ × Bool × ℝ → ℝ) Q)
    (hμ0 : Integrable (observedArmRegression Q₀ d) Q)
    (hμ1 : Integrable (observedArmRegression Q d) Q)
    (hinv : ∀ᵐ z ∂Q, |(observedPropensity Q₀ d z)⁻¹| ≤ C)
    (hp : ∀ᵐ z ∂Q, 0 < observedPropensity Q d z) :
    ∫ z, observedArmIndicator d z / observedPropensity Q₀ d z *
        (projY z - observedArmRegression Q₀ d z) ∂Q =
      ∫ z, observedPropensity Q d z / observedPropensity Q₀ d z *
        (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q := by
  let I : γ × Bool × ℝ → ℝ := observedArmIndicator d
  let p₀ : γ × Bool × ℝ → ℝ := observedPropensity Q₀ d
  let p : γ × Bool × ℝ → ℝ := observedPropensity Q d
  let μ₀ : γ × Bool × ℝ → ℝ := observedArmRegression Q₀ d
  let μ : γ × Bool × ℝ → ℝ := observedArmRegression Q d
  let Y : γ × Bool × ℝ → ℝ := projY
  have hI : Integrable I Q := integrable_observedArmIndicator Q d
  have hp_int : Integrable p Q := integrable_observedPropensity Q d
  have hIY : Integrable (fun z => I z * Y z) Q := by
    have hI_bound : ∀ᵐ z ∂Q, ‖I z‖ ≤ 1 := by
      filter_upwards with z
      by_cases hz : projA z = d <;> simp [I, observedArmIndicator, hz]
    exact hY.bdd_mul (measurable_observedArmIndicator d).aestronglyMeasurable hI_bound
  have hIμ₀ : Integrable (fun z => I z * μ₀ z) Q := by
    have hI_bound : ∀ᵐ z ∂Q, ‖I z‖ ≤ 1 := by
      filter_upwards with z
      by_cases hz : projA z = d <;> simp [I, observedArmIndicator, hz]
    exact hμ0.bdd_mul (measurable_observedArmIndicator d).aestronglyMeasurable hI_bound
  have hres : Integrable (fun z => I z * (Y z - μ₀ z)) Q := by
    refine (hIY.sub hIμ₀).congr ?_
    filter_upwards with z
    simp only [Pi.sub_apply, mul_sub]
  have hinv_meas : StronglyMeasurable[observedCovariateSigma]
      (fun z => (p₀ z)⁻¹) := by
    dsimp [p₀]
    fun_prop
  have hpμ₀ : Integrable (fun z => p z * μ₀ z) Q := by
    have hp_bound : ∀ᵐ z ∂Q, ‖p z‖ ≤ 1 := by
      filter_upwards [observedPropensity_mem_Icc_ae Q d] with z hz
      simpa [p, Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2
    exact hμ0.bdd_mul (measurable_observedPropensity Q d).aestronglyMeasurable hp_bound
  have hcond_sub : Q[fun z => I z * (Y z - μ₀ z) | observedCovariateSigma] =ᵐ[Q]
      fun z => observedArmNumerator Q d z - μ₀ z * p z := by
    have hsub := condExp_sub hIY hIμ₀ observedCovariateSigma
    have hpull := condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_observedArmRegression Q₀ d) hIμ₀ hI
    have hce : Q[fun z => I z * (Y z - μ₀ z) | observedCovariateSigma] =ᵐ[Q]
        Q[(fun z => I z * Y z) - (fun z => I z * μ₀ z) |
          observedCovariateSigma] :=
      condExp_congr_ae (Eventually.of_forall fun z => by simp [mul_sub])
    have hIYce : Q[fun z => I z * Y z | observedCovariateSigma] =ᵐ[Q]
        observedArmNumerator Q d := by
      apply condExp_congr_ae
      filter_upwards with z
      simp [I, Y, observedArmNumerator, mul_comm]
    filter_upwards [hce, hsub, hpull, hIYce]
      with z hcez hsubz hpullz hIYcez
    change Q[fun w => I w * μ₀ w | observedCovariateSigma] z =
      p z * μ₀ z at hpullz
    rw [hcez, hsubz]
    change Q[fun w => I w * Y w | observedCovariateSigma] z -
      Q[fun w => I w * μ₀ w | observedCovariateSigma] z = _
    rw [hIYcez, hpullz]
    ring
  have hnum : ∀ᵐ z ∂Q, observedArmNumerator Q d z = p z * μ z := by
    filter_upwards [hp] with z hpz
    dsimp [μ, observedArmRegression, p]
    field_simp
  have hrewrite : Q[fun z => I z * (Y z - μ₀ z) | observedCovariateSigma] =ᵐ[Q]
      fun z => p z * (μ z - μ₀ z) := by
    filter_upwards [hcond_sub, hnum] with z hcond hnumz
    rw [hcond, hnumz]
    ring
  calc
    ∫ z, I z / p₀ z * (Y z - μ₀ z) ∂Q =
        ∫ z, (p₀ z)⁻¹ * (I z * (Y z - μ₀ z)) ∂Q := by
          apply integral_congr_ae
          filter_upwards with z
          ring
    _ = ∫ z, (p₀ z)⁻¹ *
          Q[fun w => I w * (Y w - μ₀ w) | observedCovariateSigma] z ∂Q :=
      integral_mul_eq_integral_mul_condExp observedCovariateSigma_le
        hinv_meas C hinv hres
    _ = ∫ z, (p₀ z)⁻¹ * (p z * (μ z - μ₀ z)) ∂Q :=
      integral_congr_ae ((EventuallyEq.rfl.mul hrewrite))
    _ = ∫ z, p z / p₀ z * (μ z - μ₀ z) ∂Q := by
      apply integral_congr_ae
      filter_upwards with z
      ring

/-- **Exact treatment-specific-mean expansion.** Compare [a base probability law
`Q₀`](hyp:Q₀) with [an evaluation probability law `Q`](hyp:Q) for [one treatment
arm `d`](hyp:d). If [the outcome and both arm regressions are integrable](hyp:hY,hμ0,hμ1),
[the inverse base propensity is bounded](hyp:hinv), [both relevant propensities are
positive](hyp:hp0,hp), and [the residual and product terms are integrable](hyp:hres,hprod),
then [the arm-mean change minus the evaluation-law mean of the base EIF is exactly minus
the product of the propensity and outcome-regression errors](goal). -/
theorem observedArmMean_sub_integral_observedArmEIF_eq_product
    (Q₀ Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q]
    (d : Bool) (C : ℝ)
    (hY : Integrable (projY : γ × Bool × ℝ → ℝ) Q)
    (hμ0 : Integrable (observedArmRegression Q₀ d) Q)
    (hμ1 : Integrable (observedArmRegression Q d) Q)
    (hinv : ∀ᵐ z ∂Q, |(observedPropensity Q₀ d z)⁻¹| ≤ C)
    (hp0 : ∀ᵐ z ∂Q, 0 < observedPropensity Q₀ d z)
    (hp : ∀ᵐ z ∂Q, 0 < observedPropensity Q d z)
    (hres : Integrable (fun z =>
      observedArmIndicator d z / observedPropensity Q₀ d z *
        (projY z - observedArmRegression Q₀ d z)) Q)
    (hprod : Integrable (fun z =>
      (observedPropensity Q d z - observedPropensity Q₀ d z) /
        observedPropensity Q₀ d z *
          (observedArmRegression Q d z - observedArmRegression Q₀ d z)) Q) :
    observedArmMean Q d - observedArmMean Q₀ d -
        ∫ z, observedArmEIF Q₀ d z ∂Q =
      -(∫ z, (observedPropensity Q d z - observedPropensity Q₀ d z) /
          observedPropensity Q₀ d z *
            (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q) := by
  have hr := integral_weighted_observed_residual Q₀ Q d C hY hμ0 hμ1 hinv hp
  have hratio :
      ∫ z, observedPropensity Q d z / observedPropensity Q₀ d z *
          (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q =
        ∫ z, observedArmRegression Q d z - observedArmRegression Q₀ d z ∂Q +
          ∫ z, (observedPropensity Q d z - observedPropensity Q₀ d z) /
            observedPropensity Q₀ d z *
              (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q := by
    calc
      _ = ∫ z, (observedArmRegression Q d z - observedArmRegression Q₀ d z) +
          (observedPropensity Q d z - observedPropensity Q₀ d z) /
            observedPropensity Q₀ d z *
              (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hp0] with z hz
        field_simp
        ring
      _ = _ := integral_add (hμ1.sub hμ0) hprod
  have hconst : Integrable (fun _ : γ × Bool × ℝ => observedArmMean Q₀ d) Q :=
    integrable_const _
  unfold observedArmMean observedArmEIF
  integral_linearity
  rw [integral_const, probReal_univ, one_smul, hr, hratio,
    integral_sub hμ1 hμ0]
  rw [show observedArmMean Q₀ d = ∫ z, observedArmRegression Q₀ d z ∂Q₀ from rfl]
  ring

/-- **Exact doubly-robust observed-law expansion.** Compare [a base probability law
`Q₀`](hyp:Q₀) with [an evaluation probability law `Q`](hyp:Q). Assume [integrability of the
outcome and both laws' arm regressions](hyp:hY,hμ0,hμ1), [bounded inverse base arm
propensities](hyp:hinv), [positive arm propensities under both laws](hyp:hp0,hp), and the
resulting [residual and product integrability gates](hyp:hres,hprod). Then [the ATE change
minus the mean of the base-law AIPW function equals exactly the sum of products of propensity
and arm-regression errors](goal). -/
theorem observedATE_sub_integral_observedAIPW_eq_product
    (Q₀ Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q]
    (C : Bool → ℝ)
    (hY : Integrable (projY : γ × Bool × ℝ → ℝ) Q)
    (hμ0 : ∀ d, Integrable (observedArmRegression Q₀ d) Q)
    (hμ1 : ∀ d, Integrable (observedArmRegression Q d) Q)
    (hinv : ∀ d, ∀ᵐ z ∂Q, |(observedPropensity Q₀ d z)⁻¹| ≤ C d)
    (hp0 : ∀ d, ∀ᵐ z ∂Q, 0 < observedPropensity Q₀ d z)
    (hp : ∀ d, ∀ᵐ z ∂Q, 0 < observedPropensity Q d z)
    (hres : ∀ d, Integrable (fun z =>
      observedArmIndicator d z / observedPropensity Q₀ d z *
        (projY z - observedArmRegression Q₀ d z)) Q)
    (hprod : ∀ d, Integrable (fun z =>
      (observedPropensity Q d z - observedPropensity Q₀ d z) /
        observedPropensity Q₀ d z *
          (observedArmRegression Q d z - observedArmRegression Q₀ d z)) Q) :
    observedATE Q - observedATE Q₀ - ∫ z, observedAIPW Q₀ z ∂Q =
      -(∫ z, (observedPropensity Q true z - observedPropensity Q₀ true z) /
          observedPropensity Q₀ true z *
            (observedArmRegression Q true z - observedArmRegression Q₀ true z) ∂Q) +
        ∫ z, (observedPropensity Q false z - observedPropensity Q₀ false z) /
          observedPropensity Q₀ false z *
            (observedArmRegression Q false z - observedArmRegression Q₀ false z) ∂Q := by
  have hr (d : Bool) := integral_weighted_observed_residual Q₀ Q d (C d) hY
    (hμ0 d) (hμ1 d) (hinv d) (hp d)
  have hratio (d : Bool) :
      ∫ z, observedPropensity Q d z / observedPropensity Q₀ d z *
          (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q =
        ∫ z, observedArmRegression Q d z - observedArmRegression Q₀ d z ∂Q +
          ∫ z, (observedPropensity Q d z - observedPropensity Q₀ d z) /
            observedPropensity Q₀ d z *
              (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q := by
    calc
      _ = ∫ z, (observedArmRegression Q d z - observedArmRegression Q₀ d z) +
          (observedPropensity Q d z - observedPropensity Q₀ d z) /
            observedPropensity Q₀ d z *
              (observedArmRegression Q d z - observedArmRegression Q₀ d z) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hp0 d] with z hz
        field_simp
        ring
      _ = _ := integral_add ((hμ1 d).sub (hμ0 d)) (hprod d)
  unfold observedATE observedAIPW
  have hconst : Integrable (fun _ : γ × Bool × ℝ => observedATE Q₀) Q :=
    integrable_const _
  integral_linearity
  rw [integral_const, probReal_univ, one_smul]
  rw [hr true, hr false, hratio true, hratio false]
  rw [integral_sub (hμ1 true) (hμ0 true),
    integral_sub (hμ1 false) (hμ0 false)]
  rw [show observedATE Q₀ = ∫ z, observedArmRegression Q₀ true z -
      observedArmRegression Q₀ false z ∂Q₀ from rfl]
  change _ - (∫ z, observedArmRegression Q₀ true z -
      observedArmRegression Q₀ false z ∂Q₀) - _ = _
  ring

end Causalean.Estimation.Efficiency

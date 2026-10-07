/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The van Trees inequality (Bayesian Cramer-Rao bound)

This file states and proves the classical single-parameter **van Trees
inequality** `van_trees_inequality`: a Bayesian analogue of the Cramer-Rao lower bound for the
mean-squared error of estimating a smooth functional of a random parameter.

Setup (an econometrician's reading). A scalar parameter `h` is drawn from a
prior with a continuously differentiable density `q` supported on `[a, b]` that
vanishes at both endpoints (`q a = q b = 0`); its prior Fisher information is
`I_q = ∫ q'(h)² / q(h) dh`. Given `h`, data `Z` are drawn from a law `P h` with
score function `S h` (mean zero under `P h`) and Fisher information
`I(h) = E_h[S h ²]`. For any estimator `δ(Z)` of a differentiable scalar target
`ψ(h)`, the average (Bayes) mean-squared error is bounded below by

  `(∫ ψ'(h) q(h) dh)² / (I_q + ∫ I(h) q(h) dh)`.

The denominator adds the *prior* information `I_q` to the *average experimental*
information `∫ I(h) q(h) dh`; the numerator is the squared average sensitivity of
the target. Because the prior information appears additively, the bound stays
finite even where the frequentist Cramer-Rao bound degenerates, which is why the
van Trees inequality is the standard device for proving minimax lower bounds.

The canonical theorem derives the estimator-specific differentiation identity
from model-level likelihood regularity through the observation-dependent van
Trees engine.
-/

public section

namespace Causalean.Stat.Minimax

open MeasureTheory intervalIntegral Set

/-- **Classical parameter-only van Trees inequality.** For [a dominating observation
measure](hyp:μ), [parameter endpoints](hyp:ell,u), [a prior and its derivative](hyp:w,dw),
[a likelihood and its derivative](hyp:p,dp), [a parameter-only target and its
derivative](hyp:ψ,dψ), and [an estimator](hyp:T), [a nondegenerate interval and the stated
prior, model, target, boundary, measurability, integrability, and positive-information
conditions](hyp:hellu,hwC1,hwderiv,hwnonneg,hpnonneg,hpnorm,hdiffUnder,hpAC,hψAC,hdp,hψderiv,hboundary,hbalanceInt,herrorScoreSm,herrorScoreInt,hsensitivityInt,herrorSqSm,herrorSqInt,hscoreSqSm,hscoreSqInt,hpriorJointSqInt,hfisherSqInt,hcrossInt,hinfoPos),
[the squared prior-average derivative divided by prior plus average likelihood information is
at most the prior-average mean-squared error](goal).

This is a scalar, unweighted specialization of Gill--Levit (1995), Theorem 1, obtained by taking
one-dimensional parameters and targets with scalar unit weight. It specializes the
observation-dependent theorem with `g θ x = ψ θ`; the estimator-specific differentiation
identity is derived from model regularity. -/
theorem van_trees_inequality
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ell u : ℝ} (hellu : ell < u)
    (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ) (ψ dψ : ℝ → ℝ) (T : X → ℝ)
    (hwC1 : ContDiff ℝ 1 w)
    (hwderiv : ∀ θ, HasDerivAt w (dw θ) θ)
    (hwnonneg : ∀ θ, 0 ≤ w θ)
    (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    (hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂μ = 1)
    (hdiffUnder : ∀ θ ∈ Ioo ell u,
      HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ)
    (hpAC : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u)
    (hψAC : AbsolutelyContinuousOnInterval ψ ell u)
    (hdp : ∀ᵐ z ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ),
      HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1)
    (hψderiv : ∀ θ, HasDerivAt ψ (dψ θ) θ)
    (hboundary : ∀ᵐ x ∂μ,
      w u * p u x * (T x - ψ u) = 0 ∧ w ell * p ell x * (T x - ψ ell) = 0)
    (hbalanceInt : Integrable
      (ObservationDependentVanTrees.derivativeBalanceField w dw p dp
        (fun θ _ => ψ θ) (fun θ _ => dψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorScoreSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.errorScoreField w dw p dp (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorScoreInt : Integrable
      (ObservationDependentVanTrees.errorScoreField w dw p dp (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hsensitivityInt : Integrable
      (ObservationDependentVanTrees.sensitivityField w p (fun θ _ => dψ θ))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorSqSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.errorSqField w p (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorSqInt : Integrable
      (ObservationDependentVanTrees.errorSqField w p (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hscoreSqSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.scoreSqField w dw p dp)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hscoreSqInt : Integrable (ObservationDependentVanTrees.scoreSqField w dw p dp)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hpriorJointSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hfisherSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hcrossInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1 *
          ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hinfoPos : 0 < ObservationDependentVanTrees.priorInformation ell u w dw +
      ∫ θ, w θ * ObservationDependentVanTrees.fisherInformation μ p dp θ
        ∂ObservationDependentVanTrees.parameterMeasure ell u) :
    (∫ θ, dψ θ * w θ ∂ObservationDependentVanTrees.parameterMeasure ell u) ^ 2 /
        (ObservationDependentVanTrees.priorInformation ell u w dw +
          ∫ θ, w θ * ObservationDependentVanTrees.fisherInformation μ p dp θ
            ∂ObservationDependentVanTrees.parameterMeasure ell u) ≤
      ∫ θ, (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
        ∂ObservationDependentVanTrees.parameterMeasure ell u := by
  letI : IsFiniteMeasure (ObservationDependentVanTrees.parameterMeasure ell u) := by
    unfold ObservationDependentVanTrees.parameterMeasure
    infer_instance
  let g : ℝ → X → ℝ := fun θ _ => ψ θ
  let dg : ℝ → X → ℝ := fun θ _ => dψ θ
  have hraw := ObservationDependentVanTrees.observation_dependent_van_trees μ hellu
    w dw p dp g dg T hwC1 hwderiv hwnonneg hpnonneg hpnorm
    hdiffUnder hpAC (Filter.Eventually.of_forall fun _ => hψAC) hdp
    (Filter.Eventually.of_forall fun z => hψderiv z.1) hboundary hbalanceInt
    herrorScoreSm herrorScoreInt hsensitivityInt herrorSqSm herrorSqInt
    hscoreSqSm hscoreSqInt hpriorJointSqInt
    hfisherSqInt hcrossInt hinfoPos
  have hsensitivity :
      ∫ z, ObservationDependentVanTrees.sensitivityField w p dg z
          ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ) =
        ∫ θ, dψ θ * w θ ∂ObservationDependentVanTrees.parameterMeasure ell u := by
    rw [integral_prod _ hsensitivityInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    change (∫ x, dψ θ * (w θ * p θ x) ∂μ) = dψ θ * w θ
    rw [show (fun x => dψ θ * (w θ * p θ x)) =
        fun x => (dψ θ * w θ) * p θ x by funext x; ring,
      MeasureTheory.integral_const_mul, hpnorm θ hθ, mul_one]
  have hrisk :
      ∫ z, ObservationDependentVanTrees.errorSqField w p g T z
          ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ) =
        ∫ θ, (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
          ∂ObservationDependentVanTrees.parameterMeasure ell u := by
    rw [integral_prod _ herrorSqInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    change (∫ x, (T x - ψ θ) ^ 2 * (w θ * p θ x) ∂μ) =
      (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
    rw [show (fun x => (T x - ψ θ) ^ 2 * (w θ * p θ x)) =
        fun x => ((T x - ψ θ) ^ 2 * p θ x) * w θ by funext x; ring,
      MeasureTheory.integral_mul_const]
  simpa [g, dg, hsensitivity, hrisk] using hraw

end Causalean.Stat.Minimax

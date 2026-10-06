/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.VanTreesInequality
public import Mathlib.MeasureTheory.Function.L2Space

/-! # A model-level entry point for the van Trees inequality

This file packages the smooth dominated-model assumptions for the classical
parameter-only van Trees inequality. Weighted L² hypotheses on the estimation
error and the three relevant scores automatically discharge the product,
square, cross, and strong-measurability obligations of the underlying proof.
-/

@[expose] public section

namespace Causalean.Stat.Minimax

open MeasureTheory Set
open ObservationDependentVanTrees

/-- Smooth van Trees regularity consists of [a C¹ compactly supported,
nonnegative, normalized prior with the stated derivative](hyp:hwC1,hwsupport,hwderiv,hwnonneg,hwnorm),
[a nonnegative normalized dominated likelihood with integrable derivative and valid
differentiation under the integral](hyp:hpnonneg,hpnorm,hpint,hdpint,hdiffUnder),
[absolutely continuous likelihood and target sections with the stated joint derivative
representatives](hyp:hpAC,hψAC,hdp,hψderiv), [vanishing boundary errors](hyp:hboundary),
[weighted L² joint-density root, target derivative, estimation error, joint score, prior
score, and likelihood score](hyp:hjointSqrtL2,htargetDerivativeL2,herrorL2,hjointScoreL2,hpriorJointScoreL2,hlikelihoodScoreL2),
[finite prior information](hyp:hpriorSqInt), and [positive total information](hyp:hinfoPos).

These are model-level smoothness, finite-risk, and finite-information
conditions. Cauchy–Schwarz derives every error-score and prior-likelihood cross
integrability condition used internally by the product-measure proof. -/
structure VanTreesSmoothModelRegularity
    (X : Type*) [MeasurableSpace X] (μ : Measure X)
    (ell u : ℝ) (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ)
    (ψ dψ : ℝ → ℝ) (T : X → ℝ) : Prop where
  hwC1 : ContDiff ℝ 1 w
  hwsupport : Function.support w ⊆ Icc ell u
  hwderiv : ∀ θ, HasDerivAt w (dw θ) θ
  hwnonneg : ∀ θ, 0 ≤ w θ
  hwnorm : ∫ θ, w θ ∂parameterMeasure ell u = 1
  hpnonneg : ∀ θ x, 0 ≤ p θ x
  hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂μ = 1
  hpint : ∀ θ ∈ Icc ell u, Integrable (fun x => p θ x) μ
  hdpint : ∀ θ ∈ Icc ell u, Integrable (fun x => dp θ x) μ
  hdiffUnder : ∀ θ ∈ Ioo ell u,
    HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ
  hpAC : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u
  hψAC : AbsolutelyContinuousOnInterval ψ ell u
  hdp : ∀ᵐ z ∂((parameterMeasure ell u).prod μ),
    HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1
  hψderiv : ∀ θ, HasDerivAt ψ (dψ θ) θ
  hboundary : ∀ᵐ x ∂μ,
    w u * p u x * (T x - ψ u) = 0 ∧ w ell * p ell x * (T x - ψ ell) = 0
  hjointSqrtL2 : MemLp (fun z : ℝ × X => Real.sqrt (jointDensity w p z)) 2
    ((parameterMeasure ell u).prod μ)
  htargetDerivativeL2 : MemLp (fun z : ℝ × X =>
    Real.sqrt (jointDensity w p z) * dψ z.1) 2
    ((parameterMeasure ell u).prod μ)
  herrorL2 : MemLp (fun z : ℝ × X =>
    Real.sqrt (jointDensity w p z) * (T z.2 - ψ z.1)) 2
    ((parameterMeasure ell u).prod μ)
  hjointScoreL2 : MemLp (fun z : ℝ × X =>
    Real.sqrt (jointDensity w p z) * jointScore w dw p dp z) 2
    ((parameterMeasure ell u).prod μ)
  hpriorJointScoreL2 : MemLp (fun z : ℝ × X =>
    Real.sqrt (jointDensity w p z) * priorScore w dw z.1) 2
    ((parameterMeasure ell u).prod μ)
  hlikelihoodScoreL2 : MemLp (fun z : ℝ × X =>
    Real.sqrt (jointDensity w p z) * likelihoodScore p dp z.1 z.2) 2
    ((parameterMeasure ell u).prod μ)
  hpriorSqInt : Integrable (fun θ => w θ * (priorScore w dw θ) ^ 2)
    (parameterMeasure ell u)
  hinfoPos : 0 < priorInformation ell u w dw +
    ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u

private lemma weighted_sq_eq
    {X : Type*} {w : ℝ → ℝ} {p : ℝ → X → ℝ}
    (hw : ∀ θ, 0 ≤ w θ) (hp : ∀ θ x, 0 ≤ p θ x)
    (f : ℝ × X → ℝ) (z : ℝ × X) :
    (Real.sqrt (jointDensity w p z) * f z) ^ 2 =
      f z ^ 2 * jointDensity w p z := by
  have hq : 0 ≤ jointDensity w p z := mul_nonneg (hw z.1) (hp z.1 z.2)
  rw [mul_pow, Real.sq_sqrt hq]
  ring

/-- Given [a sigma-finite dominating measure and nondegenerate parameter
interval](hyp:μ,hellu), [a prior, likelihood, scalar target, estimator, and their
derivative representatives](hyp:w,dw,p,dp,ψ,dψ,T), and [smooth-model regularity with
finite weighted L² error and information](hyp:M), [the squared prior-average target
derivative divided by prior plus average likelihood information is at most the
prior-average mean-squared error](goal).

This is a scalar, unweighted specialization of Gill–Levit (1995), Theorem 1, obtained by taking
one-dimensional parameters and targets with scalar unit weight. Unlike `van_trees_inequality`,
callers provide weighted L² model conditions; all proof-internal square, product, cross, and
strong-measurability hypotheses are derived here. -/
theorem van_trees_inequality_of_smooth_model
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ell u : ℝ} (hellu : ell < u)
    (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ) (ψ dψ : ℝ → ℝ) (T : X → ℝ)
    (M : VanTreesSmoothModelRegularity X μ ell u w dw p dp ψ dψ T) :
    (∫ θ, dψ θ * w θ ∂parameterMeasure ell u) ^ 2 /
        (priorInformation ell u w dw +
          ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u) ≤
      ∫ θ, (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
        ∂parameterMeasure ell u := by
  let ν := (parameterMeasure ell u).prod μ
  let e : ℝ × X → ℝ := fun z =>
    Real.sqrt (jointDensity w p z) * (T z.2 - ψ z.1)
  let s : ℝ × X → ℝ := fun z =>
    Real.sqrt (jointDensity w p z) * jointScore w dw p dp z
  let sp : ℝ × X → ℝ := fun z =>
    Real.sqrt (jointDensity w p z) * priorScore w dw z.1
  let sl : ℝ × X → ℝ := fun z =>
    Real.sqrt (jointDensity w p z) * likelihoodScore p dp z.1 z.2
  have he_sq : Integrable (fun z => e z ^ 2) ν :=
    (memLp_two_iff_integrable_sq M.herrorL2.aestronglyMeasurable).1 M.herrorL2
  have hs_sq : Integrable (fun z => s z ^ 2) ν :=
    (memLp_two_iff_integrable_sq M.hjointScoreL2.aestronglyMeasurable).1 M.hjointScoreL2
  have hsp_sq : Integrable (fun z => sp z ^ 2) ν :=
    (memLp_two_iff_integrable_sq M.hpriorJointScoreL2.aestronglyMeasurable).1
      M.hpriorJointScoreL2
  have hsl_sq : Integrable (fun z => sl z ^ 2) ν :=
    (memLp_two_iff_integrable_sq M.hlikelihoodScoreL2.aestronglyMeasurable).1
      M.hlikelihoodScoreL2
  have herrorSqInt : Integrable
      (errorSqField w p (fun θ _ => ψ θ) T) ν := by
    refine he_sq.congr (ae_of_all _ fun z => ?_)
    exact weighted_sq_eq M.hwnonneg M.hpnonneg (fun z => T z.2 - ψ z.1) z
  have hscoreSqInt : Integrable (scoreSqField w dw p dp) ν := by
    refine hs_sq.congr (ae_of_all _ fun z => ?_)
    exact weighted_sq_eq M.hwnonneg M.hpnonneg (jointScore w dw p dp) z
  have hpriorJointSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2) ν := by
    refine hsp_sq.congr (ae_of_all _ fun z => ?_)
    dsimp [sp]
    rw [weighted_sq_eq M.hwnonneg M.hpnonneg (fun z => priorScore w dw z.1) z]
    simp only [jointDensity]
    ring
  have hfisherSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (likelihoodScore p dp z.1 z.2) ^ 2) ν := by
    refine hsl_sq.congr (ae_of_all _ fun z => ?_)
    dsimp [sl]
    rw [weighted_sq_eq M.hwnonneg M.hpnonneg
      (fun z => likelihoodScore p dp z.1 z.2) z]
    simp only [jointDensity]
    ring
  have herrorScoreInt : Integrable
      (errorScoreField w dw p dp (fun θ _ => ψ θ) T) ν := by
    have hmul : Integrable (e * s) ν := M.herrorL2.integrable_mul M.hjointScoreL2
    refine hmul.congr (ae_of_all _ fun z => ?_)
    change e z * s z = errorScoreField w dw p dp (fun θ _ => ψ θ) T z
    rw [show e z * s z =
      (T z.2 - ψ z.1) * jointScore w dw p dp z * jointDensity w p z by
        dsimp [e, s]
        have hq : 0 ≤ jointDensity w p z :=
          mul_nonneg (M.hwnonneg z.1) (M.hpnonneg z.1 z.2)
        rw [show Real.sqrt (jointDensity w p z) * (T z.2 - ψ z.1) *
            (Real.sqrt (jointDensity w p z) * jointScore w dw p dp z) =
          (Real.sqrt (jointDensity w p z)) ^ 2 *
            ((T z.2 - ψ z.1) * jointScore w dw p dp z) by ring,
          Real.sq_sqrt hq]
        ring]
    rfl
  have hsensitivityInt : Integrable
      (sensitivityField w p (fun θ _ => dψ θ)) ν := by
    have hmul : Integrable
        ((fun z : ℝ × X => Real.sqrt (jointDensity w p z) * dψ z.1) *
          fun z : ℝ × X => Real.sqrt (jointDensity w p z)) ν :=
      M.htargetDerivativeL2.integrable_mul M.hjointSqrtL2
    refine hmul.congr (ae_of_all _ fun z => ?_)
    change (Real.sqrt (jointDensity w p z) * dψ z.1) *
        Real.sqrt (jointDensity w p z) =
      sensitivityField w p (fun θ _ => dψ θ) z
    have hq : 0 ≤ jointDensity w p z :=
      mul_nonneg (M.hwnonneg z.1) (M.hpnonneg z.1 z.2)
    rw [show Real.sqrt (jointDensity w p z) * dψ z.1 *
        Real.sqrt (jointDensity w p z) =
      dψ z.1 * (Real.sqrt (jointDensity w p z)) ^ 2 by ring,
      Real.sq_sqrt hq]
    rfl
  have hbalanceInt : Integrable
      (derivativeBalanceField w dw p dp (fun θ _ => ψ θ)
        (fun θ _ => dψ θ) T) ν := by
    have hdiff := herrorScoreInt.sub hsensitivityInt
    refine hdiff.congr ?_
    filter_upwards [M.hdp] with z hdpz
    have hwzero : w z.1 = 0 → dw z.1 = 0 :=
      derivative_eq_zero_of_nonnegative_of_eq_zero M.hwnonneg (M.hwderiv z.1)
    have hpzero : p z.1 z.2 = 0 → dp z.1 z.2 = 0 :=
      derivative_eq_zero_of_nonnegative_of_eq_zero
        (fun t => M.hpnonneg t z.2) hdpz
    change errorScoreField w dw p dp (fun θ _ => ψ θ) T z -
        sensitivityField w p (fun θ _ => dψ θ) z = _
    rw [errorScoreField_eq_numerator (M.hwnonneg z.1) (M.hpnonneg z.1 z.2)
      hwzero hpzero]
    simp only [derivativeBalanceField, sensitivityField, jointDensity]
    ring
  have hcrossInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)) ν := by
    have hmul : Integrable (sp * sl) ν :=
      M.hpriorJointScoreL2.integrable_mul M.hlikelihoodScoreL2
    refine hmul.congr (ae_of_all _ fun z => ?_)
    change sp z * sl z = _
    dsimp [sp, sl]
    have hq : 0 ≤ jointDensity w p z :=
      mul_nonneg (M.hwnonneg z.1) (M.hpnonneg z.1 z.2)
    rw [show Real.sqrt (jointDensity w p z) * priorScore w dw z.1 *
        (Real.sqrt (jointDensity w p z) * likelihoodScore p dp z.1 z.2) =
      (Real.sqrt (jointDensity w p z)) ^ 2 *
        (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2) by ring,
      Real.sq_sqrt hq]
    simp only [jointDensity]
  exact van_trees_inequality μ hellu w dw p dp ψ dψ T
    M.hwC1 M.hwsupport M.hwderiv M.hwnonneg M.hwnorm M.hpnonneg M.hpnorm
    M.hpint M.hdpint M.hdiffUnder M.hpAC M.hψAC M.hdp M.hψderiv M.hboundary
    hbalanceInt.aestronglyMeasurable hbalanceInt
    herrorScoreInt.aestronglyMeasurable herrorScoreInt
    hsensitivityInt.aestronglyMeasurable hsensitivityInt
    herrorSqInt.aestronglyMeasurable herrorSqInt
    hscoreSqInt.aestronglyMeasurable hscoreSqInt
    M.hpriorSqInt.aestronglyMeasurable M.hpriorSqInt
    hpriorJointSqInt.aestronglyMeasurable hpriorJointSqInt
    hfisherSqInt.aestronglyMeasurable hfisherSqInt
    hcrossInt.aestronglyMeasurable hcrossInt M.hinfoPos

end Causalean.Stat.Minimax

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.OLSAsymptotics.Consistency
public import Causalean.Stat.MEstimation.SmoothZEstimator
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Elementary score moment conditions for OLS

This module proves measurability of the OLS score and its derivative, and
records global boundedness as a simple sufficient condition for their
integrability.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {X K : Type*} [MeasurableSpace X] [Fintype K] [DecidableEq K]
  {P : Measure X}

/-- For [measurable regressors](hyp:hx), [a measurable outcome](hyp:hy), and
[a fixed coefficient](hyp:b), the [OLS score is measurable](goal). -/
@[fun_prop]
theorem measurable_olsScore {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (b : EuclideanSpace ℝ K) :
    Measurable (olsScore x y b) := by
  unfold olsScore olsResidual
  change Measurable ((fun z => y z - ∑ i, x z i * b i) • x)
  exact (hy.sub (Finset.measurable_sum _ fun i _ =>
    ((PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : K => ℝ) i).measurable.comp hx).mul
      measurable_const)).smul hx

/-- Under [a finite population law](hyp:P), [measurable regressors](hyp:hx),
[a measurable outcome](hyp:hy), [uniform regressor and outcome
bounds](hyp:hx_bdd,hy_bdd), and [a fixed coefficient](hyp:b), [the squared
norm of the OLS score is integrable](goal). -/
@[fun_prop]
theorem integrable_sq_olsScore_of_bounded [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hx_bdd : ∃ C, ∀ z, ‖x z‖ ≤ C)
    (hy_bdd : ∃ C, ∀ z, |y z| ≤ C)
    (b : EuclideanSpace ℝ K) :
    Integrable (fun z => ‖olsScore x y b z‖ ^ 2) P := by
  rcases hx_bdd with ⟨Cx, hxC⟩
  rcases hy_bdd with ⟨Cy, hyC⟩
  let B := (|Cy| + |Cx| * ‖b‖) * |Cx|
  have hB : 0 ≤ B := mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg
    (abs_nonneg _) (norm_nonneg _))) (abs_nonneg _)
  have hscore : ∀ z, ‖olsScore x y b z‖ ≤ B := by
    intro z
    have hxabs : ‖x z‖ ≤ |Cx| := (hxC z).trans (le_abs_self Cx)
    have hyabs : |y z| ≤ |Cy| := (hyC z).trans (le_abs_self Cy)
    have hdot : |⟪x z, b⟫| ≤ |Cx| * ‖b‖ :=
      (abs_real_inner_le_norm (x z) b).trans
        (mul_le_mul_of_nonneg_right hxabs (norm_nonneg _))
    calc
      ‖olsScore x y b z‖
          = |y z - ⟪x z, b⟫| * ‖x z‖ := by
              simp [olsScore, olsResidual,
                EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm,
                norm_smul, Real.norm_eq_abs]
      _ ≤ (|Cy| + |Cx| * ‖b‖) * |Cx| := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hyabs hdot)
      _ = B := rfl
  apply Integrable.of_bound
    ((measurable_olsScore hx hy b).norm.pow_const 2).aestronglyMeasurable
    (B ^ 2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (olsScore x y b z), hscore z]

/-- For [measurable regressors](hyp:hx), the [observationwise OLS score
derivative is measurable](goal). -/
@[fun_prop]
theorem measurable_olsScoreDerivative {x : X → EuclideanSpace ℝ K}
    (hx : Measurable x) : Measurable (olsScoreDerivative x) := by
  unfold olsScoreDerivative olsRegressorFunctional
  have hcont : Continuous (fun v : EuclideanSpace ℝ K =>
      (-(innerSL ℝ) v).smulRight v) :=
    (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ K)
      (EuclideanSpace ℝ K)).continuous₂.comp
        ((innerSL ℝ).continuous.neg.prodMk continuous_id)
  exact hcont.measurable.comp hx

/-- Under [a finite population law](hyp:P), [measurable and uniformly bounded
regressors](hyp:hx,hx_bdd), the [observationwise OLS score derivative is
integrable](goal). -/
@[fun_prop]
theorem integrable_olsScoreDerivative [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} (hx : Measurable x)
    (hx_bdd : ∃ C, ∀ z, ‖x z‖ ≤ C) :
    Integrable (olsScoreDerivative x) P := by
  rcases hx_bdd with ⟨Cx, hxC⟩
  refine Integrable.of_bound (measurable_olsScoreDerivative hx).aestronglyMeasurable
    (|Cx| ^ 2) ?_
  filter_upwards with z
  have hxabs : ‖x z‖ ≤ |Cx| := (hxC z).trans (le_abs_self Cx)
  simp only [olsScoreDerivative, olsRegressorFunctional, norm_neg,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  nlinarith [norm_nonneg (x z)]

end

end Causalean.Stat

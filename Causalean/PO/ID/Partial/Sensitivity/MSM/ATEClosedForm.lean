/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — calibrated ATE cutoff forms under calibrating-cutoff integrability

Combines four quantile-balancing cutoff forms under integrability of the calibrating cutoffs: treated
upper/lower (`CutoffConstruct`/`LowerBound`) and control upper/lower
(`ControlCutoffConstruct`/`ControlLowerBound`). The ATE endpoints oppose the arm bounds:

    ateUpperCalib Λ
      = msmUpperCalib Λ − msmLowerCalib false Λ
      = candMean (cutoffProp Λ cTU) − candMean false (lowerCutoffProp0 Λ cCL),
    ateLowerCalib Λ
      = msmLowerCalib Λ − msmUpperCalib false Λ
      = candMean (lowerCutoffProp Λ cTL) − candMean false (cutoffProp0 Λ cCU),

Each is a difference of candidate means at `σ(X)`-measurable cutoffs. The two capstones expose
their calibrating-cutoff-integrability premise in their names; the interval result also exposes that
it assumes the two arm-wise validity statements.
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ATE
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlLowerBound
public import Causalean.PO.ID.Partial.Sensitivity.MSM.LowerBound

/-! # Marginal-sensitivity-model ATE cutoff forms under calibrating-cutoff integrability

This file combines the four arm-level quantile-cutoff closed forms into
closed-form endpoints for the calibrated ATE interval. Under assumed arm-wise validity, the true
ATE is then placed between the appropriate differences of the treated and control cutoff candidate
means.

The theorem `ate_endpoints_eq_cutoff_of_calibrating_cutoff_integrability` gives the endpoint
representation using treated upper/lower cutoffs and control upper/lower cutoffs. The theorem
`ate_mem_Icc_cutoff_of_calibrating_cutoff_integrability_and_arm_bounds` combines those endpoint
equalities with assumed arm-wise interval validity.
-/

public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- For [a binary-treatment backdoor system](hyp:S) and [a sensitivity parameter Λ strictly greater
than one](hyp:Λ,hΛ), assume for the treated arm that [the propensity score lies strictly between 0
and 1 almost surely](hyp:hoverlapT) and [the conditional distribution function of the outcome given
each covariate value is continuous](hyp:hatomlessT). Write D for the treated-arm indicator, Y for
the observed outcome, and w_min ≤ w_max for the smallest and largest admissible treated
inverse-propensity weights at level Λ. Suppose [every σ(X)-measurable cutoff c (measurable with
respect to the covariates) for which the conditional mean of D·1{Y > c} given the covariates equals
the upper target survival probability almost surely makes c and |c|·D·w_max integrable](hyp:hregTU),
that [the same two functions are integrable for every σ(X)-measurable cutoff matching the lower
target survival probability](hyp:hregTL), and that [D·w_max](hyp:hmaxT) and [D·|Y|·w_max](hyp:henvT)
are integrable. Assume the same for the control arm, with the control-arm indicator, the control
propensity score and the control weights: [overlap](hyp:hoverlapC), [a continuous conditional
outcome distribution function](hyp:hatomlessC), [the two integrability conditions at every
σ(X)-measurable cutoff matching the control upper target survival probability](hyp:hregCU) and [at
every one matching the control lower target survival probability](hyp:hregCL), and integrability of
[the control indicator times the largest control weight](hyp:hmaxC) and [the control indicator times
|Y| times the largest control weight](hyp:henvC). Then [there are σ(X)-measurable cutoffs cTU, cTL,
cCU, cCL such that the calibrated upper endpoint for the average treatment effect equals the treated
upper-cutoff candidate mean at cTU minus the control lower-cutoff candidate mean at cCL, and the
calibrated lower endpoint equals the treated lower-cutoff candidate mean at cTL minus the control
upper-cutoff candidate mean at cCU](goal). -/
theorem ate_endpoints_eq_cutoff_of_calibrating_cutoff_integrability
    (Λ : ℝ) (hΛ : 1 < Λ)
    -- treated arm regularity
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.treatedSurv c =ᵐ[P.μ] S.survTargetLower Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hmaxT : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (henvT : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    -- control arm regularity
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.controlSurv c =ᵐ[P.μ] S.survTarget0 Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.controlSurv c =ᵐ[P.μ] S.survTargetLower0 Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hmaxC : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (henvC : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ateUpperCalib Λ =
        S.candMean true (S.cutoffProp Λ cTU) - S.candMean false (S.lowerCutoffProp0 Λ cCL) ∧
      S.ateLowerCalib Λ =
        S.candMean true (S.lowerCutoffProp Λ cTL) - S.candMean false (S.cutoffProp0 Λ cCU) := by
  obtain ⟨cTU, hcTU, _, hTU⟩ :=
    S.msmUpperCalib_eq_cutoff_of_calibrating_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hregTU henvT hmaxT
  obtain ⟨cTL, hcTL, _, hTL⟩ :=
    S.msmLowerCalib_eq_cutoff_of_calibrating_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hregTL hmaxT henvT
  obtain ⟨cCU, hcCU, _, hCU⟩ :=
    S.msmUpperCalib0_eq_cutoff_of_calibrating_cutoff_integrability
      Λ hΛ hoverlapC hatomlessC hregCU henvC hmaxC
  obtain ⟨cCL, hcCL, _, hCL⟩ :=
    S.msmLowerCalib0_eq_cutoff_of_calibrating_cutoff_integrability
      Λ hΛ hoverlapC hatomlessC hregCL hmaxC henvC
  refine ⟨cTU, cTL, cCU, cCL, ⟨hcTU, hcTL, hcCU, hcCL⟩, ?_, ?_⟩
  · unfold POBackdoorSystem.ateUpperCalib
    rw [hTU, hCL]
  · unfold POBackdoorSystem.ateLowerCalib
    rw [hTL, hCU]

/-- For [a binary-treatment backdoor system](hyp:S) and [a sensitivity parameter Λ strictly greater
than one](hyp:Λ,hΛ), assume for the treated arm that [the propensity score lies strictly between 0
and 1 almost surely](hyp:hoverlapT) and [the conditional distribution function of the outcome given
each covariate value is continuous](hyp:hatomlessT). Write D for the treated-arm indicator, Y for
the observed outcome, and w_min ≤ w_max for the smallest and largest admissible treated
inverse-propensity weights at level Λ. Suppose [every σ(X)-measurable cutoff c (measurable with
respect to the covariates) for which the conditional mean of D·1{Y > c} given the covariates equals
the upper target survival probability almost surely makes c and |c|·D·w_max integrable](hyp:hregTU),
that [the same two functions are integrable for every σ(X)-measurable cutoff matching the lower
target survival probability](hyp:hregTL), and that [D·w_max](hyp:hmaxT) and [D·|Y|·w_max](hyp:henvT)
are integrable. Assume the same for the control arm, with the control-arm indicator, the control
propensity score and the control weights: [overlap](hyp:hoverlapC), [a continuous conditional
outcome distribution function](hyp:hatomlessC), [the two integrability conditions at every
σ(X)-measurable cutoff matching the control upper target survival probability](hyp:hregCU) and [at
every one matching the control lower target survival probability](hyp:hregCL), and integrability of
[the control indicator times the largest control weight](hyp:hmaxC) and [the control indicator times
|Y| times the largest control weight](hyp:henvC). If in addition [the mean of the treated potential
outcome lies in the treated arm's calibrated interval](hyp:hT) and [the mean of the control
potential outcome lies in the control arm's calibrated interval](hyp:hC), then [there are
σ(X)-measurable cutoffs cTU, cTL, cCU, cCL such that the average treatment effect lies between the
treated lower-cutoff candidate mean at cTL minus the control upper-cutoff candidate mean at cCU and
the treated upper-cutoff candidate mean at cTU minus the control lower-cutoff candidate mean at
cCL](goal). -/
theorem ate_mem_Icc_cutoff_of_calibrating_cutoff_integrability_and_arm_bounds
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.treatedSurv c =ᵐ[P.μ] S.survTargetLower Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hmaxT : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (henvT : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.controlSurv c =ᵐ[P.μ] S.survTarget0 Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      S.controlSurv c =ᵐ[P.μ] S.survTargetLower0 Λ →
      Integrable c P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hmaxC : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (henvC : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hT : S.Ymean true ∈ Set.Icc (S.msmLowerCalib true Λ) (S.msmUpperCalib true Λ))
    (hC : S.Ymean false ∈ Set.Icc (S.msmLowerCalib false Λ) (S.msmUpperCalib false Λ)) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ate ∈ Set.Icc
        (S.candMean true (S.lowerCutoffProp Λ cTL) - S.candMean false (S.cutoffProp0 Λ cCU))
        (S.candMean true (S.cutoffProp Λ cTU) - S.candMean false (S.lowerCutoffProp0 Λ cCL)) := by
  obtain ⟨cTU, cTL, cCU, cCL, hmeas, hUp, hLo⟩ :=
    S.ate_endpoints_eq_cutoff_of_calibrating_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hregTU hregTL hmaxT henvT
      hoverlapC hatomlessC hregCU hregCL hmaxC henvC
  have hval := S.ate_mem_Icc_calib_of_arm_bounds Λ hT hC
  rw [hUp, hLo] at hval
  exact ⟨cTU, cTL, cCU, cCL, hmeas, hval⟩

end POBackdoorSystem

end PO
end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — calibrated ATE cutoff forms under universal integrability

Combines four quantile-balancing cutoff forms under universal cutoff integrability: treated
upper/lower (`CutoffConstruct`/`LowerBound`) and control upper/lower
(`ControlCutoffConstruct`/`ControlLowerBound`). The ATE endpoints oppose the arm bounds:

    ateUpperCalib Λ
      = msmUpperCalib Λ − msmLowerCalib0 Λ
      = candMean (cutoffProp Λ cTU) − candMean0 (lowerCutoffProp0 Λ cCL),
    ateLowerCalib Λ
      = msmLowerCalib Λ − msmUpperCalib0 Λ
      = candMean (lowerCutoffProp Λ cTL) − candMean0 (cutoffProp0 Λ cCU),

Each is a difference of candidate means at conditional-quantile cutoffs. The two capstones expose
their universal cutoff-integrability premise in their names; the interval result also exposes that
it assumes the two arm-wise validity statements.
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ATE
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlLowerBound
public import Causalean.PO.ID.Partial.Sensitivity.MSM.LowerBound

/-! # Marginal-sensitivity-model ATE cutoff forms under universal integrability

This file combines the four arm-level quantile-cutoff closed forms into
closed-form endpoints for the calibrated ATE interval. Under assumed arm-wise validity, the true
ATE is then placed between the appropriate differences of the treated and control cutoff candidate
means.

The theorem `ate_endpoints_eq_cutoff_of_universal_cutoff_integrability` gives the endpoint
representation using treated upper/lower cutoffs and control upper/lower cutoffs. The theorem
`ate_mem_Icc_cutoff_of_universal_cutoff_integrability_and_arm_bounds` combines those endpoint
equalities with assumed arm-wise interval validity.
-/

public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- For [a binary-treatment backdoor system](hyp:S), fix [a sensitivity parameter Λ greater
than one](hyp:Λ,hΛ). Given, for the treated arm, [two-sided propensity
overlap](hyp:hoverlapT), [an
atomless conditional outcome distribution](hyp:hatomlessT), [that the upper and lower calibration
levels each lie strictly between 0 and 1 almost everywhere](hyp:hlevelTU,hlevelTL), and
[integrability regularity, for every `σ(X)`-measurable cutoff candidate, feeding both the upper
and lower calibration constructions](hyp:hregTU,hregTL) — together with the symmetric conditions
for the control arm ([overlap](hyp:hoverlapC), [atomlessness](hyp:hatomlessC), [calibration-level
regularity](hyp:hlevelCU,hlevelCL), and
[cutoff integrability regularity](hyp:hregCU,hregCL)) — then [there exist `σ(X)`-measurable
conditional-quantile cutoffs `cTU, cTL, cCU, cCL` such that the calibrated ATE upper
endpoint equals the treated upper-cutoff candidate mean minus the control lower-cutoff candidate
mean, and the calibrated ATE lower endpoint equals the treated lower-cutoff candidate mean
minus the control upper-cutoff candidate mean](goal). -/
theorem ate_endpoints_eq_cutoff_of_universal_cutoff_integrability
    (Λ : ℝ) (hΛ : 1 < Λ)
    -- treated arm regularity
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevelTU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1)
    (hlevelTL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower Λ ω ∧ S.calibLevelLower Λ ω < 1)
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.lowerCutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    -- control arm regularity
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevelCU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1)
    (hlevelCL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1)
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ateUpperCalib Λ =
        S.candMean true (S.cutoffProp Λ cTU) - S.candMean0 (S.lowerCutoffProp0 Λ cCL) ∧
      S.ateLowerCalib Λ =
        S.candMean true (S.lowerCutoffProp Λ cTL) - S.candMean0 (S.cutoffProp0 Λ cCU) := by
  obtain ⟨cTU, hcTU, _, hTU⟩ :=
    S.msmUpperCalib_eq_cutoff_of_universal_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hlevelTU hregTU
  obtain ⟨cTL, hcTL, _, hTL⟩ :=
    S.msmLowerCalib_eq_cutoff_of_universal_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hlevelTL hregTL
  obtain ⟨cCU, hcCU, _, hCU⟩ :=
    S.msmUpperCalib0_eq_cutoff_of_universal_cutoff_integrability
      Λ hΛ hoverlapC hatomlessC hlevelCU hregCU
  obtain ⟨cCL, hcCL, _, hCL⟩ :=
    S.msmLowerCalib0_eq_cutoff_of_universal_cutoff_integrability
      Λ hΛ hoverlapC hatomlessC hlevelCL hregCL
  refine ⟨cTU, cTL, cCU, cCL, ⟨hcTU, hcTL, hcCU, hcCL⟩, ?_, ?_⟩
  · unfold POBackdoorSystem.ateUpperCalib
    rw [hTU, hCL]
  · unfold POBackdoorSystem.ateLowerCalib
    rw [hTL, hCU]

/-- For [a binary-treatment backdoor system](hyp:S), under the same treated-arm and control-arm
regularity conditions as
`ate_endpoints_eq_cutoff_of_universal_cutoff_integrability` — [a sensitivity parameter Λ greater
than one](hyp:Λ,hΛ); for the treated arm, [propensity overlap](hyp:hoverlapT), [an atomless
conditional outcome distribution](hyp:hatomlessT), [calibration-level
regularity](hyp:hlevelTU,hlevelTL),
[cutoff integrability regularity](hyp:hregTU,hregTL); and symmetrically for the control arm
([overlap](hyp:hoverlapC), [atomlessness](hyp:hatomlessC), [calibration-level
regularity](hyp:hlevelCU,hlevelCL), and
[cutoff integrability regularity](hyp:hregCU,hregCL)) — together with [validity of the treated
arm's calibrated interval for `E[Y(1)]`](hyp:hT) and [validity of the control arm's
calibrated interval for `E[Y(0)]`](hyp:hC), [there exist `σ(X)`-measurable
conditional-quantile cutoffs `cTU, cTL, cCU, cCL` such that the true average treatment effect
`τ = E[Y(1)] − E[Y(0)]` lies between the closed-form lower endpoint (treated lower-cutoff
candidate mean minus control upper-cutoff candidate mean) and the closed-form upper endpoint
(treated upper-cutoff candidate mean minus control lower-cutoff candidate mean)](goal). -/
theorem ate_mem_Icc_cutoff_of_universal_cutoff_integrability_and_arm_bounds
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevelTU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1)
    (hlevelTL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower Λ ω ∧ S.calibLevelLower Λ ω < 1)
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.lowerCutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevelCU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1)
    (hlevelCL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1)
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLowerCalib true Λ) (S.msmUpperCalib true Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ)) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ate ∈ Set.Icc
        (S.candMean true (S.lowerCutoffProp Λ cTL) - S.candMean0 (S.cutoffProp0 Λ cCU))
        (S.candMean true (S.cutoffProp Λ cTU) - S.candMean0 (S.lowerCutoffProp0 Λ cCL)) := by
  obtain ⟨cTU, cTL, cCU, cCL, hmeas, hUp, hLo⟩ :=
    S.ate_endpoints_eq_cutoff_of_universal_cutoff_integrability
      Λ hΛ hoverlapT hatomlessT hlevelTU hlevelTL hregTU hregTL
      hoverlapC hatomlessC hlevelCU hlevelCL hregCU hregCL
  have hval := S.ate_mem_Icc_calib_of_arm_bounds Λ hT hC
  rw [hUp, hLo] at hval
  exact ⟨cTU, cTL, cCU, cCL, hmeas, hval⟩

end POBackdoorSystem

end PO
end Causalean

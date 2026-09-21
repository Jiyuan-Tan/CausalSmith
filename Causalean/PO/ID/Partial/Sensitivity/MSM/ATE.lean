/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the ATE interval

Combines the treated-arm calibrated interval (`Calibrated.lean`) and the control-arm calibrated
interval (`ControlCalibrated.lean`) into a partial-identification interval for the average
treatment effect `τ = E[Y(1)] − E[Y(0)]`. Following Dorn–Guo, the calibrated ATE bounds
are obtained by *opposing* the arm bounds:

    τ⁺(Λ) = ψ_T⁺(Λ) − ψ_C⁻(Λ),   τ⁻(Λ) = ψ_T⁻(Λ) − ψ_C⁺(Λ),

i.e. the ATE upper endpoint pairs the treated upper bound with the control *lower*
bound, and vice versa. The validity of the ATE interval (it contains the true `τ`)
follows from the two arm-wise validity statements by interval subtraction. Applying the same
construction to the uncalibrated HT-relaxation arm bounds gives another ATE interval; the stated
arm-endpoint comparison hypotheses imply that it contains the calibrated interval.
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Calibrated
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlCalibrated

/-! # Marginal-sensitivity-model ATE interval

This file combines treated-arm and control-arm marginal-sensitivity intervals
into an interval for the average treatment effect. The ATE upper endpoint pairs
the treated upper bound with the control lower bound, and the lower endpoint
pairs the treated lower bound with the control upper bound.

The main declarations are `ate`, the calibrated endpoints `ateUpperCalib` and
`ateLowerCalib`, the uncalibrated endpoints `ateUpper` and `ateLower`, validity
theorems `ate_mem_Icc_calib_of_arm_bounds` and `ate_mem_Icc_of_arm_bounds`, and the nesting theorem
`ateCalib_subset`.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ), and
[a back-door system on them](hyp:S), [the average treatment effect](goal) is the population mean
of the potential outcome under treatment minus the population mean of the potential outcome under
control. -/
noncomputable def ate : ℝ := S.Y1mean - S.Y0mean

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), [the calibrated upper bound for
the average treatment effect](goal) is the calibrated treated-arm upper bound minus the calibrated control-
arm lower bound. -/
noncomputable def ateUpperCalib (Λ : ℝ) : ℝ := S.msmUpperCalib true Λ - S.msmLowerCalib0 Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), [the calibrated lower bound for
the average treatment effect](goal) is the calibrated treated-arm lower bound minus the calibrated control-
arm upper bound. -/
noncomputable def ateLowerCalib (Λ : ℝ) : ℝ := S.msmLowerCalib true Λ - S.msmUpperCalib0 Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), [the uncalibrated upper
bound for the average treatment effect](goal) is the uncalibrated treated-arm upper bound minus
the uncalibrated control-arm lower bound. -/
noncomputable def ateUpper (Λ : ℝ) : ℝ := S.msmUpper true Λ - S.msmLower0 Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), [the uncalibrated lower
bound for the average treatment effect](goal) is the uncalibrated treated-arm lower bound minus
the uncalibrated control-arm upper bound. -/
noncomputable def ateLower (Λ : ℝ) : ℝ := S.msmLower true Λ - S.msmUpper0 Λ

/-- **Interval subtraction.** If `a ∈ [aₗ, aᵤ]` and `b ∈ [bₗ, bᵤ]`, then
`a − b ∈ [aₗ − bᵤ, aᵤ − bₗ]`. The arithmetic core of the ATE-interval theorems. -/
theorem sub_mem_Icc_of_mem_Icc {a aₗ aᵤ b bₗ bᵤ : ℝ}
    (ha : a ∈ Set.Icc aₗ aᵤ) (hb : b ∈ Set.Icc bₗ bᵤ) :
    a - b ∈ Set.Icc (aₗ - bᵤ) (aᵤ - bₗ) := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  exact ⟨by linarith, by linarith⟩

/-- The [average treatment effect lies in the calibrated ATE interval](goal) for
[a binary-treatment backdoor system](hyp:S) at [a sensitivity level](hyp:Λ) whenever [the
treated mean potential outcome lies in its calibrated interval](hyp:hT) and [the control mean
potential outcome lies in its calibrated interval](hyp:hC).

This is interval arithmetic; whatever establishes the arm-wise bounds carries the sensitivity
model's mathematical content. -/
theorem ate_mem_Icc_calib_of_arm_bounds (Λ : ℝ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLowerCalib true Λ) (S.msmUpperCalib true Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ)) :
    S.ate ∈ Set.Icc (S.ateLowerCalib Λ) (S.ateUpperCalib Λ) := by
  unfold POBackdoorSystem.ate POBackdoorSystem.ateLowerCalib POBackdoorSystem.ateUpperCalib
  exact sub_mem_Icc_of_mem_Icc hT hC

/-- The [average treatment effect lies in the uncalibrated HT-relaxation ATE interval](goal) for
[a binary-treatment backdoor system](hyp:S) at [a sensitivity level](hyp:Λ) whenever [the
treated mean potential outcome lies in its uncalibrated HT-relaxation interval](hyp:hT) and
[the control mean potential outcome lies in its uncalibrated HT-relaxation interval](hyp:hC).

This is interval arithmetic; whatever establishes the two arm-wise bounds carries the sensitivity
model's mathematical content. -/
theorem ate_mem_Icc_of_arm_bounds (Λ : ℝ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLower true Λ) (S.msmUpper true Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLower0 Λ) (S.msmUpper0 Λ)) :
    S.ate ∈ Set.Icc (S.ateLower Λ) (S.ateUpper Λ) := by
  unfold POBackdoorSystem.ate POBackdoorSystem.ateLower POBackdoorSystem.ateUpper
  exact sub_mem_Icc_of_mem_Icc hT hC

/-- The [calibrated ATE interval is contained in the uncalibrated HT-relaxation ATE
interval](goal) for [a binary-treatment backdoor system](hyp:S) at [a sensitivity
level](hyp:Λ) when [the treated calibrated upper endpoint is no larger than its uncalibrated
endpoint](hyp:hUT), [the treated uncalibrated lower endpoint is no larger than its calibrated
endpoint](hyp:hLT), [the control calibrated upper endpoint is no larger than its uncalibrated
endpoint](hyp:hU0), and [the control uncalibrated lower endpoint is no larger than its calibrated
endpoint](hyp:hL0). -/
theorem ateCalib_subset (Λ : ℝ)
    (hUT : S.msmUpperCalib true Λ ≤ S.msmUpper true Λ)
    (hLT : S.msmLower true Λ ≤ S.msmLowerCalib true Λ)
    (hU0 : S.msmUpperCalib0 Λ ≤ S.msmUpper0 Λ)
    (hL0 : S.msmLower0 Λ ≤ S.msmLowerCalib0 Λ) :
    Set.Icc (S.ateLowerCalib Λ) (S.ateUpperCalib Λ)
      ⊆ Set.Icc (S.ateLower Λ) (S.ateUpper Λ) := by
  apply Set.Icc_subset_Icc
  · unfold POBackdoorSystem.ateLower POBackdoorSystem.ateLowerCalib
    linarith
  · unfold POBackdoorSystem.ateUpper POBackdoorSystem.ateUpperCalib
    linarith

/-- **The calibrated ATE interval is valid under the marginal sensitivity model.** For [a
sensitivity budget](hyp:Λ), if [the true treated-arm propensity lies in the calibrated ambiguity
set](hyp:hmemT) and [its candidate mean is the true treated-arm mean](hyp:hbridgeT) with [the
treated candidate means bounded below](hyp:hbddT) and [above](hyp:hbddT'), and likewise [for the
control arm](hyp:hmemC,hbridgeC,hbddC,hbddC'), then [the true average treatment effect lies in the
calibrated ATE interval](goal).

This is the end-to-end statement a practitioner wants: it starts from the sensitivity model itself
rather than from assumed arm-wise bounds. It composes the two arm-level results
`Y1mean_mem_Icc_calib` and `Y0mean_mem_Icc_calib`, which carry the actual mathematical content,
with the interval arithmetic of `ate_mem_Icc_calib_of_arm_bounds`. -/
theorem ate_mem_Icc_calib_of_msm (Λ : ℝ)
    (hmemT : S.completeProp true ∈ S.MSMSetCalib true Λ)
    (hbridgeT : S.candMean true (S.completeProp true) = S.Y1mean)
    (hbddT : BddBelow (S.candMean true '' S.MSMSetCalib true Λ))
    (hbddT' : BddAbove (S.candMean true '' S.MSMSetCalib true Λ))
    (hmemC : S.completeProp0 ∈ S.MSMSetCalib0 Λ)
    (hbridgeC : S.candMean0 S.completeProp0 = S.Y0mean)
    (hbddC : BddBelow (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hbddC' : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ)) :
    S.ate ∈ Set.Icc (S.ateLowerCalib Λ) (S.ateUpperCalib Λ) :=
  S.ate_mem_Icc_calib_of_arm_bounds Λ
    (S.Y1mean_mem_Icc_calib Λ hmemT hbridgeT hbddT hbddT')
    (S.Y0mean_mem_Icc_calib Λ hmemC hbridgeC hbddC hbddC')

end POBackdoorSystem

end PO
end Causalean

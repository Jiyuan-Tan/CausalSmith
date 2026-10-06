/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Calibrated
public import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlSetup

/-! # Compatibility names for calibrated control-arm sensitivity bounds

The calibrated marginal sensitivity model is treatment-arm parameterized in
`Calibrated.lean`. This file retains the former control-specific API as deprecated
specializations at `d = false`; it contains no separate control-arm derivation.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a candidate complete control propensity](hyp:etilde),
the [control-arm calibration condition](goal) is arm-uniform calibration specialized to control. -/
@[deprecated "Use Calibrated false." (since := "2026-09-17")]
abbrev Calibrated0 (etilde : P.Ω → ℝ) : Prop := S.Calibrated false etilde

/-- Deprecated control-arm specialization of inverse-weight integrability under calibration. -/
@[fun_prop, deprecated "Use calibrated_weight_integrable false." (since := "2026-09-17")]
theorem calibrated_weight_integrable0 (etilde : P.Ω → ℝ)
    (hcal : S.Calibrated0 etilde) :
    Integrable (fun ω => S.dVar.indicator false ω / etilde ω) P.μ :=
  S.calibrated_weight_integrable false etilde hcal

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [calibrated control
ambiguity set](goal) is the arm-uniform calibrated set specialized to control. -/
@[deprecated "Use MSMSetCalib false." (since := "2026-09-17")]
abbrev MSMSetCalib0 (Λ : ℝ) : Set (P.Ω → ℝ) := S.MSMSetCalib false Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [calibrated control
upper bound](goal) is the arm-uniform calibrated upper bound specialized to control. -/
@[deprecated "Use msmUpperCalib false." (since := "2026-09-17")]
noncomputable abbrev msmUpperCalib0 (Λ : ℝ) : ℝ := S.msmUpperCalib false Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [calibrated control
lower bound](goal) is the arm-uniform calibrated lower bound specialized to control. -/
@[deprecated "Use msmLowerCalib false." (since := "2026-09-17")]
noncomputable abbrev msmLowerCalib0 (Λ : ℝ) : ℝ := S.msmLowerCalib false Λ

/-- Deprecated control-arm specialization of complete-propensity calibration. -/
@[deprecated "Use completeProp_calibrated false." (since := "2026-09-17")]
theorem completeProp0_calibrated
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hpos : ∀ᵐ ω ∂P.μ, 0 < S.completeProp0 ω)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.completeProp0 ω) P.μ) :
    S.Calibrated0 S.completeProp0 :=
  S.completeProp_calibrated false hpos hint

/-- Deprecated control-arm specialization of truth membership in the calibrated set. -/
@[deprecated "Use completeProp_mem_MSMSetCalib false." (since := "2026-09-17")]
theorem completeProp0_mem_MSMSetCalib0 (Λ : ℝ)
    (hmem : S.completeProp0 ∈ S.MSMSet0 Λ)
    (hcalib : S.Calibrated0 S.completeProp0) :
    S.completeProp0 ∈ S.MSMSetCalib0 Λ :=
  S.completeProp_mem_MSMSetCalib false Λ hmem hcalib

/-- Given [a sensitivity level](hyp:Λ), [the true complete propensity in the calibrated control
MSM set](hyp:hmem), [its control-mean bridge identity](hyp:hbridge), and [lower and upper
boundedness of the calibrated candidate means](hyp:hbdd,hbdd'), [the control potential-outcome
mean lies in the calibrated control MSM interval](goal).

Deprecated control-arm specialization of calibrated MSM interval validity. -/
@[deprecated "Use Ymean_mem_Icc_calib false." (since := "2026-09-17")]
theorem Y0mean_mem_Icc_calib (Λ : ℝ)
    (hmem : S.completeProp0 ∈ S.MSMSetCalib0 Λ)
    (hbridge : S.candMean0 S.completeProp0 = S.Y0mean)
    (hbdd : BddBelow (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hbdd' : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ)) :
    S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ) :=
  S.Ymean_mem_Icc_calib false Λ hmem hbridge hbdd hbdd'

/-- Deprecated control-arm specialization of calibrated-set inclusion. -/
@[deprecated "Use MSMSetCalib_subset false." (since := "2026-09-17")]
theorem MSMSetCalib0_subset (Λ : ℝ) : S.MSMSetCalib0 Λ ⊆ S.MSMSet0 Λ :=
  S.MSMSetCalib_subset false Λ

/-- Deprecated control-arm specialization of calibrated upper-bound tightening. -/
@[deprecated "Use msmUpperCalib_le_msmUpper false." (since := "2026-09-17")]
theorem msmUpperCalib0_le_msmUpper0 (Λ : ℝ)
    (hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty)
    (hbdd : BddAbove (S.candMean0 '' S.MSMSet0 Λ)) :
    S.msmUpperCalib0 Λ ≤ S.msmUpper0 Λ :=
  S.msmUpperCalib_le_msmUpper false Λ hne hbdd

/-- Deprecated control-arm specialization of calibrated lower-bound tightening. -/
@[deprecated "Use msmLower_le_msmLowerCalib false." (since := "2026-09-17")]
theorem msmLower0_le_msmLowerCalib0 (Λ : ℝ)
    (hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty)
    (hbdd : BddBelow (S.candMean0 '' S.MSMSet0 Λ)) :
    S.msmLower0 Λ ≤ S.msmLowerCalib0 Λ :=
  S.msmLower_le_msmLowerCalib false Λ hne hbdd

end POBackdoorSystem

end PO
end Causalean

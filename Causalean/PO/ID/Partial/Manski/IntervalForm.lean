/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.ID.Partial.Basic
public import Causalean.PO.ID.Partial.Manski.Combined
public import Causalean.PO.ID.Partial.Manski.NonAsp

/-! # Manski Interval Forms

This file restates Manski scalar lower-and-upper bounds as closed interval
membership statements for the average treatment effect. It covers the
baseline mean-independent-instrument bound, monotone treatment response with
monotone treatment selection, and, for finite instrument value spaces,
monotone treatment response with monotone instrumental variable bounds.

These results add no new identification content; they translate existing
sandwich inequalities into the interval vocabulary used by the partial
identification engine. -/

public section

set_option linter.unusedFintypeInType false

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-- **`Set.Icc` form of `manski_bounds_ATE`.** Under [the baseline Manski assumptions](hyp:hA)
and [mean independence of both potential outcomes from the instrument](hyp:hMI), for
[any two instrument values `z₁, z₀` in the support of the instrument](hyp:hz₁,hz₀),
[the average treatment effect lies in the closed interval from the `z₁`-lower/`z₀`-upper
worst-case bound to the `z₁`-upper/`z₀`-lower worst-case bound](goal) — the
per-stratum-pair mean-independent-instrument sandwich restated as interval
membership. -/
theorem manski_ATE_mem_Icc [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep)
    {z₁ z₀ : α} (hz₁ : z₁ ∈ S.support) (hz₀ : z₀ ∈ S.support) :
    S.ATE ∈ Set.Icc (S.lowerBound1 hA.lo z₁ - S.upperBound0 hA.hi z₀)
      (S.upperBound1 hA.hi z₁ - S.lowerBound0 hA.lo z₀) := by
  have h := S.manski_bounds_ATE hA hMI hz₁ hz₀
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of `manski_bounds_ATE_ciSup`.** Under [the baseline Manski
assumptions](hyp:hA), [mean independence of both potential outcomes from the
instrument](hyp:hMI), and [a nonempty instrument support](hyp:hne), [the average treatment
effect lies in the closed interval from the supremum-of-lowers-minus-infimum-of-uppers bound to
the infimum-of-uppers-minus-supremum-of-lowers bound, aggregated over every instrument
stratum](goal) — the sup/inf-aggregated mean-independent-instrument sandwich
restated as interval membership. -/
theorem manski_ATE_mem_Icc_ciSup [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    S.ATE ∈ Set.Icc
      ((⨆ z : ↑S.support, S.lowerBound1 hA.lo z.val)
        - (⨅ z : ↑S.support, S.upperBound0 hA.hi z.val))
      ((⨅ z : ↑S.support, S.upperBound1 hA.hi z.val)
        - (⨆ z : ↑S.support, S.lowerBound0 hA.lo z.val)) := by
  have h := S.manski_bounds_ATE_ciSup hA hMI hne
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of `mtr_mts_bounds_ATE`.** Under [the baseline Manski
assumptions](hyp:hA), [monotone treatment response](hyp:hMTR), and [monotone
treatment selection with `0 < P(D=1) < 1`](hyp:hMTS), [the average treatment
effect lies in the closed interval from `0` to the observed treated-control
mean contrast](goal). -/
theorem mtr_mts_ATE_mem_Icc (hA : S.BaseAssumptions)
    (hMTR : S.MTR) (hMTS : S.MTS) :
    S.ATE ∈ Set.Icc 0
      (normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY
        - normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY) := by
  have h := S.mtr_mts_bounds_ATE hA hMTR hMTS
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **Finite-value-space `Set.Icc` form of `mtr_miv_bounds_ATE`.** For a finite
instrument value space, under [the baseline Manski assumptions](hyp:hA),
[monotone treatment response](hyp:hMTR), and [a monotone instrumental
variable](hyp:hMIV), [the average treatment effect lies in the closed interval
from zero to the integrated monotone-instrument envelope contrast](goal). -/
theorem mtr_miv_ATE_mem_Icc [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMTR : S.MTR) (hMIV : S.MIV) :
    letI := hMIV.inst
    S.ATE ∈ Set.Icc 0
      (∫ ω, S.mUpper1 hA (S.factualZ ω) - S.mLower0 hA (S.factualZ ω) ∂P.μ) := by
  letI := hMIV.inst
  have h := S.mtr_miv_bounds_ATE hA hMTR hMIV
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

end POManskiIVSystem

end PO
end Causalean

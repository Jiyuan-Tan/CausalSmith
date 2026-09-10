/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Manski IV Setup

This file defines the data layer for Manski bounds with a discrete instrument,
a binary treatment, and a real-valued outcome. It provides the potential
outcomes, factual variables, instrument support, target average treatment
effect, and the four observable bound functionals used by the Manski
identification arguments.

Assumption bundles are kept in the companion assumptions file. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- The Manski IV data layer records a discrete instrument, a binary treatment,
and a real outcome inside a potential-outcome system.

This is the discrete-IV system for Manski average-treatment-effect bounds,
corresponding to `def:po-iv-manski-system`.

`α` is the value space of the instrument; discreteness enters via
`MeasurableSingletonClass α`, which makes the events `{Z = z}` measurable. -/
structure POManskiIVSystem (P : POSystem) (α : Type*)
    [MeasurableSpace α] [MeasurableSingletonClass α] where
  Z : P.V
  D : P.V
  Y : P.V
  hZ : P.X Z ≃ᵐ α
  hDbool : P.X D ≃ᵐ Bool
  hYreal : P.X Y ≃ᵐ ℝ
  hZD : Z ≠ D
  hZY : Z ≠ Y
  hDY : D ≠ Y

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the instrument
variable](goal) is its instrument represented as a potential-outcome variable. -/
def zVar : POVar P α := ⟨S.Z, S.hZ⟩

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the binary treatment
variable](goal) is its treatment represented as a potential-outcome variable. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the real-valued outcome
variable](goal) is its outcome represented as a potential-outcome variable. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), and [a binary treatment
arm](hyp:d), [the potential outcome under that arm](goal) assigns each unit its
real-valued outcome were treatment set to that arm.

This is the function `Y(d) : P.Ω → ℝ`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the observed
instrument](goal) assigns each unit its realized instrument value. -/
noncomputable def factualZ : P.Ω → α := S.zVar.factual

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the observed binary
treatment](goal) assigns each unit its realized treatment arm. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the observed
outcome](goal) assigns each unit its realized real-valued outcome. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), and [an instrument
value](hyp:z), [the corresponding instrument stratum](goal) is the set of
units whose observed instrument equals that value. -/
def zEvent (z : α) : Set P.Ω := S.zVar.event z

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), and [a binary treatment
arm](hyp:d), [the corresponding treatment stratum](goal) is the set of units
whose observed treatment equals that arm. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-! ### Measurability -/

/-- For [a fixed treatment arm `d`](hyp:d), [the counterfactual outcome `Y(d)` is
measurable](goal). -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- Factual instrument is measurable. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- Factual treatment is measurable. -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- Factual outcome is measurable. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- Each instrument stratum event is measurable. -/
lemma measurableSet_zEvent (z : α) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _ (measurableSet_singleton _)

/-- Each treatment arm event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _ (measurableSet_singleton _)

/-! ### Target parameter, support, and bound functionals -/

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the average treatment
effect](goal) is the population expectation of the potential outcome under
treatment minus the potential outcome under control. -/
noncomputable def ATE : ℝ := ∫ ω, S.YofD true ω - S.YofD false ω ∂P.μ

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), and [a Manski instrumental-variables
system based on them](hyp:S), [the instrument
support](goal) is the set of instrument values whose observed-instrument
stratum has nonzero probability. -/
def support : Set α := {z | P.μ (S.zEvent z) ≠ 0}

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), [a binary treatment
arm](hyp:d), [a real-valued outcome bound](hyp:c), and [an instrument value](hyp:z),
[the arm-bound functional](goal) is the conditional mean within that instrument
stratum of the observed outcome for units on the specified arm and the supplied
bound for units on the opposite arm.

The unified arm-bound functional averages the observed outcome on arm `d` and
the supplied outcome floor or ceiling on the opposite arm within instrument stratum `z`.

The outcome-bound parameter `c` is applied on the counterfactual arm `!d`.
Specialising `d` to `true`/`false` and `c` to `lo`/`hi` recovers the four
named functionals `lowerBound1`, `upperBound1`, `lowerBound0`, `upperBound0`. -/
noncomputable def boundArm (d : Bool) (c : ℝ) (z : α) : ℝ :=
  eventCondExp P.μ (S.zEvent z)
    (fun ω => S.factualY ω * S.dVar.indicator d ω
               + c * S.dVar.indicator (!d) ω)

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), [a real outcome
floor](hyp:lo), and [an instrument value](hyp:z), [the lower bound for the
treated potential-outcome mean](goal) is the arm-bound functional that uses
the floor for untreated units in that instrument stratum.

The lower observable bound for the treated potential-outcome mean in instrument
stratum `z` uses the outcome floor on untreated units. -/
noncomputable def lowerBound1 (lo : ℝ) (z : α) : ℝ := S.boundArm true lo z

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), [a real outcome
ceiling](hyp:hi), and [an instrument value](hyp:z), [the upper bound for the
treated potential-outcome mean](goal) is the arm-bound functional that uses
the ceiling for untreated units in that instrument stratum.

The upper observable bound for the treated potential-outcome mean in instrument
stratum `z` uses the outcome ceiling on untreated units. -/
noncomputable def upperBound1 (hi : ℝ) (z : α) : ℝ := S.boundArm true hi z

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), [a real outcome
floor](hyp:lo), and [an instrument value](hyp:z), [the lower bound for the
control potential-outcome mean](goal) is the arm-bound functional that uses
the floor for treated units in that instrument stratum.

The lower observable bound for the control potential-outcome mean in instrument
stratum `z` uses the outcome floor on treated units. -/
noncomputable def lowerBound0 (lo : ℝ) (z : α) : ℝ := S.boundArm false lo z

/-- For [a potential-outcome system](hyp:P), [a measurable instrument-value space
whose singleton values are measurable](hyp:α), [a Manski instrumental-variables
system based on them](hyp:S), [a real outcome
ceiling](hyp:hi), and [an instrument value](hyp:z), [the upper bound for the
control potential-outcome mean](goal) is the arm-bound functional that uses
the ceiling for treated units in that instrument stratum.

The upper observable bound for the control potential-outcome mean in instrument
stratum `z` uses the outcome ceiling on treated units. -/
noncomputable def upperBound0 (hi : ℝ) (z : α) : ℝ := S.boundArm false hi z

end POManskiIVSystem

end PO
end Causalean

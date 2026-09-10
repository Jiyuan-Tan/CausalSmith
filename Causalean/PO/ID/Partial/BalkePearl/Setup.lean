/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: data layer

The `POBalkePearlSystem` structure (def:po-iv-balke-pearl-system) plus all
basic accessors, measurability lemmas, the target parameter `ATE`, and the
cell probability `cellProb`.

All three variables Z, D, Y are binary (Bool).  No assumption bundles live
here — see `Assumptions.lean`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Causalean.PO.Assumptions.IndepCF
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Balke-Pearl Setup

This file defines the data layer for Balke-Pearl partial identification of the
average treatment effect with a binary instrument, binary treatment, and binary
outcome. The structure `POBalkePearlSystem` records the three binary system
variables and their distinctness; its namespace supplies the factual variables
`factualZ`, `factualD`, `factualY`, the counterfactuals `DofZ`, `YofD`, and
`YofZD`, the real-valued Boolean embedding used for integration, the target
estimand `ATE`, and the observable conditional cell probability `cellProb`. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- **Binary-IV system for Balke–Pearl ATE bounds** (`def:po-iv-balke-pearl-system`). Inside a
potential-outcome system, this bundles [a binary instrument node `Z`](hyp:Z,hZbool), [a binary
treatment node `D`](hyp:D,hDbool), and [a binary outcome node `Y`](hyp:Y,hYbool), subject to
[the instrument, treatment, and outcome being pairwise distinct system
variables](hyp:hZD,hZY,hDY). -/
structure POBalkePearlSystem (P : POSystem) where
  Z : P.V
  D : P.V
  Y : P.V
  hZbool : P.X Z ≃ᵐ Bool
  hDbool : P.X D ≃ᵐ Bool
  hYbool : P.X Y ≃ᵐ Bool
  hZD : Z ≠ D
  hZY : Z ≠ Y
  hDY : D ≠ Y

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### POVar wrappers -/

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [instrument variable](goal) is the system's instrument, packaged together with its binary measurement scale. -/
def zVar : POVar P Bool := ⟨S.Z, S.hZbool⟩

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [treatment variable](goal) is the system's treatment, packaged together with its binary measurement scale. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [outcome variable](goal) is the system's outcome, packaged together with its binary measurement scale. -/
def yVar : POVar P Bool := ⟨S.Y, S.hYbool⟩

/-! ### Single-target counterfactuals -/

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [an instrument value](hyp:z), the [potential treatment function](goal) maps each unit to the treatment it would receive were the instrument set to that value. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool := S.dVar.cfUnder S.zVar z

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [a treatment value](hyp:d), the [potential outcome function](goal) maps each unit to the binary outcome it would have under that treatment value. -/
noncomputable def YofD (d : Bool) : P.Ω → Bool := S.yVar.cfUnder S.dVar d

/-! ### Two-target counterfactual Y(z,d) -/

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), [an instrument value](hyp:z), and [a treatment value](hyp:d), the [joint intervention regime](goal) sets the instrument to the specified instrument value and the treatment to the specified treatment value.

Built as a disjoint union of the singleton regimes `{Z ← z}` and `{D ← d}`;
disjointness uses `S.hZD : Z ≠ D`. -/
noncomputable def regimeZD (z d : Bool) : Regime P.V P.X :=
  (Regime.single S.Z (S.hZbool.symm z)).sqcup
    (Regime.single S.D (S.hDbool.symm d))
    (Regime.single_disjoint_single S.hZD _ _)

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), [an instrument value](hyp:z), and [a treatment value](hyp:d), the [joint-intervention potential outcome function](goal) maps each unit to its outcome when the instrument and treatment are set jointly to those values. -/
noncomputable def YofZD (z d : Bool) : P.Ω → Bool := S.yVar.cf (S.regimeZD z d)

/-! ### Factuals -/

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [factual instrument function](goal) maps each unit to its observed binary instrument value. -/
noncomputable def factualZ : P.Ω → Bool := S.zVar.factual

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [factual treatment function](goal) maps each unit to its observed binary treatment value. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [factual outcome function](goal) maps each unit to its observed binary outcome value. -/
noncomputable def factualY : P.Ω → Bool := S.yVar.factual

/-! ### Real cast for integration -/

/-- The [binary-to-real encoding](goal) maps every binary value to a real number: [for true](step:1), its value is one, and [for false](step:2), its value is zero. -/
@[simp] noncomputable def boolToReal : Bool → ℝ
  | true  => 1
  | false => 0

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [a treatment value](hyp:d), the [real-valued potential outcome function](goal) maps each unit's binary potential outcome under that treatment to its zero--one real encoding. -/
noncomputable def YofD_real (d : Bool) : P.Ω → ℝ := boolToReal ∘ S.YofD d

/-! ### Events -/

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [an instrument value](hyp:z), the [instrument event](goal) is the set of units whose factual instrument equals that value. -/
def zEvent (z : Bool) : Set P.Ω := S.zVar.event z

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [a treatment value](hyp:d), the [treatment event](goal) is the set of units whose factual treatment equals that value. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [an outcome value](hyp:y), the [outcome event](goal) is the set of units whose factual outcome equals that value. -/
def yEvent (y : Bool) : Set P.Ω := S.yVar.event y

/-! ### Measurability -/

/-- For [a fixed instrument value `z`](hyp:z), [the potential treatment `D(z)` is
measurable](goal). -/
@[fun_prop]
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- The outcome under a fixed treatment value is measurable. -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The outcome under fixed instrument and treatment values is measurable. -/
@[fun_prop]
lemma measurable_YofZD (z d : Bool) : Measurable (S.YofZD z d) :=
  S.yVar.measurable_cf _

/-- The factual instrument is measurable. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- The factual treatment is measurable. -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- The factual outcome is measurable. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- The factual instrument event is measurable. -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _ (measurableSet_singleton _)

/-- The factual treatment event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _ (measurableSet_singleton _)

/-- The factual outcome event is measurable. -/
lemma measurableSet_yEvent (y : Bool) : MeasurableSet (S.yEvent y) :=
  S.yVar.measurableSet_event _ (measurableSet_singleton _)

/-- The Boolean-to-real embedding is measurable. -/
@[fun_prop]
lemma measurable_boolToReal : Measurable (boolToReal) := by
  apply measurable_of_finite

/-- The real-valued potential outcome under a fixed treatment is measurable. -/
@[fun_prop]
lemma measurable_YofD_real (d : Bool) : Measurable (S.YofD_real d) :=
  measurable_boolToReal.comp (S.measurable_YofD d)

/-! ### Target parameter and cell probability -/

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [average treatment effect](goal) is the expectation, under the system's probability measure, of the real-valued potential outcome under treatment minus that under control. -/
noncomputable def ATE : ℝ :=
  ∫ ω, S.YofD_real true ω - S.YofD_real false ω ∂P.μ

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), [an outcome value](hyp:y), [a treatment value](hyp:d), and [an instrument value](hyp:z), the [conditional cell probability](goal) is the probability that the factual outcome and treatment equal the specified values conditional on the factual instrument equaling the specified instrument value.

It is defined as the probability of the joint instrument--outcome--treatment event divided by the probability of the instrument event. -/
noncomputable def cellProb (y d z : Bool) : ℝ :=
  (P.μ (S.zEvent z ∩ S.yEvent y ∩ S.dEvent d)).toReal
    / (P.μ (S.zEvent z)).toReal

end POBalkePearlSystem

end PO
end Causalean

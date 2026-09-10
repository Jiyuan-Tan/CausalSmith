/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds: data layer

The `POLeeSystem` structure (def:po-lee-system) plus the basic accessors,
factual / counterfactual variables, factual events
(`aEvent`, `selEvent`, `selectedTreated`, `selectedControl`),
and measurability lemmas.

No assumption bundles and no principal-stratum events live here — see
`Assumptions.lean` and `PrincipalStrata.lean`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Lee Bounds Setup

This file defines the potential-outcome data layer for Lee sample-selection
bounds. It provides the treatment, selection, and outcome variables, their
factual and counterfactual versions, the observed selected cells, and basic
measurability facts. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- The data layer for Lee (2009) bounds: a treatment-selection model in which a
binary treatment `A` affects whether an outcome `Y` is observed at all, through a
binary sample-selection indicator `Sel`.  The outcome `Y` is only meaningful when
`Sel = true` (e.g. a wage observed only for the employed), so the treatment
effect on `Y` among the always-selected subpopulation is only partially
identified — the object the Lee bounds bracket.  Formally this packages, inside
an ambient PO system `P`, the three nodes `A`, `Sel`, `Y`, the measurable
identifications of their value spaces with `Bool`/`Bool`/`ℝ`, and the fact that
the three nodes are distinct (def:po-lee-system).

* `A` is the binary treatment.
* `Sel` is the binary sample-selection indicator
  (denoted `S` in the doc; renamed to `Sel` so that the conventional
  bound variable `S : POLeeSystem P` does not shadow it).
* `Y` is the real-valued outcome (only meaningful on `{Sel = true}`). -/
structure POLeeSystem (P : POSystem) where
  /-- The binary treatment node (an index into the ambient system's variables). -/
  A : P.V
  /-- The binary sample-selection / observability indicator node: `Y` is observed
  iff `Sel = true`. -/
  Sel : P.V
  /-- The real-valued outcome node (only meaningful where `Sel = true`). -/
  Y : P.V
  /-- The treatment's value space is measurably equivalent to `Bool`. -/
  hAbool : P.X A ≃ᵐ Bool
  /-- The selection indicator's value space is measurably equivalent to `Bool`. -/
  hSelbool : P.X Sel ≃ᵐ Bool
  /-- The outcome's value space is measurably equivalent to `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- Treatment and selection are distinct nodes. -/
  hASel : A ≠ Sel
  /-- Treatment and outcome are distinct nodes. -/
  hAY : A ≠ Y
  /-- Selection and outcome are distinct nodes. -/
  hSelY : Sel ≠ Y

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- For [a Lee sample-selection system](hyp:S), the [binary treatment potential-outcome variable](goal) is its treatment node with its binary representation. -/
def aVar : POVar P Bool := ⟨S.A, S.hAbool⟩

/-- For [a Lee sample-selection system](hyp:S), the [binary selection-indicator potential-outcome variable](goal) is its selection node with its binary representation. -/
def selVar : POVar P Bool := ⟨S.Sel, S.hSelbool⟩

/-- For [a Lee sample-selection system](hyp:S), the [real-valued outcome potential-outcome variable](goal) is its outcome node with its real-valued representation. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- For [a Lee sample-selection system](hyp:S) and [a treatment arm](hyp:a), the [potential selection indicator](goal) assigns each unit whether its outcome would be selected under that arm.

Counterfactual selection under treatment arm `a`.

This is the function `Sel(a) : P.Ω → Bool`. -/
noncomputable def SelOfA (a : Bool) : P.Ω → Bool := S.selVar.cfUnder S.aVar a

/-- For [a Lee sample-selection system](hyp:S) and [a treatment arm](hyp:a), the [potential outcome](goal) assigns each unit its outcome under that arm.

Counterfactual outcome under treatment arm `a`.

This is the function `Y(a) : P.Ω → ℝ`. -/
noncomputable def YofA (a : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.aVar a

/-- For [a Lee sample-selection system](hyp:S), the [factual treatment](goal) assigns each unit its observed binary treatment. -/
noncomputable def factualA : P.Ω → Bool := S.aVar.factual

/-- For [a Lee sample-selection system](hyp:S), the [factual selection indicator](goal) assigns each unit its observed selection status. -/
noncomputable def factualSel : P.Ω → Bool := S.selVar.factual

/-- For [a Lee sample-selection system](hyp:S), the [factual outcome](goal) assigns each unit its observed real outcome. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- For [a Lee sample-selection system](hyp:S) and [a treatment arm](hyp:a), the [treatment event](goal) is the set of units whose observed treatment equals that arm. -/
def aEvent (a : Bool) : Set P.Ω := S.aVar.event a

/-- For [a Lee sample-selection system](hyp:S) and [a selection status](hyp:s), the [selection event](goal) is the set of units whose observed selection indicator equals that status. -/
def selEvent (s : Bool) : Set P.Ω := S.selVar.event s

/-- For [a Lee sample-selection system](hyp:S), the [selected-treated cell](goal) is the set of units with observed treatment and observed selection both equal to one. -/
def selectedTreated : Set P.Ω := S.aEvent true ∩ S.selEvent true

/-- For [a Lee sample-selection system](hyp:S), the [selected-control cell](goal) is the set of units with observed treatment equal to zero and observed selection equal to one. -/
def selectedControl : Set P.Ω := S.aEvent false ∩ S.selEvent true

/-! ### Measurability -/

/-- Counterfactual selection under any fixed arm is measurable. -/
@[fun_prop]
lemma measurable_SelOfA (a : Bool) : Measurable (S.SelOfA a) :=
  S.selVar.measurable_cfUnder S.aVar a

/-- For [a fixed treatment arm `a`](hyp:a), [the counterfactual outcome `Y(a)` is
measurable](goal). -/
@[fun_prop]
lemma measurable_YofA (a : Bool) : Measurable (S.YofA a) :=
  S.yVar.measurable_cfUnder S.aVar a

/-- Factual treatment is measurable. -/
@[fun_prop]
lemma measurable_factualA : Measurable S.factualA := S.aVar.measurable_factual
/-- Factual selection is measurable. -/
@[fun_prop]
lemma measurable_factualSel : Measurable S.factualSel := S.selVar.measurable_factual
/-- Factual outcome is measurable. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- Each factual treatment arm event is measurable. -/
lemma measurableSet_aEvent (a : Bool) : MeasurableSet (S.aEvent a) :=
  S.aVar.measurableSet_event _ (measurableSet_singleton _)

/-- Each factual selection event is measurable. -/
lemma measurableSet_selEvent (s : Bool) : MeasurableSet (S.selEvent s) :=
  S.selVar.measurableSet_event _ (measurableSet_singleton _)

/-- The selected-treated observed cell is measurable. -/
lemma measurableSet_selectedTreated : MeasurableSet S.selectedTreated :=
  (S.measurableSet_aEvent true).inter (S.measurableSet_selEvent true)

/-- The selected-control observed cell is measurable. -/
lemma measurableSet_selectedControl : MeasurableSet S.selectedControl :=
  (S.measurableSet_aEvent false).inter (S.measurableSet_selEvent true)

end POLeeSystem

end PO
end Causalean

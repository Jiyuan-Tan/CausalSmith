/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.Core.System

/-! # Consistency for Potential Outcomes

This file defines pathwise agreement predicates and separates textbook factual
consistency from the stronger composition property for nested interventions.
The public API consists of `POSystem.FactualAgrees`,
`POSystem.IntermediateAgrees`, `POSystem.Consistency`, and
`POSystem.CompositionConsistency`. Textbook consistency is the factual clause;
composition consistency is a separate modelling assumption used for nested or
sequential regimes. -/

@[expose] public section

namespace Causalean
namespace PO

namespace POSystem

variable (P : POSystem)

/-- For [a potential-outcome system](hyp:P), [an intervention regime](hyp:r), and [a unit in its sample space](hyp:ω), [factual agreement](goal) means that every variable targeted by the regime has, for that unit under the factual regime, exactly the value assigned by the intervention.

For a potential-outcome system, an intervention regime, and a unit in the
sample space, factual agreement means that for every variable targeted by the
regime, the factual value of that variable for the unit equals the value assigned
by the regime.

Pathwise predicate: factual value of `r.target` equals `r.assign` at `ω`. -/
def FactualAgrees (r : Regime P.V P.X) (ω : P.Ω) : Prop :=
  ∀ v (hv : v ∈ r.target), P.eval Regime.empty ω v = r.assign v hv

/-- For [a potential-outcome system](hyp:P), [a first intervention regime](hyp:r₁), [a second intervention regime](hyp:r₂), and [a unit in its sample space](hyp:ω), [intermediate agreement](goal) means that, after the first intervention, every variable targeted by the second has exactly the value assigned by the second.

For a potential-outcome system, two intervention regimes, and a unit in the
sample space, intermediate agreement means that after applying the first regime,
every variable targeted by the second regime has the value assigned to it by the
second regime.

Pathwise predicate: post-`r₁` value of `r₂.target` equals `r₂.assign` at `ω`. -/
def IntermediateAgrees (r₁ r₂ : Regime P.V P.X) (ω : P.Ω) : Prop :=
  ∀ v (hv : v ∈ r₂.target), P.eval r₁ ω v = r₂.assign v hv

/-- For [a potential-outcome system](hyp:P), [consistency](hyp:factual) says
that whenever a unit factually receives an intervention regime, every non-target
potential outcome under that regime equals its observed factual outcome.

This is the observed/counterfactual linkage component of consistency in Hernán
and Robins (2020, §3.5). Their §3.4 separately discusses the requirement that
counterfactual outcomes be sufficiently well-defined, which this structure does
not encode. See also Cole and Frangakis (2009). A researcher studying a one-shot
treatment can assume this linkage without also imposing a recursive composition
law. -/
structure Consistency (P : POSystem) : Prop where
  /-- Factual consistency. -/
  factual :
    ∀ (r : Regime P.V P.X) (Y : Finset P.V),
      _root_.Disjoint Y r.target →
      ∀ ω : P.Ω, P.FactualAgrees r ω →
        P.poVariable r Y ω = P.poVariable Regime.empty Y ω

/-- For [a potential-outcome system](hyp:P), [composition consistency for nested
or sequential interventions](hyp:composition) says that an intervention which
assigns variables their values after a first disjoint intervention can be
removed from the composed regime.

This is the nested-regime form of composition in Pearl (2009, §7.3,
Property 1, eq. 7.19) and recursive substitution in Robins (1986). It is a separate
modelling assumption: automatic for a potential-outcome system induced by an
SCM, but genuinely additional for a bare potential-outcome system. It is needed
for sequential or nested-regime arguments such as the g-formula, front-door
identification, and dynamic treatment regimes, rather than for ordinary
single-treatment consistency. -/
structure CompositionConsistency (P : POSystem) : Prop where
  /-- Composition / nested consistency. -/
  composition :
    ∀ (r₁ r₂ : Regime P.V P.X) (h : r₁.Disjoint r₂) (Y : Finset P.V),
      _root_.Disjoint Y (r₁.target ∪ r₂.target) →
      ∀ ω : P.Ω, P.IntermediateAgrees r₁ r₂ ω →
        P.poVariable (r₁.sqcup r₂ h) Y ω = P.poVariable r₁ Y ω

end POSystem

end PO
end Causalean

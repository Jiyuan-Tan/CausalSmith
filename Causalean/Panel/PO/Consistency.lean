/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Panel consistency

Consistency is an assumption relating independently stored factual outcomes to
the corresponding potential outcomes at the realized exposure.  It is stated
only for observed cells `r ∈ R`, the support on which the panel records
outcomes and weights.
-/

import Causalean.Panel.PO.CellPO

/-! # Panel Consistency

This file states the panel consistency property for a `PanelPOSystem`. The
predicate `PanelPOSystem.observedY_eq_potentialOutcome` is the pointwise
observed-cell equality, while `PanelConsistency` requires it for every observed
cell and sample point. The lemma `panelConsistency_holds` exposes the equality
directly from the assumption. -/

namespace Causalean
namespace Panel

namespace PanelPOSystem

variable (P : PanelPOSystem)

/-- For [a panel potential-outcomes system](hyp:P), [an observed unit-period cell](hyp:r,hr),
and [a sample point](hyp:ω), [pointwise consistency is the assertion that the factual observed
outcome equals the potential outcome at that cell under the exposure realized at that sample
point](goal). -/
def observedY_eq_potentialOutcome (r : P.I × P.T) (hr : r ∈ P.cells.observed)
    (ω : P.Ω) : Prop :=
  P.observedY r hr ω = P.Y r hr (P.observedExposure r hr ω) ω

end PanelPOSystem

/-- For [a panel potential-outcomes system](hyp:P), [the panel consistency condition](goal)
requires that, for every observed unit-period cell and every sample point, the factual observed
outcome equals the potential outcome at that cell under the exposure realized at that sample point. -/
def PanelConsistency (P : PanelPOSystem) : Prop :=
  ∀ (r : P.I × P.T) (hr : r ∈ P.cells.observed) (ω : P.Ω),
    P.observedY_eq_potentialOutcome r hr ω

/-- If [panel consistency holds for the panel potential-outcome system `P`](hyp:hP), then [the
factual observed outcome equals the potential outcome evaluated at the realized exposure, for
every observed unit-period cell and every sample point](goal). -/
lemma panelConsistency_holds (P : PanelPOSystem) (hP : PanelConsistency P) :
    ∀ (r : P.I × P.T) (hr : r ∈ P.cells.observed) (ω : P.Ω),
      P.observedY r hr ω = P.Y r hr (P.observedExposure r hr ω) ω :=
  hP

end Panel
end Causalean

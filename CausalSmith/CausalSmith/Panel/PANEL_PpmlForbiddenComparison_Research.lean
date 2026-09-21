/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Basic
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Collapse
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.ForbiddenSign
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.FourCohort
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FiniteCollapse
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.Frontier
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FrontierSign
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.PoissonArgmaxDerivative
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWL
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWLContinuity
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Homogeneous
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.PrimitiveFrontier
public import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
public import Causalean.Stat.MEstimation.ArgmaxStability
public import Causalean.Stat.MEstimation.FinitePoisson
public import Causalean.Stat.MEstimation.FinitePoissonConsistency
public import Causalean.Stat.MEstimation.FinitePoissonDerivative
public import Causalean.Stat.MEstimation.FinitePoissonSign

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Basic
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.DornScope
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.HolderCompletion
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.LowerPair
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Model
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Density
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Geometry
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Ranking
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Setwise
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Bias
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Coefficients
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Asymptotics
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Base
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Budget
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Fibre
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.MGF
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Maximal
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Measurability
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Rank
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.TemplateAlgebra
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.TemplateGeometry
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Witnesses
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TAdaptiveMinimax
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TDornA3FreeCorollary
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TRegularVariationReduction
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TStrictEnlargement

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

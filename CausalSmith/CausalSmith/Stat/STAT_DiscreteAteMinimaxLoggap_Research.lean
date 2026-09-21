/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Basic
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ChebyshevCertificate
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.CombinedEnvelope
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Endpoint
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FactorialMoments
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCell
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCellMoments
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HybridProgram
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCell
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellAssembly
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRate
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRateAsymptotic
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRateDeterministic
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRatePilot
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellVariance
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MultinomialMoments
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MvPolynomialEnvelope
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotConditioning
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotSandwich
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ShiftedChebyshev
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.T_OverlapAdaptiveUniversalHybrid
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.T_SharpMinimaxFixedInterior
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.T_TwoCategoryConfounding

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Basic
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Capacities
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.CitedGates
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.DerivedMargins
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.FiniteSupport
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.IntervalArithmetic
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.PolicyAtoms
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Projection
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Sampling
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Scan
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.SlicePasting
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.OpenQuestions
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TFinitePolicyGridProjectionCorollary
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TFiniteSampleOptimizerCoverage
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TLinearWholeCurveScan
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TPerfectReferenceReduction
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TProjectionOptimizerSandwich
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpMassSupport
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpRegretFormula
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TStrictRectangularLoss
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSubmeasureBijection

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Basic
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.BernsteinSpan
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.Chebyshev
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.CitedAnalysis
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.ExactMultinomial
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.FullSupport
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.LimitedPooling
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentReduction
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.RealAlgebraic
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_BoundaryDiracRegression
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_BoundaryFiberAtlas
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_ExactCadRecovery
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_FiniteComplexityInference
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_GrowingPlateModulus
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_IdentificationFrontier
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_MOneRegression
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_OptimizedLimitedPooling
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpEnvelopeDomination
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpPrimalDual
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_WholeSetCoverage

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Completion
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Frontier
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.MultiOrder
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Sampling
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Separated
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.World
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.CitedGates
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.InterventionAlgebra
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.KernelMatching
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.LawFiber
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.TensorPencil
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.VeroneseKruskal
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.THeterogeneousOrderBoundary
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TIdentificationCountermodels
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TSharpEffectFrontier
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TSquareReduction
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TUniformConfidenceFrontier

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

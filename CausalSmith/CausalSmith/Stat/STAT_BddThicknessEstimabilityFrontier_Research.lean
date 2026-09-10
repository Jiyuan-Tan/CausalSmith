/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Basic
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.BandWidth
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Benchmark
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.DiskPattern
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Estimator
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Geometry
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Testing
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.TubeCoords
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ArbitraryModulusTwoSidedBracket
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ExponentialHornConsistency
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_GlobalHonestBand
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_HonestAdaptiveBandsQuestion
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_LowerProfileOnlyClass
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ObservedLawIdentification
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_PervasiveAdaptiveFrontier
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ThicknessEntropySeparation

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

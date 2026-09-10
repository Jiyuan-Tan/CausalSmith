/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Basic
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Fibers
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FiniteSCM
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FiniteSampleCoverage
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FixedWaldLocalization
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Perturbation
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.RegularBenchmark
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Sampling
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.SetGeometry
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.StudentizedWitness
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TriangularArray
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TruncatedSVD
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TwoSampleProductTV
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Witness
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TFiniteSampleProjectionCoverage
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TPositiveFullLawConverse
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TStrictFullrankExtension
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TStudentizedUniformProjection
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TTargetSpanIff

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/

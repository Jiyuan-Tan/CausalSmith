/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.Martingale.Basic
public import Causalean.Stat.Limit.Convergence

/-!
# Compatibility between row-wise and fixed-space convergence wrappers

The row-wise convergence API permits a different probability space in every row, whereas the
scalar Slutsky and delta-method API uses one fixed probability space. This module records the
definitional bridge obtained by specializing the row laws to a constant family.
-/

public section

namespace Causalean.Stat

open MeasureTheory

/-- For [a fixed source probability law](hyp:μ), [a target probability law](hyp:Q), and
[almost-everywhere measurable row variables](hyp:Y,hY), [the row-wise convergence wrapper is
equivalent to the scalar fixed-space convergence wrapper](goal). -/
theorem tendstoInDistribution_iff_tendsto_dist
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hY : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun _ => μ) Y Q hY ↔ Tendsto_dist Y Q μ hY :=
  Iff.rfl

end Causalean.Stat

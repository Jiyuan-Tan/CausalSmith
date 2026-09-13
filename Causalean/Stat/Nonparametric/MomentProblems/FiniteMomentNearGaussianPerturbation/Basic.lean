/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.MomentCumulantInversion
import Causalean.Stat.Nonparametric.MomentProblems.RawMoment
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Hamburger--Carleman series

This module fixes the Carleman-series notation used by the finite Gaussian perturbation
construction.  The series is built from the shared raw moments `rawMoment` and uses the positive
even orders `2 * (s + 1)`; closeness to the Gaussian is measured with the library's testing
total-variation distance `Causalean.Stat.tvDist`.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Given [a real measure](hyp:ν), the [explicit Hamburger--Carleman series](goal) is [given by
the sum of inverse roots of its positive even raw moments](step:1). It is the Carleman series only
for a measure whose even moments exist: a non-integrable even power has raw moment zero by the
integral convention, and the zero base with a negative exponent makes that term infinite. -/
noncomputable def hamburgerCarlemanSeries (ν : Measure ℝ) : ℝ≥0∞ :=
  ∑' s : ℕ,
    (ENNReal.ofReal |rawMoment ν (2 * (s + 1))|).rpow
      (-(1 : ℝ) / (2 * (s + 1)))

/-- For [a real measure](hyp:ν), [the Hamburger--Carleman notation equals its explicit
integral-series formula](goal). -/
theorem hamburgerCarlemanSeries_eq (ν : Measure ℝ) :
    hamburgerCarlemanSeries ν =
      ∑' s : ℕ,
        (ENNReal.ofReal |∫ x, x ^ (2 * (s + 1)) ∂ν|).rpow
          (-(1 : ℝ) / (2 * (s + 1))) := rfl

end Causalean.Stat.MomentProblems

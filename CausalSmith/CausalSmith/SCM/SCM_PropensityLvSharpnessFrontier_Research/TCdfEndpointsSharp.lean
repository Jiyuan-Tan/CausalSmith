import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TSupportRegimeCdfEndpointsSharp

/-! # Sharp mutual-support CDF endpoints -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- The exact mutual-support bow-SCM identified interval at every threshold is
the atom-aware endpoint interval, and both endpoints are attained.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:cdf-endpoints-sharp
theorem cdf_endpoints_sharp (a : Bool) (e : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (y : ℝ) :
    {r : ℝ | ∃ Q ∈ bowCompatibleSet a e P, r = cdf Q y} =
      Set.Icc (cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y)).1
        (cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y)).2 := by
  exact (support_regime_cdf_endpoints_sharp a e P hPos y).2

end CausalSmith.SCM.PropensityLvSharpnessFrontier

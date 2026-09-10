import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Basic
import Mathlib.Probability.CDF

/-! # Atom-aware and unrestricted CDF endpoint maps -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- Atom-aware mutual-support endpoint pair. -/
-- @node: def:cdf-maps
noncomputable def cdfEndpoints (e p : Set.Icc (0 : ℝ) 1) : ℝ × ℝ :=
  (if p.1 < 1 then e.1 * p.1 else 1,
    if p.1 = 0 then 0 else e.1 * p.1 + 1 - e.1)
  -- @realizes L_e(p),U_e(p)(piecewise atom-aware endpoint pair)
  -- @realizes p(observed event-probability argument)

/-- Continuous unrestricted endpoint pair. -/
-- @node: def:cdf-maps-one-sided
def cdfEndpointsOneSided (e p : Set.Icc (0 : ℝ) 1) : ℝ × ℝ :=
  (e.1 * p.1, e.1 * p.1 + 1 - e.1)
  -- @realizes L^{\to}_e(p),U^{\to}_e(p)(continuous one-sided endpoints)
  -- @realizes p(one-sided endpoint argument restricted to [0,1])

/-- A maintained-support propensity as a point of `[0,1]`. -/
def endpointPropensity (e : ℝ) (he : StrictPositivity e ∨ e = 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨e, by
    rcases he with he | rfl
    · exact ⟨le_of_lt he.1, le_of_lt he.2⟩
    · exact ⟨zero_le_one, le_rfl⟩⟩

/-- A probability-law CDF value as a point of `[0,1]`. -/
noncomputable def cdfProbability (P : Measure ℝ) [IsProbabilityMeasure P] (y : ℝ) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨cdf P y, cdf_nonneg P y, cdf_le_one P y⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier

module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogSharp
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality

/-! A measure-theoretic realization of the finite three-score coupling problem. -/

@[expose] public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory

noncomputable section

/-- For [the specified mathematical inputs](hyp:q,t), [this definition](goal) introduces the corresponding object. -/
def threeScoreOutcomeLaw (q t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (t / q) • Measure.dirac 1 +
    ENNReal.ofReal (1 - t / q) • Measure.dirac 0

/-- For [the specified mathematical inputs](hyp:x,y,z,w₁,w₂,w₃), [this definition](goal) introduces the corresponding object. -/
def threeScoreInverseLaw (x y z w₁ w₂ w₃ : ℝ) : Measure ℝ :=
  let q := x * w₁ + y * w₂ + z * w₃
  (ENNReal.ofReal (x * w₁ / q) • Measure.dirac (1 / x) +
    ENNReal.ofReal (y * w₂ / q) • Measure.dirac (1 / y)) +
    ENNReal.ofReal (z * w₃ / q) • Measure.dirac (1 / z)

end
end CausalSmith.PartialID.UnlinkedPropensityAte

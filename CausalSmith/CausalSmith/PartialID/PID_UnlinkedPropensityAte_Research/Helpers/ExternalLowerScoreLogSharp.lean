module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogCalibration
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogPair

/-! Explicit three-score couplings for the score-log sharp endpoints. -/

@[expose] public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:x,y,w₁,t), [this definition](goal) introduces the corresponding object. -/
def threeScoreUpperEndpoint (x y w₁ t : ℝ) : ℝ :=
  w₁ + (t - x * w₁) / y

/-- For [the specified mathematical inputs](hyp:z,t), [this definition](goal) introduces the corresponding object. -/
def threeScoreLowerEndpoint (z t : ℝ) : ℝ :=
  t / z

/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,t,u,hx,hxy), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreUpperEndpoint_perturbation
    (x y z t u : ℝ) (hx : 0 < x) (hxy : x < y) :
    threeScoreUpperEndpoint x y (1 / 3 + u * (z - y)) t -
      threeScoreUpperEndpoint x y (1 / 3) t =
      u * (z - y) * (1 - x / y) := by
  unfold threeScoreUpperEndpoint
  exact fiberTriple_upperEndpoint_shift x y z t u (ne_of_gt (lt_trans hx hxy))

end
end CausalSmith.PartialID.UnlinkedPropensityAte

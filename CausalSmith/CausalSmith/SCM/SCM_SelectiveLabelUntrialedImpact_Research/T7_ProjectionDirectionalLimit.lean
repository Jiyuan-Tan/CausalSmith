import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Inference
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T2_SharpInterval

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! # Projection-composed directional limit -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open MeasureTheory

variable {O T OBlind Ω : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]
  [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSingletonClass O]
  {μ : Measure Ω} {P : Measure O}

/-- Projection followed by the two endpoint programs is Hadamard
directionally differentiable even at projection faces and LP ties, and the
plug-in endpoint estimator converges to the displayed Gaussian image. -/
-- @node: thm:projection-composed-directional-limit
theorem projection_composed_directional_limit
    (G : SLCCIncidence O T OBlind) (p : O → ℝ)
    (S : Causalean.Stat.IIDSample Ω O μ P)
    (hIID : IidFiniteSampling μ P S G p) :
    Causalean.Stat.HasHadamardDirDerivAt
      (fun x => sharpEndpointPrograms G (metricProjection (observablePolytope G) x))
      (projectionComposedDerivative G p) p ∧
    WeakConvergence μ
      (fun n ω => Real.sqrt n •
        (projectionEndpointEstimator G (empiricalLaw S n ω) - sharpEndpointPrograms G p))
      ((multinomialGaussianLaw p).map (projectionComposedDerivative G p)) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact

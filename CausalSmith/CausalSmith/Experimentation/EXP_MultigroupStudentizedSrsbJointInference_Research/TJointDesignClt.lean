import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.BlockMoments
import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.CitedGates
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Joint design-based martingale CLT for the direct-and-spillover estimator. -/

open scoped BigOperators
open Filter Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass

noncomputable section

def complexDesignExpectation {Omega : Type*} [Fintype Omega]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Omega)
    (X : Omega → ℂ) : ℂ :=
  ∑ w, (D.p w : ℂ) * X w

def JointGaussianLimit {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) (OmegaRR : Mat2) : Prop :=
  ∀ c : Vec2,
    Tendsto (fun N ↦ complexDesignExpectation (Mdl N).design (fun w ↦
      Complex.exp (Complex.I * (vecDot c (Real.sqrt ((Mdl N).G * (Mdl N).B) •
        (jointHTEstimator (Mdl N) w - jointEstimand (Mdl N))) : ℂ)))) atTop
      (nhds (Complex.exp (-(matQuad OmegaRR c : ℂ) / 2)))

-- @node: thm:joint-design-clt
theorem joint_design_clt
    {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (OmegaRR : Mat2)
    (hBlocks : Tendsto (fun N ↦ (Mdl N).B) atTop atTop)
    (hUniform : SharedModelConstants Mdl)
    (hRR : RRCovarianceStabilization
      (fun N ↦ (Mdl N).design)
      (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR)
    (hPositive : RRLimitPositive OmegaRR) :
    JointGaussianLimit Mdl OmegaRR := by sorry

end


end CausalSmith.Experimentation.MultigroupStudentizedSRSB

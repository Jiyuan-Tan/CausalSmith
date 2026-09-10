import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.TJointDesignClt
import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.TStudentizer
import Causalean.Stat.CLT.ChiSquaredProjection

/-! Simultaneous conservative Wald coverage for both causal contrasts. -/

open Filter Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass

noncomputable def waldCoverageProbability {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) : ℝ := by
  classical
  exact Mdl.design.Pr (fun w ↦ jointEstimand Mdl ∈
    simultaneousWaldRegion Mdl.G Mdl.B (jointHTEstimator Mdl w)
      (gammaClipped Mdl w) Mdl.alpha)

-- @node: thm:wald-coverage
theorem simultaneous_wald_coverage
    {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (OmegaRR : Mat2) (alpha : ℝ)
    (hBlocks : Tendsto (fun N ↦ (Mdl N).B) atTop atTop)
    (hUniform : SharedModelConstants Mdl)
    (hClip : SharedClippingSequence Mdl)
    (hAlpha : alpha ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ N, (Mdl N).alpha = alpha)
    (hRR : RRCovarianceStabilization (fun N ↦ (Mdl N).design)
      (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR)
    (hPositive : RRLimitPositive OmegaRR) :
    ∀ ε : ℝ, 0 < ε → ∃ N0, ∀ N, N0 ≤ N →
      1 - alpha - ε ≤ waldCoverageProbability (Mdl N) := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB

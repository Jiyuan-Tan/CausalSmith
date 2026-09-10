import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.TWeightedGaussianTransport
import Causalean.Experimentation.DesignBased.InProb

/-! Projection formula comparing soft rerandomization with complete randomization. -/

open Filter Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass

def UniformProjectionApproximation {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0, ∀ N, N0 ≤ N → ∀ (w : O N) (b : Fin (Mdl N).B),
    matMaxAbs (rrCovariance (Mdl N) w b - completeRandomizationCovariance (Mdl N) w b +
      projectionGain (Mdl N).eta (Mdl N).kappa
        (outer (projectionLoading (Mdl N) w b) (projectionLoading (Mdl N) w b))) < ε

-- @node: thm:projection-covariance
theorem projection_covariance
    {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (OmegaRR OmegaCR P : Mat2)
    (hWindow : ∀ N, ImbalanceVarianceWindow (Mdl N).cSigma (Mdl N).CSigma (Mdl N).sigmaSq)
    (hUniform : SharedModelConstants Mdl)
    (hCR : CRCovarianceStabilization (fun N ↦ (Mdl N).design)
      (fun N w ↦ avgSigmaCR (Mdl N) w) OmegaCR)
    (hRR : RRCovarianceStabilization (fun N ↦ (Mdl N).design)
      (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR)
    (hProjection : ProjectionStabilization (fun N ↦ (Mdl N).design)
      (fun N w ↦ avgProjection (Mdl N) w) P)
    (hGroups : Tendsto (fun N ↦ (Mdl N).G) Filter.atTop Filter.atTop) :
    UniformProjectionApproximation Mdl ∧
    OmegaRR = OmegaCR - projectionGain (Mdl 0).eta (Mdl 0).kappa P ∧
    Matrix.PosSemidef P ∧
    ∀ c : Vec2, c ≠ 0 →
      (matQuad OmegaRR c < matQuad OmegaCR c ↔ 0 < matQuad P c) := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB

import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.BlockMoments
import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.PerfectMatching
import Causalean.Mathlib.OperatorSqrt
import Causalean.Experimentation.DesignBased.EdgeVarianceBound

/-! Singular-covariance weighted Gaussian transport for the balanced score. -/

open scoped BigOperators
open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open Causalean.Experimentation.DesignBased
open BoundedLagOnePartialInterferenceClass

noncomputable section

-- @node: thm:weighted-gaussian-transport
theorem weighted_gaussian_transport
    {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (hUniform : SharedModelConstants Mdl)
    (hGroups : Tendsto (fun N ↦ (Mdl N).G) atTop atTop) :
    ∃ epsilon_G : ℕ → ℝ,
      (∀ N, 0 ≤ epsilon_G N) ∧ Tendsto epsilon_G atTop (nhds 0) ∧
      ∀ N (w : O N) (b : Fin (Mdl N).B),
        ∃ QA QR : Measure Vec3,
          IsCenteredGaussianWithCovariance QA
            (scoreBalanceCovariance ((Mdl N).referenceDesign w b) (fun z ↦ blockA (Mdl N) z b)
              (fun z ↦ standardizedBalance (Mdl N) w b ((Mdl N).x z b))) ∧
          IsCenteredGaussianWithCovariance QR
            (scoreBalanceCovariance ((Mdl N).referenceDesign w b) (fun z ↦ blockR (Mdl N) z b)
              (fun z ↦ standardizedBalance (Mdl N) w b ((Mdl N).x z b))) ∧
          |rawSoftScalarMoment ((Mdl N).referenceDesign w b) (Mdl N).eta (Mdl N).kappa
              (fun z ↦ standardizedBalance (Mdl N) w b ((Mdl N).x z b)) -
              gaussianSoftScalarMoment QA (Mdl N).eta (Mdl N).kappa| +
            matMaxAbs (rawSoftMatrixMoment ((Mdl N).referenceDesign w b)
              (Mdl N).eta (Mdl N).kappa (fun z ↦ blockA (Mdl N) z b)
              (fun z ↦ standardizedBalance (Mdl N) w b ((Mdl N).x z b)) -
              gaussianSoftMatrixMoment QA (Mdl N).eta (Mdl N).kappa) ≤ epsilon_G N ∧
          matMaxAbs (rawSoftMatrixMoment ((Mdl N).referenceDesign w b)
              (Mdl N).eta (Mdl N).kappa (fun z ↦ blockR (Mdl N) z b)
              (fun z ↦ standardizedBalance (Mdl N) w b ((Mdl N).x z b)) -
              gaussianSoftMatrixMoment QR (Mdl N).eta (Mdl N).kappa) ≤ epsilon_G N := by sorry
-- @realizes \varepsilon_G(deterministic nonnegative transport modulus tending to zero)
-- @realizes (A_b^\star,W_b^\star)(first covariance-matched Gaussian law QA)
-- @realizes (R_b^\star,W_b^\star)(second covariance-matched Gaussian law QR)

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB

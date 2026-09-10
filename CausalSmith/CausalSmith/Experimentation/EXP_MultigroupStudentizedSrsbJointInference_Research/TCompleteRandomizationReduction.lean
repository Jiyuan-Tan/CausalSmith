import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.Studentizer
import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.BlockScore

/-! Boundary reduction of the soft kernel to ordinary complete randomization. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open Causalean.Experimentation.DesignBased
open BoundedLagOnePartialInterferenceClass

noncomputable def ordinaryBalancedTwoStageHT {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) : Vec2 :=
  jointHTEstimator Mdl w

noncomputable def ordinaryBalancedTwoStageStudentizer {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) :=
  completedStudentizer Mdl w

-- @node: prop:complete-randomization-reduction
theorem complete_randomization_reduction :
    (∀ kappa w : ℝ, radialWeight 1 kappa w = 1) ∧
    (∀ eta w : ℝ, radialWeight eta 0 w = 1) ∧
    (∀ (P : Mat2) (kappa eta : ℝ),
      projectionGain 1 kappa P = 0 ∧ projectionGain eta 0 P = 0) ∧
    (∀ (Omega : Type*) (_ : Fintype Omega) (D : FiniteDesign Omega) (z : Omega)
      (hweight : ∀ u, 0 ≤ (1 : ℝ)) (hnorm : D.E (fun _ ↦ (1 : ℝ)) ≠ 0),
      (softTilt D (fun _ ↦ (1 : ℝ)) hweight hnorm).p z = D.p z) ∧
    (∀ (Omega : Type*) (_ : Fintype Omega)
      (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) (b : Fin Mdl.B),
      Mdl.eta = 1 ∨ Mdl.kappa = 0 →
      rrCovariance Mdl w b = referenceConditionalCovVec Mdl b w (fun z ↦ blockR Mdl z b)) ∧
    (∀ (Omega : Type*) (_ : Fintype Omega)
      (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega),
      Mdl.eta = 1 ∨ Mdl.kappa = 0 →
      jointHTEstimator Mdl w = ordinaryBalancedTwoStageHT Mdl w ∧
      completedStudentizer Mdl w = ordinaryBalancedTwoStageStudentizer Mdl w) ∧
    (∀ (O : ℕ → Type*) (inst : ∀ N, Fintype (O N))
      (Mdl : ∀ N, @BoundedLagOnePartialInterferenceClass (O N) (inst N))
      (OmegaRR OmegaCR : Mat2),
      (∀ N w, avgSigmaRR (Mdl N) w = avgSigmaCR (Mdl N) w) →
      RRCovarianceStabilization (fun N ↦ (Mdl N).design)
        (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR →
      CRCovarianceStabilization (fun N ↦ (Mdl N).design)
        (fun N w ↦ avgSigmaCR (Mdl N) w) OmegaCR →
      OmegaRR = OmegaCR) := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB

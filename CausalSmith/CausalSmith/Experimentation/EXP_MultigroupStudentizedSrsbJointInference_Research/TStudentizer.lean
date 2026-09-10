import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.Studentizer
import Causalean.Mathlib.Topology.SubsequentialLimits

/-! Conservativeness, many-block expansion, and spectral clipping of the studentizer. -/

open scoped BigOperators
open Filter Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass

noncomputable section

def gammaBlocks {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) :=
  (completedStudentizer Mdl w).1

def gammaAverage {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) :=
  (completedStudentizer Mdl w).2.1

def gammaClipped {Omega : Type*} [Fintype Omega]
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) :=
  (completedStudentizer Mdl w).2.2

def matrixResidualConvergesInProbability {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (X : (N : ℕ) → O N → Mat2) : Prop :=
  rowMatrixConvergesInProbability (fun N ↦ (Mdl N).design) X 0

def InverseBoundedInProbability {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N0, ∀ N, N0 ≤ N →
    (Mdl N).design.Pr (fun w ↦ matMaxAbs ((gammaClipped (Mdl N) w)⁻¹) > C) ≤ ε

def ProbabilityLimitPointsDominate {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N)) (OmegaRR : Mat2) : Prop :=
  ∀ (phi : ℕ → ℕ), StrictMono phi → ∀ L : Mat2,
    rowMatrixConvergesInProbability
      (fun k ↦ (Mdl (phi k)).design)
      (fun k w ↦ gammaAverage (Mdl (phi k)) w) L →
    Matrix.PosSemidef (L - OmegaRR)

-- @node: thm:studentizer
theorem completed_studentizer_conservative
    {O : ℕ → Type*} [∀ N, Fintype (O N)]
    (Mdl : ∀ N, BoundedLagOnePartialInterferenceClass (O N))
    (OmegaRR : Mat2) :
    (∀ N (w : O N) b,
      (∀ i j, conditionalE (Mdl N) b w (fun z ↦ gammaBlocks (Mdl N) z b i j) =
        (rrCovariance (Mdl N) w b + completionBias (Mdl N) w b) i j) ∧
      Matrix.PosSemidef (completionBias (Mdl N) w b)) ∧
    (SharedModelConstants Mdl → ∃ C : ℝ, ∀ N (w : O N) b,
      matMaxAbs (gammaBlocks (Mdl N) w b) ≤ C ∧
      matMaxAbs (completionBias (Mdl N) w b) ≤ C) ∧
    (Tendsto (fun N ↦ (Mdl N).B) atTop atTop → SharedModelConstants Mdl →
      RRCovarianceStabilization (fun N ↦ (Mdl N).design)
        (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR →
      matrixResidualConvergesInProbability Mdl (fun N w ↦
        gammaAverage (Mdl N) w - OmegaRR -
          ((Mdl N).B : ℝ)⁻¹ • ∑ b, completionBias (Mdl N) w b) ∧
      ProbabilityLimitPointsDominate Mdl OmegaRR) ∧
    (Tendsto (fun N ↦ (Mdl N).B) atTop atTop → SharedModelConstants Mdl →
      SharedClippingSequence Mdl →
      RRCovarianceStabilization (fun N ↦ (Mdl N).design)
        (fun N w ↦ avgSigmaRR (Mdl N) w) OmegaRR →
      RRLimitPositive OmegaRR →
      (∀ ε : ℝ, 0 < ε → ∃ N0, ∀ N, N0 ≤ N →
        (Mdl N).design.Pr (fun w ↦ gammaClipped (Mdl N) w = gammaAverage (Mdl N) w) ≥ 1 - ε) ∧
      InverseBoundedInProbability Mdl) := by sorry

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB

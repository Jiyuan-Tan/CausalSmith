import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.DeterminantEnvelope
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.DeterminantEnvelope
import Causalean.Discovery.LinearDisentanglement.Quantitative.CompactExclusion

/-!
# Ambient compact box for uniform contraction

This module packages the finite-dimensional true-system and candidate-witness variables into a
nested product.  Fixing the retained environment set separately keeps every component normed and
lets compactness follow directly from compactness of closed balls and finite products.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator

/-- Covariance arrays over the fixed finite environment type. -/
abbrev ContractionCovariances (p m : ℕ) := Environment m → RealMatrix p

/-- Shift arrays over the fixed finite environment and coordinate types. -/
abbrev ContractionShifts (p m : ℕ) := Environment m → Fin p → ℝ

/-- True-system variables `(D,D⁻¹,Ω,Σ,s)`. -/
abbrev TrueContractionAmbient (p m : ℕ) :=
  RealMatrix p ×
  (RealMatrix p ×
  (RealMatrix p ×
  (ContractionCovariances p m × ContractionShifts p m)))

/-- Candidate-witness variables `(B,B⁻¹,Γ,Ψ,t)`. -/
abbrev CandidateContractionAmbient (p m : ℕ) :=
  RealMatrix p ×
  (RealMatrix p ×
  (ContractionCovariances p m ×
  (RealMatrix p × ContractionShifts p m)))

/-- Ambient variables `(D,D⁻¹,Ω,Σ,s,B,B⁻¹,Γ,Ψ,t)` used by uniform exclusion. -/
abbrev UniformContractionAmbient (p m : ℕ) :=
  TrueContractionAmbient p m × CandidateContractionAmbient p m

namespace UniformContractionAmbient

variable {p m : ℕ}

abbrev structural (z : UniformContractionAmbient p m) : RealMatrix p := z.1.1
abbrev structuralInv (z : UniformContractionAmbient p m) : RealMatrix p := z.1.2.1
abbrev invariantNoise (z : UniformContractionAmbient p m) : RealMatrix p := z.1.2.2.1
abbrev trueCovariance (z : UniformContractionAmbient p m) : ContractionCovariances p m := z.1.2.2.2.1
abbrev trueShifts (z : UniformContractionAmbient p m) : ContractionShifts p m := z.1.2.2.2.2
abbrev candidate (z : UniformContractionAmbient p m) : RealMatrix p := z.2.1
abbrev candidateInv (z : UniformContractionAmbient p m) : RealMatrix p := z.2.2.1
abbrev selectedCovariance (z : UniformContractionAmbient p m) : ContractionCovariances p m :=
  z.2.2.2.1
abbrev candidateNoise (z : UniformContractionAmbient p m) : RealMatrix p :=
  z.2.2.2.2.1
abbrev candidateShifts (z : UniformContractionAmbient p m) : ContractionShifts p m :=
  z.2.2.2.2.2

end UniformContractionAmbient

/-- Product of common-radius closed balls for all uniform-contraction variables. -/
def uniformContractionBox (p m : ℕ) (R : ℝ) : Set (UniformContractionAmbient p m) :=
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
    Metric.closedBall 0 R)))) ×ˢ
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
  (Metric.closedBall 0 R ×ˢ
    Metric.closedBall 0 R))))

/-- The common-radius ambient box is compact. [This is the asserted conclusion](goal). -/
lemma isCompact_uniformContractionBox (p m : ℕ) (R : ℝ) :
    IsCompact (uniformContractionBox p m R) := by
  unfold uniformContractionBox
  apply IsCompact.prod
  · apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    apply IsCompact.prod
      (ProperSpace.isCompact_closedBall (0 : ContractionCovariances p m) R)
    exact ProperSpace.isCompact_closedBall (0 : ContractionShifts p m) R
  · apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    apply IsCompact.prod
      (ProperSpace.isCompact_closedBall (0 : ContractionCovariances p m) R)
    apply IsCompact.prod (ProperSpace.isCompact_closedBall (0 : RealMatrix p) R)
    exact ProperSpace.isCompact_closedBall (0 : ContractionShifts p m) R

end CausalSmith.ExactID.RobustBackshiftUniformDistance

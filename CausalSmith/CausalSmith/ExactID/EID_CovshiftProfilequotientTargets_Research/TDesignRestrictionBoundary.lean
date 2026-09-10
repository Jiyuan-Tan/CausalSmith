import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Witnesses
import Causalean.Mathlib.StandardGaussian

/-! # Boundary witnesses for the design restrictions -/

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- Every legal-model clause except nonnegative variance shifts. -/
def LegalExceptNonnegative {d E r : ℕ} (M : CovShiftModel d E r) : Prop :=
  AdmissibleDimension d ∧ AdmissibleEnvironmentCount E ∧
  AcyclicObservedSystem M ∧ CenteredGaussianNoises M ∧ BlockIndependentNoises M ∧
  StationaryLatentNoise M ∧ StationaryMeasurementError M ∧ PositiveStructuralNoise M ∧
  PositiveMeasurementNoise M ∧ TargetCardinality M ∧ NoOffTargetShifts M ∧
  PanelTargetCoverage M

-- @node: prop:design-restriction-boundary
theorem design_restriction_boundary :
    let D := restrictionBoundaryWitnesses
    (∃ M : CovShiftModel 3 2 2,
      LegalExceptNonnegative M ∧ ¬NonnegativeVarianceShifts M ∧
      (∀ e j, 0 < M.ω0 j + M.shiftVariance e j) ∧
      M.target = D.target ∧ ∀ e, M.covOf e = D.thetaSigned.cov e) ∧
    (∀ t : Fin 2 → Fin 3, Orders t D.target → ¬Cert D.thetaSigned D.target t) ∧
    (∀ t : Fin 2 → Fin 3, Orders t D.target →
      ∃ hQ : (orderedPrincipalBlock (aggregateShift D.thetaSigned) t).PosDef,
        LDL.lower hQ = 1 ∧ ∃ i : Fin 2,
          transformedTargetBlock D.thetaSigned t hQ (1 : Fin 2).succ i i = -(1 / 2 : ℝ)) ∧
    (∃ M : CovShiftModel 3 2 2,
      LegalCovShiftModel M ∧ M.target = D.target ∧
      (∀ e : Fin 2, ¬∀ j ∈ M.target, 0 < M.shiftVariance e.succ j) ∧
      ∀ e, M.covOf e = D.thetaSplit.cov e) ∧
    (covarianceShift D.thetaSplit (1 : Environment 2)).rank = 1 ∧
    (aggregateShift D.thetaSplit).rank = 2 ∧
    (∀ t : Fin 2 → Fin 3, Orders t D.target → Cert D.thetaSplit D.target t) := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets

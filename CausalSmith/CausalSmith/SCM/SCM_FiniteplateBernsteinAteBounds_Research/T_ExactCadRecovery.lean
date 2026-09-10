import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.RealAlgebraic
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpPrimalDual

/-! # Exact CAD endpoint recovery -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- Rational inputs are represented by rational-valued coordinate vectors. -/
def IsRationalVector {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ i, ∃ r : ℚ, (r : ℝ) = x i

/-- Conditional on the CAD gate, both recovery branches terminate with the
paper's primal witnesses; only the relative-interior branch promises matching
dual certificates, while a boundary failure returns a flag without discarding
the primal endpoints. -/
-- @node: thm:exact-cad-recovery
theorem exact_cad_recovery
    (hCAD_of_gate : CylindricalAlgebraicDecompositionQE)
    (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ) ∧
      (∃ e : ℚ, (e : ℝ) = ε) ∧ IsRationalVector b) →
    ∃ cad, CadAlgorithmCorrect cad ∧
      (b ∈ intrinsicInterior ℝ (bernsteinMomentBody m ε) →
        ∃ out, some out ∈ cadRecoveryProcedure m ε b ∧
          CadCertifiesRecovery cad out ∧
          HasRationalAlgebraicDescription out.1.1 ∧
          HasRationalAlgebraicDescription out.2.1 ∧
          out.1.2.2.2.2 = true ∧ out.2.2.2.2.2 = true) ∧
      (b ∉ bernsteinMomentBody m ε → none ∈ cadRecoveryProcedure m ε b) ∧
      (b ∈ bernsteinMomentBody m ε →
        ∃ out, some out ∈ cadRecoveryProcedure m ε b ∧
          CadCertifiesRecovery cad out ∧
          HasRationalAlgebraicDescription out.1.1 ∧
          HasRationalAlgebraicDescription out.2.1 ∧
          MomentReductionConverse m 1 ε out.1.measure ∧
          MomentReductionConverse m 1 ε out.2.measure ∧
          (out.1.2.2.2.2 = true ↔
            MatchingDualCertificate m ε b true out.1) ∧
          (out.2.2.2.2.2 = true ↔
            MatchingDualCertificate m ε b false out.2)) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

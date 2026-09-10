import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_ExactCadRecovery
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_BoundaryDiracRegression
import Mathlib.Analysis.Convex.Caratheodory

/-! # Truth-invariant boundary fiber atlas -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- A boundary label correctly records point identification and the two
minimum endpoint support sizes. -/
def BoundaryLabelCorrect (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ)
    (label : BoundaryLabel) : Prop :=
  (label.1 = true ↔ lowerEndpoint m ε b = upperEndpoint m ε b) ∧
  1 ≤ label.2.1 ∧ label.2.1 ≤ countIndexCard m ∧
  1 ≤ label.2.2 ∧ label.2.2 ≤ countIndexCard m ∧
  (∃ ν ∈ momentFiber m ε b,
    ateFunctional ν = lowerEndpoint m ε b ∧ SupportedOnAtMost ν label.2.1) ∧
  (∀ k < label.2.1, ¬ ∃ ν ∈ momentFiber m ε b,
    ateFunctional ν = lowerEndpoint m ε b ∧ SupportedOnAtMost ν k) ∧
  (∃ ν ∈ momentFiber m ε b,
    ateFunctional ν = upperEndpoint m ε b ∧ SupportedOnAtMost ν label.2.2) ∧
  (∀ k < label.2.2, ¬ ∃ ν ∈ momentFiber m ε b,
    ateFunctional ν = upperEndpoint m ε b ∧ SupportedOnAtMost ν k)

/-- Conditional on CAD, the relative boundary has a finite truth-invariant
semialgebraic stratification with constant identification dimension and
minimum endpoint support labels, algebraic sample points and minimum-size
witnesses. The atlas output type intentionally contains no cellwise symbolic
witness map; a separately supplied algebraic point is handled by a fresh run. -/
-- @node: thm:boundary-fiber-atlas
theorem boundary_fiber_atlas
    (hCAD_of_gate : CylindricalAlgebraicDecompositionQE)
    (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ) ∧
      (∃ e : ℚ, (e : ℝ) = ε)) →
    ∃ cad, CadAlgorithmCorrect cad ∧
      ∃ atlas ∈ boundaryAtlasHandle m ε,
        CadGeneratesBoundaryAtlas cad atlas ∧
        (∀ cell ∈ atlas.cells, ∀ b ∈ cell,
          BoundaryLabelCorrect m ε b (atlas.label cell)) ∧
        (∀ cell ∈ atlas.cells,
          RationalFormulaDefinesMomentCell cell (atlas.formula cell) ∧
          IsMomentFaceCell m ε cell ∧
          BoundaryLabelCorrect m ε (atlas.sample cell) (atlas.label cell) ∧
          (atlas.sampleEndpoints cell).1.activeAtoms = (atlas.label cell).2.1 ∧
          (atlas.sampleEndpoints cell).2.activeAtoms = (atlas.label cell).2.2) ∧
        (∀ b ∈ intrinsicFrontier ℝ (bernsteinMomentBody m ε),
          (∀ c, HasRationalAlgebraicDescription (b c)) →
          ∃ cell ∈ atlas.cells, b ∈ cell ∧
            ∃ out, some out ∈ cadRecoveryProcedure m ε b ∧
              CadCertifiesRecovery cad out ∧
              BoundaryLabelCorrect m ε b (atlas.label cell) ∧
              out.1.activeAtoms = (atlas.label cell).2.1 ∧
              out.2.activeAtoms = (atlas.label cell).2.2) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

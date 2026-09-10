import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.T_SharpPrimalDual
import Mathlib.MeasureTheory.Measure.Dirac

/-! # Closed-form one-observation regression test -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- Uniform count law for the `m=1` regression case. -/
noncomputable def uniformOneCountLaw : CountIndex 1 → ℝ := fun _ => 1 / 4

/-- The displayed affine upper dual certificate. -/
noncomputable def mOneUpperCertificate (q : CellLaw) : ℝ :=
  1 - (4 / 3 : ℝ) * (q (false, true) + q (true, false))

/-- The displayed affine lower dual certificate. -/
noncomputable def mOneLowerCertificate (q : CellLaw) : ℝ :=
  1 / 3 - (4 / 3 : ℝ) * (q (false, true) + q (true, false))

/-- At `m=1`, overlap `1/4`, and the uniform count law, the exact sharp
interval is `[-1/3,1/3]`, the displayed affine certificates are valid, and
both endpoints have attaining mixing laws with at most four atoms. -/
-- @node: prop:m-one-regression
theorem m_one_regression :
    lowerEndpoint 1 (1 / 4) uniformOneCountLaw = -(1 / 3 : ℝ) ∧
    upperEndpoint 1 (1 / 4) uniformOneCountLaw = (1 / 3 : ℝ) ∧
    (∃ lowerCoeff, IsMinorant 1 (1 / 4) lowerCoeff ∧
      ∀ q ∈ overlapSimplex (1 / 4),
        (∑ c, lowerCoeff c * bernsteinCoordinate 1 c q) = mOneLowerCertificate q) ∧
    (∃ upperCoeff, IsMajorant 1 (1 / 4) upperCoeff ∧
      ∀ q ∈ overlapSimplex (1 / 4),
        (∑ c, upperCoeff c * bernsteinCoordinate 1 c q) = mOneUpperCertificate q) ∧
    (∃ νL ∈ momentFiber 1 (1 / 4) uniformOneCountLaw,
      SupportedOnAtMost νL 4 ∧ ateFunctional νL = -(1 / 3 : ℝ)) ∧
    (∃ νU ∈ momentFiber 1 (1 / 4) uniformOneCountLaw,
      SupportedOnAtMost νU 4 ∧ ateFunctional νU = (1 / 3 : ℝ)) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! # Shifted Chebyshev approximation certificate -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- The overlap interval radius. -/
def overlapRadius (ε : ℝ) : ℝ := 1 - 2 * ε

/-- The shifted normalized degree-`m` Chebyshev residual. -/
noncomputable def shiftedChebyshevResidual (m : ℕ) (ε p : ℝ) : ℝ :=
  (-1 : ℝ) ^ m *
    (Polynomial.Chebyshev.T ℝ m).eval ((2 * p - 1) / overlapRadius ε) /
      (Polynomial.Chebyshev.T ℝ m).eval (1 / overlapRadius ε)

/-- The explicit Chebyshev approximation error certificate. -/
noncomputable def chebyshevError (m : ℕ) (ε : ℝ) : ℝ :=
  1 / (Polynomial.Chebyshev.T ℝ m).eval (1 / overlapRadius ε)

/-- The polynomial envelope constructed from the shifted residual. -/
noncomputable def chebyshevEnvelope (m : ℕ) (ε : ℝ) (q : CellLaw) : ℝ :=
  causalIntegrand q - shiftedChebyshevResidual m ε (treatmentProb q)

lemma chebyshev_certificate (m : ℕ) (ε : ℝ)
    (hm : 1 ≤ m) (hε0 : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ)) :
    chebyshevEnvelope m ε ∈ bernsteinSpan m ∧
    overlapUniformError ε causalIntegrand (chebyshevEnvelope m ε) ≤
      chebyshevError m ε ∧
    chebyshevError m ε =
      1 / Real.cosh (m * Real.arcosh (1 / overlapRadius ε)) ∧
    chebyshevError m ε ≤ overlapRadius ε ^ m ∧
    (2 ≤ m → chebyshevError m ε < overlapRadius ε ^ m) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

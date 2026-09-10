import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionCompactness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Local affine-minor inversion constants

The explicit dimension, conditioning, separation, and scale constants used after the global
compactness argument enters the identity chart.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

/-- Uniform matrix-norm constant from determinant and condition-number control. -/
noncomputable def contractionL0 (p : ℕ) (kappabar : ℝ) : ℝ :=
  ((Nat.factorial p : ℝ) * kappabar ^ (p - 1)) ^ (1 / (p : ℝ))

/-- Local affine-minor inversion constant. -/
noncomputable def contractionK0 (p : ℕ) (gamma0 Mbar kappabar : ℝ) : ℝ :=
  (6 * Mbar / gamma0) *
    Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + contractionL0 p kappabar ^ 2))

/-- Explicit linear contraction modulus. -/
noncomputable def contractionC0 (p : ℕ) (gamma0 Mbar kappabar : ℝ) : ℝ :=
  16 * contractionK0 p gamma0 Mbar kappabar * contractionL0 p kappabar ^ 3

end CausalSmith.ExactID.RobustBackshiftUniformDistance

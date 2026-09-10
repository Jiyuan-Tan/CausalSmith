import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.BoundedClass
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Operations

/-! # Frozen Gaussian covariance-information distance

The local quadratic information norm, opposite-classification set, and its
extended-nonnegative distance from the focal covariance tuple.
-/

open scoped BigOperators ENNReal
open Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

variable {d E r : ℕ}

/-- Squared frozen covariance-information norm. -/
noncomputable def informationNormSq (n : Environment E → ℕ)
    (θ : CovarianceTuple d E) (H : Environment E → RealMatrix d) : ℝ :=
  (1 / 2 : ℝ) * ∑ e, (n e : ℝ) *
    Matrix.trace ((θ.cov e)⁻¹ * H e * (θ.cov e)⁻¹ * H e)
  -- @realizes Hpert(generic symmetric covariance displacement)
  -- @realizes Inorm(one-half weighted Gaussian information quadratic form)

/-- Frozen covariance-information norm as an extended nonnegative value. -/
noncomputable def informationNorm (n : Environment E → ℕ)
    (θ ζ : CovarianceTuple d E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (informationNormSq n θ (fun e => ζ.cov e - θ.cov e)))

/-- Covariance tuples with a classification different from the focal tuple. -/
def oppositeClassificationSet (m M : ℝ) (θ : CovarianceTuple d E) (r : ℕ) :
    Set (CovarianceTuple d E) :=
  {ζ | ζ ∈ ThetaK d E r m M ∧ completeClassification ζ r ≠ completeClassification θ r}
  -- @realizes Ah(opposite-classification set inside ThetaK)

-- @node: def:classification-information-distance
noncomputable def classificationInformationDistance (m M : ℝ)
    (n : Environment E → ℕ) (θ : CovarianceTuple d E) (r : ℕ) : ℝ≥0∞ :=
  sInf {a | ∃ ζ ∈ oppositeClassificationSet m M θ r, a = informationNorm n θ ζ}
  -- @realizes deltan(infimum information distance; empty infimum is infinity)

end CausalSmith.ExactID.CovshiftProfilequotientTargets

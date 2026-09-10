import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Certificate
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.longLine false

/-! # Bounded exact-rank covariance class

The Loewner-bounded, common-range, certificate-bearing parameter class used
for uniform inference.
-/

open Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @env: S3
variable {d E r : ℕ}

-- @node: ass:bounded-covariance-member
def BoundedCovarianceMember (m M : ℝ) (ζ : CovarianceTuple d E) : Prop :=
  0 < m ∧ m < M ∧ -- @realizes m(strictly positive lower bound) @realizes M(upper bound strictly above m)
  ∀ e,
    (ζ.cov e - m • (1 : RealMatrix d)).PosSemidef ∧ -- @realizes m(lower Loewner bound) @realizes zeta(generic covariance tuple)
    (M • (1 : RealMatrix d) - ζ.cov e).PosSemidef -- @realizes M(upper Loewner bound)

-- @node: ass:bounded-reference-rank
def BoundedAggregateRank (ζ : CovarianceTuple d E) (r : ℕ) : Prop :=
  (aggregateShift ζ).rank = r

-- @node: ass:bounded-common-range
def BoundedCommonRange (ζ : CovarianceTuple d E) : Prop :=
  ∀ e : Fin E,
    LinearMap.range (Matrix.mulVecLin (covarianceShift ζ e.succ)) ≤
      LinearMap.range (Matrix.mulVecLin (aggregateShift ζ))

-- @node: ass:bounded-certificate-exists
def BoundedCertificateExists (ζ : CovarianceTuple d E) (r : ℕ) : Prop :=
  ∃ T : Finset (Fin d), T.card = r ∧
    ∃ t : Fin r → Fin d, Orders t T ∧ Cert ζ T t
  -- @realizes T(candidate target set of size r)

-- @node: def:bounded-covariance-class
structure BoundedCovarianceClass (m M : ℝ) (ζ : CovarianceTuple d E) (r : ℕ) : Prop where
  bounded : BoundedCovarianceMember m M ζ
  exactRank : BoundedAggregateRank ζ r
  commonRange : BoundedCommonRange ζ
  certificate : BoundedCertificateExists ζ r

/-- The bounded covariance parameter space `Θ_K`. -/
def ThetaK (d E r : ℕ) (m M : ℝ) : Set (CovarianceTuple d E) :=
  {ζ | Nonempty (BoundedCovarianceClass m M ζ r)}
  -- @realizes ThetaK(Loewner-bounded exact-rank certificate class)

end CausalSmith.ExactID.CovshiftProfilequotientTargets

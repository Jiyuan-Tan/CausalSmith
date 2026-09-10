import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Common finite-dimensional notation for collision-safe spectral laws

This module fixes the Euclidean matrix carrier and its spectral operator norm.  The remaining
modules use these definitions for rectangular Moore--Penrose inverses, nonnormal functional
calculus, and finite atomic laws.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped BigOperators Matrix.Norms.L2Operator

/-- `Euc n` is real Euclidean `n`-space with its two-norm. -/
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `RectMatrix rows cols` is the type of real `rows`-by-`cols` matrices. -/
abbrev RectMatrix (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) ℝ

/-- A real rectangular matrix regarded as a continuous linear map between Euclidean spaces. -/
noncomputable def matrixCLM {rows cols : ℕ} (A : RectMatrix rows cols) :
    Euc cols →L[ℝ] Euc rows :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

/-- The zero-based singular value of a real rectangular matrix, in decreasing order. -/
noncomputable def singularValue {rows cols : ℕ} (A : RectMatrix rows cols) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

end CausalSmith.Substrate.CollisionSafeSpectralLaw

import Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.AbsoluteValue
import Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Positivity
import Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Restriction

/-!
# Finite positive Perron eigenvector

This module assembles the finite-dimensional Perron--Frobenius theorem for a
real symmetric irreducible nonnegative matrix.  Its eigenvalue is simultaneously
identified with the coordinate unit-sphere supremum, the Euclidean unit-sphere
supremum, and Mathlib's nonzero-vector `iSup` Rayleigh quotient.
-/

namespace Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A [real symmetric irreducible finite matrix](hyp:A,hA_symm,hA_irred) has [a strictly positive unit eigenvector whose eigenvalue is simultaneously the coordinate-sphere, Euclidean-sphere, and nonzero-vector top Rayleigh value](goal). -/
theorem finite_positive_perron_eigenvector
    (A : Matrix ι ι ℝ) (hA_symm : A.IsSymm) (hA_irred : A.IsIrreducible) :
    ∃ (v : EVec ι) (ρ : ℝ),
      ‖v‖ = 1 ∧
      (∀ i, 0 < v i) ∧
      A.mulVec v = ρ • v ∧
      rayleighForm A v = ρ ∧
      ρ = sphereRayleighValue A ∧
      ρ = coordinateSphereRayleighValue A ∧
      ρ = iSupRayleighValue A := by
  obtain ⟨x, hx_norm, hx_eigen, hx_top⟩ :=
    exists_unit_eigenvector_sphereRayleighValue A hA_symm
  obtain ⟨habs_norm, habs_nonneg, habs_top, habs_eigen⟩ :=
    absVec_preserves_top_eigenvector A hA_symm hA_irred.nonneg
      hx_norm hx_eigen hx_top
  refine ⟨absVec x, sphereRayleighValue A, habs_norm, ?_, habs_eigen,
    habs_top, rfl, ?_, ?_⟩
  · exact IsIrreducible.unit_eigenvector_pos hA_irred
      habs_nonneg habs_norm habs_eigen
  · exact (coordinateSphereRayleighValue_eq_sphereRayleighValue A).symm
  · exact sphereRayleighValue_eq_iSupRayleighValue A

/-- A [symmetric finite matrix](hyp:A,hA_symm), [a nonempty finite coordinate set](hyp:s), [an irreducible restricted block](hyp:hA_irred), and [block closure from outside rows into that set](hyp:hclosed) ensure [that the block’s strictly positive unit Perron vector zero-extends to a global eigenvector](goal). -/
theorem finite_positive_perron_eigenvector_on_restriction
    (A : Matrix ι ι ℝ) (hA_symm : A.IsSymm) (s : Finset ι) [Nonempty s]
    (hA_irred : (restrictMatrix A s).IsIrreducible)
    (hclosed : ∀ i j, i ∉ s → j ∈ s → A i j = 0) :
    ∃ (v : EVec s) (ρ : ℝ),
      ‖v‖ = 1 ∧
      (∀ i, 0 < v i) ∧
      (restrictMatrix A s).mulVec v = ρ • v ∧
      A.mulVec (zeroExtendVec s v) = ρ • zeroExtendVec s v ∧
      ρ = sphereRayleighValue (restrictMatrix A s) ∧
      ρ = coordinateSphereRayleighValue (restrictMatrix A s) ∧
      ρ = iSupRayleighValue (restrictMatrix A s) := by
  obtain ⟨v, ρ, hv_norm, hv_pos, hv_eigen, _, hρ_sphere, hρ_coordinate, hρ_iSup⟩ :=
    finite_positive_perron_eigenvector (restrictMatrix A s)
      (restrictMatrix_isSymm hA_symm s) hA_irred
  refine ⟨v, ρ, hv_norm, hv_pos, hv_eigen, ?_, hρ_sphere, hρ_coordinate, hρ_iSup⟩
  exact zeroExtendVec_eigenvector_of_closed A s hclosed hv_eigen

end

end Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

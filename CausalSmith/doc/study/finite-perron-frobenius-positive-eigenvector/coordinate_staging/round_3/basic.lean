import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Finite Perron--Frobenius: Rayleigh-value interface

This file fixes the Euclidean-space conventions used by the finite positive
Perron eigenvector substrate.  It defines the quadratic form and three equivalent
presentations of its top Rayleigh value: a coordinate unit-sphere `sSup`, a
Euclidean unit-sphere `sSup`, and Mathlib's `iSup` of the Rayleigh quotient.
-/

open scoped BigOperators
open Metric Set

namespace Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Euclidean real vector [indexed by a finite coordinate type](hyp:ι), called [a finite real coordinate vector](goal), [is given by the Euclidean space on that coordinate type](step:1). -/
abbrev EVec (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

/-- The Euclidean vector obtained from [a finite real vector](hyp:x) by [taking the absolute value of every coordinate](goal) [is given coordinate by coordinate](step:1). -/
def absVec (x : EVec ι) : EVec ι :=
  WithLp.toLp 2 fun i => |x i|

/-- The quadratic form associated with [a finite real matrix](hyp:A) and [a Euclidean coordinate vector](hyp:x), called [its Rayleigh form](goal), [is given by the vector-matrix-vector quadratic sum](step:1). -/
def rayleighForm (A : Matrix ι ι ℝ) (x : EVec ι) : ℝ :=
  ∑ i, x i * (A.mulVec x) i

/-- The greatest quadratic Rayleigh-form value among [the Euclidean unit vectors for a finite real matrix](hyp:A), called [the Euclidean-sphere top Rayleigh value](goal), [is given by a supremum](step:1). -/
def sphereRayleighValue (A : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : EVec ι, ‖x‖ = 1 ∧ r = rayleighForm A x}

/-- The greatest quadratic Rayleigh-form value among [the coordinate vectors whose squared coordinates sum to one for a finite real matrix](hyp:A), called [the coordinate-sphere top Rayleigh value](goal), [is given by a supremum](step:1). -/
def coordinateSphereRayleighValue (A : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : ι → ℝ, (∑ i, x i ^ 2) = 1 ∧
    r = ∑ i, x i * (A.mulVec x) i}

/-- Mathlib's supremum Rayleigh quotient for [a finite real matrix](hyp:A), called [the nonzero-vector top Rayleigh value](goal), [is given by the matrix's Euclidean linear map](step:1). -/
def iSupRayleighValue (A : Matrix ι ι ℝ) : ℝ :=
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  ⨆ x : {x : EVec ι // x ≠ 0}, T.rayleighQuotient x

private theorem reApplyInnerSelf_toEuclideanLin_eq_rayleighForm
    (A : Matrix ι ι ℝ) (x : EVec ι) :
    (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x = rayleighForm A x := by
  simp [ContinuousLinearMap.reApplyInnerSelf_apply,
    EuclideanSpace.inner_eq_star_dotProduct, rayleighForm, dotProduct, Matrix.mulVec,
    Matrix.toLpLin_apply]

/-- With [a finite real matrix](hyp:A), [the coordinate and Euclidean unit-sphere top Rayleigh values agree](goal). -/
theorem coordinateSphereRayleighValue_eq_sphereRayleighValue
    (A : Matrix ι ι ℝ) :
    coordinateSphereRayleighValue A = sphereRayleighValue A := by
  unfold coordinateSphereRayleighValue sphereRayleighValue
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · have hs : ‖WithLp.toLp 2 x‖ ^ 2 = 1 ^ 2 := by
        simpa [EuclideanSpace.real_norm_sq_eq] using hx
      exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hs
    · rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun i => x i, ?_, rfl⟩
    rw [← EuclideanSpace.real_norm_sq_eq, hx]
    norm_num

/-- On a nonempty finite coordinate space, [a real matrix](hyp:A) has [its Euclidean unit-sphere top value equal to Mathlib's supremum Rayleigh quotient](goal). -/
theorem sphereRayleighValue_eq_iSupRayleighValue [Nonempty ι]
    (A : Matrix ι ι ℝ) :
    sphereRayleighValue A = iSupRayleighValue A := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  rw [iSupRayleighValue, show (Matrix.toEuclideanLin A).toContinuousLinearMap = T from rfl]
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere (by norm_num : (0 : ℝ) < 1)]
  unfold sphereRayleighValue
  rw [show {r : ℝ | ∃ x : EVec ι, ‖x‖ = 1 ∧ r = rayleighForm A x} =
      rayleighForm A '' sphere (0 : EVec ι) 1 by
    ext r
    simp [eq_comm]]
  rw [sSup_image']
  apply iSup_congr
  intro x
  simp only [ContinuousLinearMap.rayleighQuotient]
  rw [show ‖(x : EVec ι)‖ = 1 by simpa using x.property]
  simp [T, reApplyInnerSelf_toEuclideanLin_eq_rayleighForm]

/-- On a nonempty finite coordinate space, [a real matrix](hyp:A) has [its coordinate unit-sphere top value equal to Mathlib's supremum Rayleigh quotient](goal). -/
theorem coordinateSphereRayleighValue_eq_iSupRayleighValue [Nonempty ι]
    (A : Matrix ι ι ℝ) :
    coordinateSphereRayleighValue A = iSupRayleighValue A := by
  exact (coordinateSphereRayleighValue_eq_sphereRayleighValue A).trans
    (sphereRayleighValue_eq_iSupRayleighValue A)

/-- On a nonempty finite coordinate space, [a real symmetric matrix](hyp:A,hA) has [a unit vector attaining its Euclidean-sphere top Rayleigh value](goal). -/
theorem exists_unit_isMaxOn_rayleighForm [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∃ x : EVec ι, ‖x‖ = 1 ∧
      IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) x ∧
      rayleighForm A x = sphereRayleighValue A := by
  have hcompact : IsCompact (sphere (0 : EVec ι) 1) := isCompact_sphere _ _
  have hsphere : (sphere (0 : EVec ι) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hcontinuous : Continuous (rayleighForm A) := by
    unfold rayleighForm Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨x, hx, hmax⟩ :=
    hcompact.exists_isMaxOn hsphere hcontinuous.continuousOn
  refine ⟨x, by simpa using hx, hmax, ?_⟩
  symm
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨x, by simpa using hx, rfl⟩
  · rintro r ⟨y, hy, rfl⟩
    apply hmax
    simpa using hy

/-- On a nonempty finite coordinate space, [a real symmetric matrix](hyp:A,hA) has [a unit eigenvector at its Euclidean-sphere top Rayleigh value](goal). -/
theorem exists_unit_eigenvector_sphereRayleighValue [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∃ x : EVec ι, ‖x‖ = 1 ∧
      A.mulVec x = sphereRayleighValue A • x ∧
      rayleighForm A x = sphereRayleighValue A := by
  obtain ⟨x, hx, hmax, hval⟩ := exists_unit_isMaxOn_rayleighForm A hA
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  have hself : IsSelfAdjoint T := hsym.toSelfAdjoint.prop
  have hxne : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hmaxT : IsMaxOn T.reApplyInnerSelf (sphere (0 : EVec ι) ‖x‖) x := by
    intro y hy
    change T.reApplyInnerSelf y ≤ T.reApplyInnerSelf x
    rw [show T.reApplyInnerSelf y = rayleighForm A y by
        simpa [T] using reApplyInnerSelf_toEuclideanLin_eq_rayleighForm A y,
      show T.reApplyInnerSelf x = rayleighForm A x by
        simpa [T] using reApplyInnerSelf_toEuclideanLin_eq_rayleighForm A x]
    apply hmax
    simpa [hx] using hy
  have heig := hself.hasEigenvector_of_isMaxOn hxne hmaxT
  refine ⟨x, hx, ?_, hval⟩
  have htop : (⨆ y : {y : EVec ι // y ≠ 0}, T.rayleighQuotient y) =
      sphereRayleighValue A := by
    simpa [iSupRayleighValue, T] using
      (sphereRayleighValue_eq_iSupRayleighValue A).symm
  rw [htop] at heig
  exact congrArg WithLp.ofLp heig.apply_eq_smul

end

end Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

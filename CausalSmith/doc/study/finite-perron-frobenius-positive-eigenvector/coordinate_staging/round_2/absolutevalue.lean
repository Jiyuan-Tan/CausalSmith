import Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Basic

/-!
# Absolute values of Rayleigh maximizers

For an entrywise-nonnegative matrix, taking coordinatewise absolute values
preserves Euclidean norm and can only increase the quadratic form.  Consequently
it preserves unit-sphere maximality; for a symmetric matrix the resulting
nonnegative maximizer is again a top eigenvector.
-/

open scoped BigOperators
open Metric Set

namespace Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With [a Euclidean coordinate vector](hyp:x), [coordinatewise absolute value preserves its Euclidean norm](goal). -/
@[simp] theorem norm_absVec (x : EVec ι) : ‖absVec x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, absVec]

/-- With [a Euclidean coordinate vector](hyp:x) and [a coordinate](hyp:i), [the corresponding coordinatewise absolute value is nonnegative](goal). -/
theorem absVec_nonneg (x : EVec ι) (i : ι) : 0 ≤ absVec x i := by
  simp [absVec]

/-- An [entrywise nonnegative finite real matrix](hyp:A,hA) and [a Euclidean coordinate vector](hyp:x) satisfy [that taking coordinatewise absolute values cannot lower the Rayleigh form](goal). -/
theorem rayleighForm_le_absVec (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (x : EVec ι) :
    rayleighForm A x ≤ rayleighForm A (absVec x) := by
  unfold rayleighForm Matrix.mulVec dotProduct
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_left (le_abs_self (x i * x j)) (hA i j)
  change x i * (A i j * x j) ≤ |x i| * (A i j * |x j|)
  rw [abs_mul] at h
  nlinarith

/-- A [radius](hyp:r) and [a Euclidean coordinate vector on the sphere of that radius](hyp:x,hx) satisfy [that coordinatewise absolute value remains on the same sphere](goal). -/
theorem absVec_mem_sphere {r : ℝ} {x : EVec ι}
    (hx : x ∈ sphere (0 : EVec ι) r) :
    absVec x ∈ sphere (0 : EVec ι) r := by
  simpa [mem_sphere] using hx

/-- An [entrywise nonnegative finite real matrix](hyp:A,hA), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that taking coordinatewise absolute values preserves the Rayleigh-form value](goal). -/
theorem rayleighForm_absVec_eq_of_isMaxOn
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x : EVec ι} (hx : x ∈ sphere (0 : EVec ι) 1)
    (hmax : IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) x) :
    rayleighForm A (absVec x) = rayleighForm A x := by
  apply le_antisymm
  · exact hmax (absVec_mem_sphere hx)
  · exact rayleighForm_le_absVec A hA x

/-- An [entrywise nonnegative finite real matrix](hyp:A,hA), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that coordinatewise absolute value is another unit-sphere maximizer](goal). -/
theorem absVec_isMaxOn
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x : EVec ι} (hx : x ∈ sphere (0 : EVec ι) 1)
    (hmax : IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) x) :
    IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) (absVec x) := by
  intro y hy
  rw [rayleighForm_absVec_eq_of_isMaxOn A hA hx hmax]
  exact hmax hy

/-- On a nonempty finite coordinate space, an [entrywise nonnegative symmetric real matrix](hyp:A,hA_symm,hA_nonneg), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that the coordinatewise absolute vector is an eigenvector at the top Rayleigh value](goal). -/
theorem absVec_eigenvector_of_isMaxOn [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA_symm : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : EVec ι} (hx : x ∈ sphere (0 : EVec ι) 1)
    (hmax : IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) x) :
    A.mulVec (absVec x) = sphereRayleighValue A • absVec x := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA_symm
  have hself : IsSelfAdjoint T := hsym.toSelfAdjoint.prop
  have habs_norm : ‖absVec x‖ = 1 := by
    rw [norm_absVec]
    simpa [mem_sphere] using hx
  have habs_ne : absVec x ≠ 0 := by
    intro hzero
    simp [hzero] at habs_norm
  have habs_max := absVec_isMaxOn A hA_nonneg hx hmax
  have hmaxT : IsMaxOn T.reApplyInnerSelf
      (sphere (0 : EVec ι) ‖absVec x‖) (absVec x) := by
    intro y hy
    change T.reApplyInnerSelf y ≤ T.reApplyInnerSelf (absVec x)
    change rayleighForm A y ≤ rayleighForm A (absVec x)
    apply habs_max
    simpa [habs_norm] using hy
  have heig := hself.hasEigenvector_of_isMaxOn habs_ne hmaxT
  have htop : (⨆ y : {y : EVec ι // y ≠ 0}, T.rayleighQuotient y) =
      sphereRayleighValue A := by
    simpa [iSupRayleighValue, T] using
      (sphereRayleighValue_eq_iSupRayleighValue A).symm
  rw [htop] at heig
  exact congrArg WithLp.ofLp heig.apply_eq_smul

/-- On a nonempty finite coordinate space, an [entrywise nonnegative symmetric real matrix](hyp:A,hA_symm,hA_nonneg) and [a normalized top eigenvector](hyp:x,hx_norm,hx_eigen,hx_top) ensure [that coordinatewise absolute value is a normalized nonnegative top eigenvector with the same top value](goal). -/
theorem absVec_preserves_top_eigenvector [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA_symm : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : EVec ι} (hx_norm : ‖x‖ = 1)
    (hx_eigen : A.mulVec x = sphereRayleighValue A • x)
    (hx_top : rayleighForm A x = sphereRayleighValue A) :
    ‖absVec x‖ = 1 ∧
      (∀ i, 0 ≤ absVec x i) ∧
      rayleighForm A (absVec x) = sphereRayleighValue A ∧
      A.mulVec (absVec x) = sphereRayleighValue A • absVec x := by
  have hx : x ∈ sphere (0 : EVec ι) 1 := by
    simpa [mem_sphere] using hx_norm
  obtain ⟨y, hy_norm, hy_max, hy_value⟩ := exists_unit_isMaxOn_rayleighForm A hA_symm
  have hx_max : IsMaxOn (rayleighForm A) (sphere (0 : EVec ι) 1) x := by
    intro z hz
    calc
      rayleighForm A z ≤ rayleighForm A y := hy_max hz
      _ = sphereRayleighValue A := hy_value
      _ = rayleighForm A x := hx_top.symm
  refine ⟨norm_absVec x |>.trans hx_norm, absVec_nonneg x, ?_, ?_⟩
  · exact (rayleighForm_absVec_eq_of_isMaxOn A hA_nonneg hx hx_max).trans hx_top
  · exact absVec_eigenvector_of_isMaxOn A hA_symm hA_nonneg hx hx_max

end

end Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

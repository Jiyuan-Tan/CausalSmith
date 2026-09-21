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


/-!
# Positivity propagation for irreducible matrices

This file isolates the graph-theoretic step of Perron--Frobenius: a nonzero,
coordinatewise-nonnegative eigenvector of an irreducible nonnegative matrix has
no zero coordinate.  No symmetry assumption is needed for this propagation.
-/

open scoped BigOperators

namespace Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An [entrywise nonnegative matrix](hyp:A,hA_nonneg), [a nonnegative eigenvector](hyp:x,hx_nonneg,hx_eigen), [a row coordinate where it vanishes](hyp:i,hxi), and [a strictly positive matrix entry from that row](hyp:j,hAij) ensure [that the eigenvector also vanishes at the entry’s target coordinate](goal). -/
theorem zero_coordinate_propagates_across_positive_entry
    (A : Matrix ι ι ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : EVec ι} (hx_nonneg : ∀ i, 0 ≤ x i) {ρ : ℝ}
    (hx_eigen : A.mulVec x = ρ • x) {i j : ι}
    (hxi : x i = 0) (hAij : 0 < A i j) :
    x j = 0 := by
  have hsum : ∑ k, A i k * x k = 0 := by
    have hi := congrFun hx_eigen i
    simpa [Matrix.mulVec, dotProduct, hxi] using hi
  have hterm : A i j * x j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hA_nonneg i k) (hx_nonneg k))).mp hsum j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hAij)

/-- An [irreducible finite matrix](hyp:hA) and [a nonnegative nonzero eigenvector](hyp:x,hx_nonneg,hx_ne,hx_eigen) ensure [that every coordinate is strictly positive](goal). -/
theorem IsIrreducible.eigenvector_pos
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible)
    {x : EVec ι} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) {ρ : ℝ}
    (hx_eigen : A.mulVec x = ρ • x) :
    ∀ i, 0 < x i := by
  have hpath : ∀ {i j : ι},
      @Quiver.Path ι (Matrix.toQuiver A) i j → x i = 0 → x j = 0 := by
    intro i j p
    induction p with
    | nil => exact id
    | @cons j k p e ih =>
        intro hxi
        exact zero_coordinate_propagates_across_positive_entry A hA.nonneg hx_nonneg hx_eigen
          (ih hxi) e.down
  intro i
  by_contra hxi_pos
  have hxi : x i = 0 := le_antisymm (le_of_not_gt hxi_pos) (hx_nonneg i)
  apply hx_ne
  ext j
  obtain ⟨p, _⟩ := hA.connected i j
  exact hpath p hxi

/-- An [irreducible finite matrix](hyp:hA) and [a normalized nonnegative eigenvector](hyp:x,hx_nonneg,hx_norm,hx_eigen) ensure [that every coordinate is strictly positive](goal). -/
theorem IsIrreducible.unit_eigenvector_pos
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible)
    {x : EVec ι} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_norm : ‖x‖ = 1) {ρ : ℝ}
    (hx_eigen : A.mulVec x = ρ • x) :
    ∀ i, 0 < x i := by
  apply Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.IsIrreducible.eigenvector_pos
    hA hx_nonneg _ hx_eigen
  intro hx
  simp [hx] at hx_norm

end

end Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector


/-!
# Restriction and zero extension

This file supplies the coordinate bridges used for finite connected components.
It defines principal-submatrix restriction and zero extension, proves the exact
`mulVec` identities they satisfy, and relates the corresponding top Rayleigh
values.  Cross-boundary hypotheses are stated explicitly whenever an identity
for the original matrix would otherwise be false.
-/

open scoped BigOperators

namespace Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The principal submatrix of [a finite real matrix](hyp:A) on [a finite set of coordinates](hyp:s), called [its restricted matrix](goal), [is given by selecting those rows and columns](step:1). -/
def restrictMatrix (A : Matrix ι ι ℝ) (s : Finset ι) : Matrix s s ℝ :=
  A.submatrix Subtype.val Subtype.val

/-- The Euclidean vector obtained by restricting [a finite real vector](hyp:x) to [a finite coordinate set](hyp:s), called [its restricted vector](goal), [is given by retaining those coordinates](step:1). -/
def restrictVec (s : Finset ι) (x : EVec ι) : EVec s :=
  WithLp.toLp 2 fun i => x i.1

/-- The Euclidean vector obtained by extending [a vector on a finite coordinate subtype](hyp:x) by zero outside [that finite coordinate set](hyp:s), called [its zero extension](goal), [is given coordinate by coordinate](step:1). -/
def zeroExtendVec (s : Finset ι) (x : EVec s) : EVec ι :=
  WithLp.toLp 2 fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 0

/-- The matrix obtained by extending [a matrix on a finite coordinate subtype](hyp:B) by zero outside [that coordinate set](hyp:s), called [its zero extension](goal), [is given entry by entry](step:1). -/
def zeroExtendMatrix (s : Finset ι) (B : Matrix s s ℝ) : Matrix ι ι ℝ :=
  fun i j => if hi : i ∈ s then
    if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that restricting its zero extension recovers the original subtype vector](goal). -/
@[simp] theorem restrictVec_zeroExtendVec (s : Finset ι) (x : EVec s) :
    restrictVec s (zeroExtendVec s x) = x := by
  ext i
  simp [restrictVec, zeroExtendVec]

/-- A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that zero extension preserves Euclidean norm](goal). -/
@[simp] theorem norm_zeroExtendVec (s : Finset ι) (x : EVec s) :
    ‖zeroExtendVec s x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : ι, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) ^ 2) =
    ∑ i : s, (x i) ^ 2
  calc
    _ = ∑ i ∈ s, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, (x i) ^ 2 := by
      rw [← Finset.sum_coe_sort]
      simp

/-- A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that applying the zero-extended matrix to the zero-extended vector equals the zero extension of the subtype action](goal). -/
theorem zeroExtendMatrix_mulVec_zeroExtendVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec s) :
    (zeroExtendMatrix s B).mulVec (zeroExtendVec s x) =
      zeroExtendVec s (WithLp.toLp 2 (B.mulVec x)) := by
  ext i
  by_cases hi : i ∈ s
  · simp only [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct,
      hi, dite_true]
    calc
      _ = ∑ j ∈ s, (if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0) *
          (if hj : j ∈ s then x ⟨j, hj⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, B ⟨i, hi⟩ j * x j := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct, hi]

/-- A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that zero extension preserves their Rayleigh form](goal). -/
theorem rayleighForm_zeroExtendMatrix_zeroExtendVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec s) :
    rayleighForm (zeroExtendMatrix s B) (zeroExtendVec s x) =
      rayleighForm B x := by
  unfold rayleighForm
  rw [zeroExtendMatrix_mulVec_zeroExtendVec]
  change (∑ i : ι, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) *
      (if hi : i ∈ s then (B.mulVec x) ⟨i, hi⟩ else 0)) =
    ∑ i : s, x i * (B.mulVec x) i
  calc
    _ = ∑ i ∈ s, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) *
        (if hi : i ∈ s then (B.mulVec x) ⟨i, hi⟩ else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, x i * (B.mulVec x) i := by
      rw [← Finset.sum_coe_sort]
      simp

private theorem norm_restrictVec_le (s : Finset ι) (x : EVec ι) :
    ‖restrictVec s x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : s, (x i.1) ^ 2) ≤ ∑ i : ι, (x i) ^ 2
  calc
    _ = ∑ i ∈ s, (x i) ^ 2 := Finset.sum_coe_sort s (fun i => (x i) ^ 2)
    _ ≤ ∑ i : ι, (x i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro i _ _
      exact sq_nonneg (x i)

private theorem rayleighForm_smul (A : Matrix ι ι ℝ) (c : ℝ) (x : EVec ι) :
    rayleighForm A (c • x) = c ^ 2 * rayleighForm A x := by
  simp [rayleighForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
  ring_nf

private theorem zeroExtendMatrix_mulVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec ι) :
    (zeroExtendMatrix s B).mulVec x =
      zeroExtendVec s (WithLp.toLp 2 (B.mulVec (restrictVec s x))) := by
  ext i
  by_cases hi : i ∈ s
  · simp only [zeroExtendMatrix, zeroExtendVec, restrictVec, Matrix.mulVec,
      dotProduct, hi, dite_true]
    calc
      _ = ∑ j ∈ s, (if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0) * x j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, B ⟨i, hi⟩ j * x j.1 := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct, hi]

private theorem rayleighForm_zeroExtendMatrix
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec ι) :
    rayleighForm (zeroExtendMatrix s B) x =
      rayleighForm B (restrictVec s x) := by
  unfold rayleighForm
  rw [zeroExtendMatrix_mulVec]
  change (∑ i : ι, x i *
      (if hi : i ∈ s then (B.mulVec (restrictVec s x)) ⟨i, hi⟩ else 0)) =
    ∑ i : s, x i.1 * (B.mulVec (restrictVec s x)) i
  calc
    _ = ∑ i ∈ s, x i *
        (if hi : i ∈ s then (B.mulVec (restrictVec s x)) ⟨i, hi⟩ else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, x i.1 * (B.mulVec (restrictVec s x)) i := by
      rw [← Finset.sum_coe_sort]
      simp

private theorem rayleighForm_le_sphereRayleighValue [Nonempty ι]
    (A : Matrix ι ι ℝ) (x : EVec ι) (hx : ‖x‖ = 1) :
    rayleighForm A x ≤ sphereRayleighValue A := by
  unfold sphereRayleighValue
  apply le_csSup
  · rw [show {r : ℝ | ∃ y : EVec ι, ‖y‖ = 1 ∧ r = rayleighForm A y} =
        rayleighForm A '' Metric.sphere (0 : EVec ι) 1 by
      ext r
      simp [eq_comm]]
    apply (isCompact_sphere (0 : EVec ι) 1).bddAbove_image
    unfold rayleighForm Matrix.mulVec dotProduct
    fun_prop
  · exact ⟨x, hx, rfl⟩

private theorem sphereRayleighValue_nonneg [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ sphereRayleighValue A := by
  let i : ι := Classical.choice inferInstance
  let e : EVec ι := EuclideanSpace.single i 1
  have he_norm : ‖e‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [e]
  have he_form : rayleighForm A e = A i i := by
    simp [rayleighForm, Matrix.mulVec, dotProduct, e]
  calc
    0 ≤ A i i := hA i i
    _ = rayleighForm A e := he_form.symm
    _ ≤ sphereRayleighValue A := rayleighForm_le_sphereRayleighValue A e he_norm

/-- On a nonempty finite coordinate space, [a nonempty finite coordinate set](hyp:s) and [an entrywise nonnegative subtype matrix](hyp:B,hB) satisfy [that zero extension preserves its top Rayleigh value](goal). -/
theorem sphereRayleighValue_zeroExtendMatrix [Nonempty ι]
    (s : Finset ι) [Nonempty s] (B : Matrix s s ℝ)
    (hB : ∀ i j, 0 ≤ B i j) :
    sphereRayleighValue (zeroExtendMatrix s B) = sphereRayleighValue B := by
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec ι) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (by norm_num)
      exact ⟨rayleighForm (zeroExtendMatrix s B) x, x, by simpa using hx, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      rw [rayleighForm_zeroExtendMatrix]
      let y := restrictVec s x
      have hy_norm : ‖y‖ ≤ 1 := (norm_restrictVec_le s x).trans_eq hx
      by_cases hy : y = 0
      · change rayleighForm B y ≤ sphereRayleighValue B
        simpa [hy, rayleighForm, Matrix.mulVec, dotProduct] using
          sphereRayleighValue_nonneg B hB
      · have hy_norm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
        let u : EVec s := ‖y‖⁻¹ • y
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_smul, hy_norm_ne]
        have hu_le : rayleighForm B u ≤ sphereRayleighValue B :=
          rayleighForm_le_sphereRayleighValue B u hu_norm
        have htop : 0 ≤ sphereRayleighValue B :=
          sphereRayleighValue_nonneg B hB
        have hy_sq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
        have hy_eq : ‖y‖ • u = y := by
          simp [u, smul_smul, hy_norm_ne]
        calc
          rayleighForm B y = rayleighForm B (‖y‖ • u) :=
            congrArg (rayleighForm B) hy_eq.symm
          _ = ‖y‖ ^ 2 * rayleighForm B u := rayleighForm_smul B ‖y‖ u
          _ ≤ ‖y‖ ^ 2 * sphereRayleighValue B :=
            mul_le_mul_of_nonneg_left hu_le (sq_nonneg _)
          _ ≤ 1 * sphereRayleighValue B :=
            mul_le_mul_of_nonneg_right hy_sq htop
          _ = sphereRayleighValue B := one_mul _
  · apply csSup_le
    · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec s) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (by norm_num)
      exact ⟨rayleighForm B x, x, by simpa using hx, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      calc
        rayleighForm B x =
            rayleighForm (zeroExtendMatrix s B) (zeroExtendVec s x) :=
          (rayleighForm_zeroExtendMatrix_zeroExtendVec s B x).symm
        _ ≤ sphereRayleighValue (zeroExtendMatrix s B) :=
          rayleighForm_le_sphereRayleighValue _ _ (by simpa using hx)

/-- A [symmetric finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains symmetric](goal). -/
theorem restrictMatrix_isSymm {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (s : Finset ι) :
    (restrictMatrix A s).IsSymm := by
  exact hA.submatrix Subtype.val

/-- An [entrywise nonnegative finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains entrywise nonnegative](goal). -/
theorem restrictMatrix_nonneg {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (s : Finset ι) :
    ∀ i j, 0 ≤ restrictMatrix A s i j := by
  intro i j
  exact hA i.1 j.1

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector](hyp:x) that [vanishes outside the set](hyp:hx) ensure [that restriction commutes with applying the matrix](goal). -/
theorem restrictMatrix_mulVec_restrictVec_of_zero_off
    (A : Matrix ι ι ℝ) (s : Finset ι) (x : EVec ι)
    (hx : ∀ i, i ∉ s → x i = 0) :
    (restrictMatrix A s).mulVec (restrictVec s x) =
      restrictVec s (WithLp.toLp 2 (A.mulVec x)) := by
  ext i
  change (∑ j : s, A i.1 j.1 * x j.1) = ∑ j : ι, A i.1 j * x j
  calc
    _ = ∑ j ∈ s, A i.1 j * x j := by
      simpa using Finset.sum_coe_sort s (fun j => A i.1 j * x j)
    _ = ∑ j : ι, A i.1 j * x j := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      simp [hx j hj]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [block closure from outside rows into the set](hyp:hclosed) ensure [that applying the original matrix to a zero extension equals the zero extension of the restricted action](goal). -/
theorem mulVec_zeroExtendVec_of_closed
    (A : Matrix ι ι ℝ) (s : Finset ι)
    (hclosed : ∀ i j, i ∉ s → j ∈ s → A i j = 0)
    (x : EVec s) :
    A.mulVec (zeroExtendVec s x) =
      zeroExtendVec s (WithLp.toLp 2 ((restrictMatrix A s).mulVec x)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, zeroExtendVec, restrictMatrix,
    Matrix.submatrix_apply]
  by_cases hi : i ∈ s
  · simp only [hi, dite_true]
    calc
      _ = ∑ j ∈ s, A i j * (if hj : j ∈ s then x ⟨j, hj⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, A i j.1 * x j := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp only [hi, dite_false]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · simp [hj, hclosed i j hi hj]
    · simp [hj]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), [block closure from outside rows into the set](hyp:hclosed), and [a restricted eigen-equation](hyp:x,hx) ensure [that zero extension satisfies the corresponding global eigen-equation](goal). -/
theorem zeroExtendVec_eigenvector_of_closed
    (A : Matrix ι ι ℝ) (s : Finset ι)
    (hclosed : ∀ i j, i ∉ s → j ∈ s → A i j = 0)
    {x : EVec s} {ρ : ℝ}
    (hx : (restrictMatrix A s).mulVec x = ρ • x) :
    A.mulVec (zeroExtendVec s x) = ρ • zeroExtendVec s x := by
  rw [mulVec_zeroExtendVec_of_closed A s hclosed, hx]
  ext i
  by_cases hi : i ∈ s <;> simp [zeroExtendVec, hi]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector that vanishes outside that set](hyp:x,hx) ensure [that restriction preserves its Rayleigh form](goal). -/
theorem rayleighForm_restrictVec_of_zero_off
    (A : Matrix ι ι ℝ) (s : Finset ι) (x : EVec ι)
    (hx : ∀ i, i ∉ s → x i = 0) :
    rayleighForm (restrictMatrix A s) (restrictVec s x) =
      rayleighForm A x := by
  unfold rayleighForm
  rw [restrictMatrix_mulVec_restrictVec_of_zero_off A s x hx]
  change (∑ i : s, x i.1 * (A.mulVec x) i.1) =
    ∑ i : ι, x i * (A.mulVec x) i
  calc
    _ = ∑ i ∈ s, x i * (A.mulVec x) i := by
      simpa using Finset.sum_coe_sort s (fun i => x i * (A.mulVec x) i)
    _ = ∑ i : ι, x i * (A.mulVec x) i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hx i hi]

/-- On a nonempty finite coordinate space, [a finite matrix](hyp:A) and [a nonempty finite coordinate set](hyp:s) satisfy [that the restricted top Rayleigh value is at most the global top Rayleigh value](goal). -/
theorem sphereRayleighValue_restrictMatrix_le [Nonempty ι]
    (A : Matrix ι ι ℝ) (s : Finset ι) [Nonempty s] :
    sphereRayleighValue (restrictMatrix A s) ≤ sphereRayleighValue A := by
  apply csSup_le
  · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec s) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr (by norm_num)
    exact ⟨rayleighForm (restrictMatrix A s) x, x, by simpa using hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    have hx_off : ∀ i, i ∉ s → zeroExtendVec s x i = 0 := by
      intro i hi
      simp [zeroExtendVec, hi]
    have hform :=
      rayleighForm_restrictVec_of_zero_off A s (zeroExtendVec s x) hx_off
    calc
      rayleighForm (restrictMatrix A s) x =
          rayleighForm A (zeroExtendVec s x) := by simpa using hform
      _ ≤ sphereRayleighValue A :=
        rayleighForm_le_sphereRayleighValue A (zeroExtendVec s x) (by simpa using hx)

/-- On a nonempty finite coordinate space, [a finite matrix](hyp:A), [a nonempty finite coordinate set](hyp:s), and [a global unit maximizer supported on that set](hyp:x,hx_norm,hx_support,hx_top) ensure [that the restricted and global top Rayleigh values agree](goal). -/
theorem sphereRayleighValue_restrictMatrix_eq_of_supported_maximizer
    [Nonempty ι] (A : Matrix ι ι ℝ) (s : Finset ι) [Nonempty s]
    {x : EVec ι} (hx_norm : ‖x‖ = 1)
    (hx_support : ∀ i, i ∉ s → x i = 0)
    (hx_top : rayleighForm A x = sphereRayleighValue A) :
    sphereRayleighValue (restrictMatrix A s) = sphereRayleighValue A := by
  apply le_antisymm
  · exact sphereRayleighValue_restrictMatrix_le A s
  · have hzeroExtend : zeroExtendVec s (restrictVec s x) = x := by
      ext i
      by_cases hi : i ∈ s
      · simp [zeroExtendVec, restrictVec, hi]
      · simp [zeroExtendVec, hi, hx_support i hi]
    have hrestrict_norm : ‖restrictVec s x‖ = 1 := by
      rw [← norm_zeroExtendVec s (restrictVec s x), hzeroExtend, hx_norm]
    calc
      sphereRayleighValue A = rayleighForm A x := hx_top.symm
      _ = rayleighForm (restrictMatrix A s) (restrictVec s x) :=
        (rayleighForm_restrictVec_of_zero_off A s x hx_support).symm
      _ ≤ sphereRayleighValue (restrictMatrix A s) :=
        rayleighForm_le_sphereRayleighValue _ _ hrestrict_norm

end

end Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector


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

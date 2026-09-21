import Causalean.Mathlib.MeasureTheory.PolynomialZeroLocus
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rational maps and algebraic-locus compilers

This module represents finite-coordinate real rational maps by numerator and denominator
polynomials.  It clears coordinatewise equality, compiles finite conjunctions by sums of squares
and finite unions by products, and supplies polynomial-matrix and adjugate/determinant inverse
specializations.
-/

open Set
open scoped BigOperators Matrix

namespace Causalean.Mathlib.AlgebraicGeometry

variable {S T U B : Type*}

/-- A finite-coordinate real rational map stores one numerator and denominator multivariate
polynomial for each output coordinate. -/
structure RationalMap (S T : Type*) where
  num : T → MvPolynomial S ℝ
  den : T → MvPolynomial S ℝ

namespace RationalMap

/-- Evaluating a rational map substitutes the source coordinates into each numerator and
denominator and divides coordinatewise. -/
noncomputable def eval (f : RationalMap S T) (x : S → ℝ) : T → ℝ :=
  fun t => MvPolynomial.eval x (f.num t) / MvPolynomial.eval x (f.den t)

/-- A rational map is defined on a domain when every coordinate denominator is nonzero at every
point of that domain. -/
def DefinedOn (f : RationalMap S T) (D : Set (S → ℝ)) : Prop :=
  ∀ x ∈ D, ∀ t, MvPolynomial.eval x (f.den t) ≠ 0

/-- A polynomial coordinate map is viewed as a rational map with denominator one in every
coordinate. -/
noncomputable def ofPolynomial (p : T → MvPolynomial S ℝ) : RationalMap S T where
  num := p
  den := fun _ => 1

/-- For a [polynomial coordinate map](hyp:p) and [source assignment](hyp:x), the
[denominator-one rational representation has ordinary polynomial evaluation](goal). -/
theorem eval_ofPolynomial (p : T → MvPolynomial S ℝ) (x : S → ℝ) :
    (ofPolynomial p).eval x = fun t => MvPolynomial.eval x (p t) := by
  funext t
  simp [eval, ofPolynomial]

/-- The cleared numerator for equality of one coordinate of two rational maps is the cross-product
of their numerators and denominators. -/
noncomputable def equalityPolynomial (f g : RationalMap S T) (t : T) : MvPolynomial S ℝ :=
  f.num t * g.den t - g.num t * f.den t

/-- Given [two rational maps](hyp:f,g), [a source assignment](hyp:x), [an output coordinate](hyp:t),
and [nonzero first and second denominators](hyp:hf,hg), the [rational values agree exactly when
the cleared equality polynomial vanishes](goal). -/
theorem eval_eq_iff_equalityPolynomial_eq_zero (f g : RationalMap S T)
    (x : S → ℝ) (t : T)
    (hf : MvPolynomial.eval x (f.den t) ≠ 0)
    (hg : MvPolynomial.eval x (g.den t) ≠ 0) :
    f.eval x t = g.eval x t ↔
      MvPolynomial.eval x (equalityPolynomial f g t) = 0 := by
  simp only [eval, equalityPolynomial, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    sub_eq_zero]
  exact div_eq_div_iff hf hg

end RationalMap

/-- The conjunction polynomial of finitely many real polynomials is their sum of squares. -/
noncomputable def conjunctionPolynomial [Fintype T]
    (p : T → MvPolynomial S ℝ) : MvPolynomial S ℝ :=
  ∑ t, (p t) ^ 2

/-- For a [finite polynomial family](hyp:p) and [source assignment](hyp:x), the [conjunction
polynomial vanishes exactly when every constituent polynomial vanishes](goal). -/
theorem eval_conjunctionPolynomial_eq_zero_iff [Fintype T]
    (p : T → MvPolynomial S ℝ) (x : S → ℝ) :
    MvPolynomial.eval x (conjunctionPolynomial p) = 0 ↔
      ∀ t, MvPolynomial.eval x (p t) = 0 := by
  simp only [conjunctionPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_pow]
  constructor
  · intro h t
    have ht : (MvPolynomial.eval x (p t)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg
        (MvPolynomial.eval x (p i)))).mp h t (Finset.mem_univ t)
    exact sq_eq_zero_iff.mp ht
  · intro h
    apply Finset.sum_eq_zero
    intro t _
    simp [h t]

/-- Given a [finite polynomial family](hyp:p), [source assignment](hyp:x), [coordinate](hyp:t),
and [a nonzero value at that coordinate](hyp:h), the [conjunction polynomial is nonzero](goal). -/
theorem conjunctionPolynomial_ne_zero_of_witness [Fintype T]
    (p : T → MvPolynomial S ℝ) (x : S → ℝ) (t : T)
    (h : MvPolynomial.eval x (p t) ≠ 0) :
    conjunctionPolynomial p ≠ 0 := by
  intro hp
  have hz : MvPolynomial.eval x (conjunctionPolynomial p) = 0 := by
    rw [hp]
    simp
  exact h ((eval_conjunctionPolynomial_eq_zero_iff p x).mp hz t)

/-- The union-of-conjunctions polynomial multiplies the sum-of-squares certificate for every
branch. -/
noncomputable def unionConjunctionPolynomial [Fintype B] [Fintype T]
    (p : B → T → MvPolynomial S ℝ) : MvPolynomial S ℝ :=
  ∏ b, conjunctionPolynomial (p b)

/-- For a [finite family of finite polynomial systems](hyp:p) and [source assignment](hyp:x), the
[union certificate vanishes exactly when one branch vanishes coordinatewise](goal). -/
theorem eval_unionConjunctionPolynomial_eq_zero_iff [Fintype B] [Fintype T]
    (p : B → T → MvPolynomial S ℝ) (x : S → ℝ) :
    MvPolynomial.eval x (unionConjunctionPolynomial p) = 0 ↔
      ∃ b, ∀ t, MvPolynomial.eval x (p b t) = 0 := by
  classical
  simp only [unionConjunctionPolynomial, MvPolynomial.eval_prod,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro b
  exact eval_conjunctionPolynomial_eq_zero_iff (p b) x

/-- Given a [finite polynomial-system family](hyp:p), [branchwise witness assignments](hyp:witness),
[branchwise coordinates](hyp:coordinate), and [nonzero witness values](hyp:h), the [union
certificate is nonzero](goal). -/
theorem unionConjunctionPolynomial_ne_zero_of_witnesses [Fintype B] [Fintype T]
    (p : B → T → MvPolynomial S ℝ)
    (witness : B → S → ℝ) (coordinate : B → T)
    (h : ∀ b, MvPolynomial.eval (witness b) (p b (coordinate b)) ≠ 0) :
    unionConjunctionPolynomial p ≠ 0 := by
  apply Causalean.Mathlib.MeasureTheory.mvPolynomial_fintype_prod_ne_zero
  intro b
  exact conjunctionPolynomial_ne_zero_of_witness
    (p b) (witness b) (coordinate b) (h b)

/-- Given two finite-coordinate rational maps [f](hyp:f) and [g](hyp:g) on a common
[domain](hyp:D) where [the denominators of the first map do not vanish](hyp:hf) and
[the denominators of the second map do not vanish](hyp:hg), the [whole-output equality condition is
one real polynomial zero locus](goal). -/
theorem rationalMap_eq_locus [Fintype T]
    (f g : RationalMap S T) (D : Set (S → ℝ))
    (hf : f.DefinedOn D) (hg : g.DefinedOn D) :
    {x | x ∈ D ∧ f.eval x = g.eval x} =
      D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus
        (conjunctionPolynomial (RationalMap.equalityPolynomial f g)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
    Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus]
  apply and_congr_right
  intro hx
  rw [eval_conjunctionPolynomial_eq_zero_iff]
  constructor
  · intro h t
    exact (RationalMap.eval_eq_iff_equalityPolynomial_eq_zero f g x t
      (hf x hx t) (hg x hx t)).mp (congrFun h t)
  · intro h
    funext t
    exact (RationalMap.eval_eq_iff_equalityPolynomial_eq_zero f g x t
      (hf x hx t) (hg x hx t)).mpr (h t)

/-- Given [finite families of rational maps](hyp:f,g) on a [common domain](hyp:D), with [all first
and second denominators nonvanishing](hyp:hf,hg), the [union of their equality conditions is one
polynomial zero locus](goal). -/
theorem rationalMap_eq_union_locus [Fintype B] [Fintype T]
    (f g : B → RationalMap S T) (D : Set (S → ℝ))
    (hf : ∀ b, (f b).DefinedOn D) (hg : ∀ b, (g b).DefinedOn D) :
    {x | x ∈ D ∧ ∃ b, (f b).eval x = (g b).eval x} =
      D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus
        (unionConjunctionPolynomial
          (fun b => RationalMap.equalityPolynomial (f b) (g b))) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
    Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus]
  apply and_congr_right
  intro hx
  rw [eval_unionConjunctionPolynomial_eq_zero_iff]
  apply exists_congr
  intro b
  constructor
  · intro h t
    exact (RationalMap.eval_eq_iff_equalityPolynomial_eq_zero (f b) (g b) x t
      (hf b x hx t) (hg b x hx t)).mp (congrFun h t)
  · intro h
    funext t
    exact (RationalMap.eval_eq_iff_equalityPolynomial_eq_zero (f b) (g b) x t
      (hf b x hx t) (hg b x hx t)).mpr (h t)

/-- A rational matrix map is a rational map whose output coordinates are row-column pairs. -/
abbrev RationalMatrixMap (S T U : Type*) := RationalMap S (T × U)

/-- Evaluating a rational matrix map and reshaping its pair-indexed output gives an ordinary
matrix-valued function. -/
noncomputable def RationalMatrixMap.evalMatrix (f : RationalMatrixMap S T U)
    (x : S → ℝ) : Matrix T U ℝ :=
  Matrix.of fun i j => f.eval x (i, j)

/-- Evaluating a matrix of multivariate polynomials substitutes the source point in every matrix
entry. -/
noncomputable def evalPolynomialMatrix (A : Matrix T U (MvPolynomial S ℝ))
    (x : S → ℝ) : Matrix T U ℝ :=
  A.map (MvPolynomial.eval x)

/-- A polynomial matrix is represented as a rational matrix map with denominator one entrywise. -/
noncomputable def polynomialMatrixRationalMap
    (A : Matrix T U (MvPolynomial S ℝ)) : RationalMatrixMap S T U :=
  RationalMap.ofPolynomial (fun ij => A ij.1 ij.2)

/-- For a [polynomial matrix](hyp:A) and [source assignment](hyp:x), the [rational-matrix
representation agrees with entrywise polynomial evaluation](goal). -/
theorem polynomialMatrixRationalMap_eval
    (A : Matrix T U (MvPolynomial S ℝ)) (x : S → ℝ) :
    (polynomialMatrixRationalMap A).evalMatrix x = evalPolynomialMatrix A x := by
  ext i j
  simp [RationalMatrixMap.evalMatrix, polynomialMatrixRationalMap,
    RationalMap.eval_ofPolynomial, evalPolynomialMatrix]

/-- The adjugate-over-determinant representation is the rational matrix map associated with the
inverse of a square polynomial matrix. -/
noncomputable def polynomialMatrixInverseRationalMap [Fintype T] [DecidableEq T]
    (A : Matrix T T (MvPolynomial S ℝ)) : RationalMatrixMap S T T where
  num := fun ij => A.adjugate ij.1 ij.2
  den := fun _ => A.det

/-- Given a [square polynomial matrix](hyp:A), [source assignment](hyp:x), and [nonzero evaluated
determinant](hyp:hdet), the [adjugate-over-determinant map evaluates to the matrix inverse](goal). -/
theorem polynomialMatrixInverseRationalMap_eval [Fintype T] [DecidableEq T]
    (A : Matrix T T (MvPolynomial S ℝ)) (x : S → ℝ)
    (hdet : MvPolynomial.eval x A.det ≠ 0) :
    (polynomialMatrixInverseRationalMap A).evalMatrix x =
      (evalPolynomialMatrix A x)⁻¹ := by
  rw [Matrix.inv_def]
  ext i j
  change MvPolynomial.eval x (A.adjugate i j) / MvPolynomial.eval x A.det =
    (Ring.inverse (A.map (MvPolynomial.eval x)).det •
      (A.map (MvPolynomial.eval x)).adjugate) i j
  rw [show (A.map (MvPolynomial.eval x)).det = MvPolynomial.eval x A.det from
      (RingHom.map_det (MvPolynomial.eval x) A).symm,
    show (A.map (MvPolynomial.eval x)).adjugate =
        A.adjugate.map (MvPolynomial.eval x) from
      (RingHom.map_adjugate (MvPolynomial.eval x) A).symm]
  by_cases hd : MvPolynomial.eval x A.det = 0
  · exact (hdet hd).elim
  · simp [Ring.inverse_eq_inv, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

/-- Given a [square polynomial matrix](hyp:A), [domain](hyp:D), and [a nowhere-vanishing evaluated
determinant](hyp:hdet), the [inverse representation is defined on the domain](goal). -/
theorem polynomialMatrixInverseRationalMap_definedOn [Fintype T] [DecidableEq T]
    (A : Matrix T T (MvPolynomial S ℝ)) (D : Set (S → ℝ))
    (hdet : ∀ x ∈ D, MvPolynomial.eval x A.det ≠ 0) :
    (polynomialMatrixInverseRationalMap A).DefinedOn D := by
  intro x hx ij
  exact hdet x hx

variable {S U T R C : Type*}

namespace RationalMap

/-- Renaming the source variables of a rational map along a coordinate map renames every numerator
and denominator polynomial. -/
noncomputable def renameSource (f : RationalMap S T) (e : S → U) : RationalMap U T where
  num := fun t => MvPolynomial.rename e (f.num t)
  den := fun t => MvPolynomial.rename e (f.den t)

/-- For a [rational map](hyp:f), [coordinate renaming](hyp:e), and [renamed-source assignment](hyp:x),
the [renamed map evaluates as the original map on the pulled-back assignment](goal). -/
theorem eval_renameSource (f : RationalMap S T) (e : S → U) (x : U → ℝ) :
    (f.renameSource e).eval x = f.eval (x ∘ e) := by
  funext t
  simp [eval, renameSource, MvPolynomial.eval_rename]

/-- The left lift of a rational map makes it depend on the left coordinates of a disjoint-sum
parameter space. -/
noncomputable def leftLift (f : RationalMap S T) : RationalMap (S ⊕ U) T :=
  f.renameSource Sum.inl

/-- The right lift of a rational map makes it depend on the right coordinates of a disjoint-sum
parameter space. -/
noncomputable def rightLift (g : RationalMap U T) : RationalMap (S ⊕ U) T :=
  g.renameSource Sum.inr

end RationalMap

/-- The sum-coordinate form of a product domain requires the left and right restrictions of one
assignment to lie in their respective domains. -/
def sumProductDomain (D : Set (S → ℝ)) (E : Set (U → ℝ)) : Set ((S ⊕ U) → ℝ) :=
  {z | (z ∘ Sum.inl) ∈ D ∧ (z ∘ Sum.inr) ∈ E}

/-- Given finite-coordinate rational maps [f](hyp:f) and [g](hyp:g) on [domains](hyp:D,E), with
[nonvanishing denominators for the first map](hyp:hf) and [the second map](hyp:hg), the [pairs of
parameters at which their images meet form one polynomial zero locus](goal). -/
theorem rationalMap_imageIntersection_locus [Fintype T]
    (f : RationalMap S T) (g : RationalMap U T)
    (D : Set (S → ℝ)) (E : Set (U → ℝ))
    (hf : f.DefinedOn D) (hg : g.DefinedOn E) :
    {z | z ∈ sumProductDomain D E ∧
      f.eval (z ∘ Sum.inl) = g.eval (z ∘ Sum.inr)} =
      sumProductDomain D E ∩
        Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus
          (conjunctionPolynomial
            (RationalMap.equalityPolynomial f.leftLift g.rightLift)) := by
  have hleft : f.leftLift.DefinedOn (sumProductDomain D E) := by
    intro z hz t
    change MvPolynomial.eval z (MvPolynomial.rename Sum.inl (f.den t)) ≠ 0
    rw [MvPolynomial.eval_rename]
    exact hf (z ∘ Sum.inl) hz.1 t
  have hright : g.rightLift.DefinedOn (sumProductDomain D E) := by
    intro z hz t
    change MvPolynomial.eval z (MvPolynomial.rename Sum.inr (g.den t)) ≠ 0
    rw [MvPolynomial.eval_rename]
    exact hg (z ∘ Sum.inr) hz.2 t
  simpa only [RationalMap.eval_renameSource, RationalMap.leftLift,
    RationalMap.rightLift] using
      (rationalMap_eq_locus f.leftLift g.rightLift (sumProductDomain D E)
        hleft hright)

/-- Given [rational matrix maps](hyp:f,g) on [domains](hyp:D,E), with [nonvanishing denominators
for both maps](hyp:hf,hg), the [parameter pairs at which their matrix images meet form one
polynomial zero locus](goal). -/
theorem rationalMatrixMap_imageIntersection_locus [Fintype R] [Fintype C]
    (f : RationalMatrixMap S R C) (g : RationalMatrixMap U R C)
    (D : Set (S → ℝ)) (E : Set (U → ℝ))
    (hf : f.DefinedOn D) (hg : g.DefinedOn E) :
    {z | z ∈ sumProductDomain D E ∧
      f.evalMatrix (z ∘ Sum.inl) = g.evalMatrix (z ∘ Sum.inr)} =
      sumProductDomain D E ∩
        Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus
          (conjunctionPolynomial
            (RationalMap.equalityPolynomial f.leftLift g.rightLift)) := by
  rw [← rationalMap_imageIntersection_locus f g D E hf hg]
  ext z
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  constructor
  · intro h
    funext ij
    exact congrFun (congrFun h ij.1) ij.2
  · intro h
    ext i j
    exact congrFun h (i, j)


end Causalean.Mathlib.AlgebraicGeometry


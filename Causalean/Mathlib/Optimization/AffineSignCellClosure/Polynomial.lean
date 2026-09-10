/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.AffineSignCellClosure.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Degree-one polynomial bridge

This module compiles checked real multivariate polynomials of total degree at most one into
the explicit affine-constraint representation and proves that this compilation preserves both
strict and weak cells.
-/

open scoped BigOperators
open Set

namespace Causalean.Mathlib.Optimization.AffineSignCellClosure

/-- Given [a real multivariate polynomial](hyp:p), its [compiled affine function](goal) is
given by [the coefficients of its degree-one monomials and its constant coefficient](step:1).

The affine function compiled from a real multivariate polynomial. -/
noncomputable def affineFnOfMvPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : AffineFn n where
  coeff i := MvPolynomial.coeff (Finsupp.single i 1) p
  constant := MvPolynomial.coeff 0 p

private lemma finsupp_eq_zero_or_single_of_sum_le_one {n : ℕ} (d : Fin n →₀ ℕ)
    (h : d.sum (fun _ e => e) ≤ 1) : d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  by_cases hd : d = 0
  · exact Or.inl hd
  · right
    apply (Finsupp.sum_eq_one_iff d).mp
    have hne : d.sum (fun _ e => e) ≠ 0 := by
      intro hz
      apply hd
      simpa only [Finsupp.sum, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff,
        ne_eq, not_imp_self, DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply] using hz
    omega

private lemma coeff_linear_sum_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.coeff 0 (∑ j, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) p) *
        MvPolynomial.X j) = 0 := by
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]

private lemma coeff_linear_sum_single {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.coeff (Finsupp.single i 1)
      (∑ j, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) p) * MvPolynomial.X j) =
      MvPolynomial.coeff (Finsupp.single i 1) p := by
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  · intro j hj hji
    have hs : Finsupp.single j 1 ≠ Finsupp.single i 1 :=
      fun h => hji (Finsupp.single_left_injective one_ne_zero h)
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, hs]
  · simp

/-- Given [a real multivariate polynomial](hyp:p), [a proof that its total degree is at most
one](hyp:hp), and [a coordinate vector](hyp:x), [evaluating its compiled affine function equals
evaluating the polynomial](goal). -/
theorem affineFnOfMvPolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ 1) (x : Fin n → ℝ) :
    (affineFnOfMvPolynomial p).eval x = MvPolynomial.eval x p := by
  classical
  have hp_eq : p = MvPolynomial.C (MvPolynomial.coeff 0 p) +
        ∑ i, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single i 1) p) * MvPolynomial.X i := by
    ext d
    by_cases hd0 : d = 0
    · subst d
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C, coeff_linear_sum_zero]
      simp
    by_cases hd1 : ∃ i, d = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hd1
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C, coeff_linear_sum_single]
      have hs : (0 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [hs]
    · have hd_not_mem : d ∉ p.support := by
        intro hd_mem
        have hsum : d.sum (fun _ e => e) ≤ 1 := (MvPolynomial.le_totalDegree hd_mem).trans hp
        exact (finsupp_eq_zero_or_single_of_sum_le_one d hsum).elim hd0 hd1
      rw [MvPolynomial.notMem_support_iff.mp hd_not_mem, MvPolynomial.coeff_add,
        MvPolynomial.coeff_C]
      simp only [if_neg (Ne.symm hd0), zero_add]
      rw [MvPolynomial.coeff_sum]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hs : Finsupp.single i 1 ≠ d := fun h => hd1 ⟨i, h.symm⟩
      simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, hs]
  unfold AffineFn.eval affineFnOfMvPolynomial
  calc
    (∑ i, MvPolynomial.coeff (Finsupp.single i 1) p * x i) + MvPolynomial.coeff 0 p =
        MvPolynomial.coeff 0 p + ∑ i, MvPolynomial.coeff (Finsupp.single i 1) p * x i := add_comm _ _
    _ = MvPolynomial.eval x (MvPolynomial.C (MvPolynomial.coeff 0 p) +
          ∑ i, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single i 1) p) * MvPolynomial.X i) := by simp
    _ = MvPolynomial.eval x p := by rw [← hp_eq]

/-- Given [a finite number of coordinates](hyp:n), a checked polynomial constraint contains
[its polynomial left-hand side](hyp:polynomial), [its weak-or-strict mark](hyp:kind), and [a
certificate that it is affine](hyp:degree_le_one).

A degree-at-most-one polynomial constraint with a weak-or-strict mark. -/
structure PolynomialConstraint (n : ℕ) where
  /-- The polynomial left-hand side, normalized against zero. -/
  polynomial : MvPolynomial (Fin n) ℝ
  /-- Whether the normalized inequality is weak or strict. -/
  kind : ConstraintKind
  /-- The polynomial has total degree at most one. -/
  degree_le_one : polynomial.totalDegree ≤ 1

/-- Given [a checked polynomial constraint](hyp:c), its [affine constraint compilation](goal)
is given by [the compiled affine function with the original mark retained](step:1).

Compilation from a checked polynomial constraint to an affine constraint. -/
noncomputable def PolynomialConstraint.toConstraint {n : ℕ} (c : PolynomialConstraint n) : Constraint n where
  fn := affineFnOfMvPolynomial c.polynomial
  kind := c.kind

/-- Given [a finite list of checked polynomial constraints](hyp:Γ), its [compiled affine
system](goal) is given by [compiling every listed constraint](step:1).

Entrywise compilation of a checked polynomial system. -/
noncomputable def affineSystemOfPolynomials {n : ℕ}
    (Γ : List (PolynomialConstraint n)) : AffineSystem n := Γ.map PolynomialConstraint.toConstraint

/-- Given [a finite list of checked polynomial constraints](hyp:Γ), its [direct strict
polynomial cell](goal) is given by [satisfaction of each original weak-or-strict polynomial comparison](step:1).

The strict cell written directly in polynomial syntax. -/
def polynomialStrictCell {n : ℕ} (Γ : List (PolynomialConstraint n)) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, match c.kind with
    | .weak => MvPolynomial.eval x c.polynomial ≤ 0
    | .strict => MvPolynomial.eval x c.polynomial < 0}

/-- Given [a finite list of checked polynomial constraints](hyp:Γ), its [direct weak polynomial
cell](goal) is given by [weak satisfaction of every polynomial constraint](step:1).

The weak cell written directly in polynomial syntax. -/
def polynomialWeakCell {n : ℕ} (Γ : List (PolynomialConstraint n)) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, MvPolynomial.eval x c.polynomial ≤ 0}

/-- Given [a finite checked polynomial system](hyp:Γ), [compilation preserves its strict cell](goal). -/
theorem strictCell_affineSystemOfPolynomials {n : ℕ} (Γ : List (PolynomialConstraint n)) :
    strictCell (affineSystemOfPolynomials Γ) = polynomialStrictCell Γ := by
  ext x
  constructor
  · intro hx c hc
    have hmem : c.toConstraint ∈ affineSystemOfPolynomials Γ := List.mem_map.mpr ⟨c, hc, rfl⟩
    have h := hx c.toConstraint hmem
    have hev := affineFnOfMvPolynomial_eval c.polynomial c.degree_le_one x
    cases hk : c.kind <;> simpa [polynomialStrictCell, Constraint.strictHolds,
      PolynomialConstraint.toConstraint, hk, hev] using h
  · intro hx c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have h := hx d hd
    have hev := affineFnOfMvPolynomial_eval d.polynomial d.degree_le_one x
    cases hk : d.kind <;> simpa [polynomialStrictCell, Constraint.strictHolds,
      PolynomialConstraint.toConstraint, hk, hev] using h

/-- Given [a finite checked polynomial system](hyp:Γ), [compilation preserves its weak cell](goal). -/
theorem weakCell_affineSystemOfPolynomials {n : ℕ} (Γ : List (PolynomialConstraint n)) :
    weakCell (affineSystemOfPolynomials Γ) = polynomialWeakCell Γ := by
  ext x
  constructor
  · intro hx c hc
    have hmem : c.toConstraint ∈ affineSystemOfPolynomials Γ := List.mem_map.mpr ⟨c, hc, rfl⟩
    have h := hx c.toConstraint hmem
    simpa [polynomialWeakCell, Constraint.weakHolds, PolynomialConstraint.toConstraint,
      affineFnOfMvPolynomial_eval c.polynomial c.degree_le_one x] using h
  · intro hx c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have h := hx d hd
    simpa [polynomialWeakCell, Constraint.weakHolds, PolynomialConstraint.toConstraint,
      affineFnOfMvPolynomial_eval d.polynomial d.degree_le_one x] using h

end Causalean.Mathlib.Optimization.AffineSignCellClosure

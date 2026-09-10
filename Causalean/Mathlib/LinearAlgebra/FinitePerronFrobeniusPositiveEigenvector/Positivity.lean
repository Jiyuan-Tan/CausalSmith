import Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Basic

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

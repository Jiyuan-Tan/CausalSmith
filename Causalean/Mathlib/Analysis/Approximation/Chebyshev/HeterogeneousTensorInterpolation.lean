module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Heterogeneous tensor interpolation

This module gives an explicit finite tensor-grid interpolant for arbitrary finite coordinate
types and coordinate-dependent degree bounds, together with coefficient and reproduction
identities.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A coordinate-specific degree map](hyp:d) determines [the uniform interpolation degree](goal).
[The degree](step:1) is the sum of the coordinatewise Jackson degree bounds. -/
def interpolationDegree (d : ι → ℕ) : ℕ := ∑ i, 2 * (d i - 1)

/-- [A coordinate-specific degree map](hyp:d) determines [the type of bounded tensor interpolation indices](goal).
[An index](step:1) chooses one grid position in every coordinate. -/
abbrev GridIndex (d : ι → ℕ) := ι → Fin (interpolationDegree d + 1)

/-- [A coordinate-specific degree map](hyp:d) and [a tensor interpolation index](hyp:b) determine [the corresponding tensor-grid point](goal).
[The point](step:1) uses the fixed equispaced node in every coordinate. -/
def gridPoint (d : ι → ℕ) (b : GridIndex d) : ι → ℝ :=
  fun i => equispacedLagrangeNode (interpolationDegree d) (b i)

/-- [A coordinate-specific degree map](hyp:d), [a target coefficient index](hyp:a), and [a grid-value index](hyp:b) determine [the tensor interpolation weight](goal).
[The weight](step:1) is the product of the one-dimensional recovery weights. -/
def gridWeight (d : ι → ℕ) (a b : GridIndex d) : ℝ :=
  ∏ i, equispacedLagrangeWeight (interpolationDegree d) (a i) (b i)

/-- [A coordinate-specific degree map](hyp:d) and [a tensor interpolation index](hyp:a) determine [the corresponding finitely supported monomial exponent](goal).
[The exponent](step:1) records the selected index in every coordinate. -/
def exponent (d : ι → ℕ) (a : GridIndex d) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

/-- [A coordinate-specific degree map](hyp:d) and [values on its tensor grid](hyp:v) determine [the explicit tensor interpolation polynomial](goal).
[The polynomial](step:1) is the finite monomial sum with fixed-grid recovery coefficients. -/
def interpolate (d : ι → ℕ) (v : GridIndex d → ℝ) : MvPolynomial ι ℝ :=
  ∑ a : GridIndex d, MvPolynomial.monomial (exponent d a)
    (∑ b : GridIndex d, gridWeight d a b * v b)

/-- [A coordinate-specific degree map](hyp:d), [tensor-grid values](hyp:v), and [a requested tensor index](hyp:a) imply that [the interpolant coefficient is its finite weighted grid-value sum](goal). -/
theorem coeff_interpolate (d : ι → ℕ) (v : GridIndex d → ℝ)
    (a : GridIndex d) :
    MvPolynomial.coeff (exponent d a) (interpolate d v) =
      ∑ b : GridIndex d, gridWeight d a b * v b := by
  classical
  have hinj : Function.Injective (exponent d) := by
    intro a b h
    funext i
    apply Fin.ext
    have hi := congrArg (fun m : ι →₀ ℕ => m i) h
    simpa [exponent] using hi
  simp only [interpolate, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : exponent d b ≠ exponent d a := fun h => hba (hinj h)
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ a)).elim

/-- [A coordinate-specific degree map](hyp:d), [tensor-grid values](hyp:v), [a monomial exponent](hyp:γ), and [an exponent outside the interpolation box](hyp:hγ) imply that [the interpolant coefficient vanishes](goal). -/
theorem coeff_interpolate_eq_zero (d : ι → ℕ) (v : GridIndex d → ℝ)
    (γ : ι →₀ ℕ) (hγ : ∃ i, interpolationDegree d < γ i) :
    MvPolynomial.coeff γ (interpolate d v) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hγ
  simp only [interpolate, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro a _
  have hne : exponent d a ≠ γ := by
    intro h
    have heq := congrArg (fun m : ι →₀ ℕ => m i) h
    have hle : (a i : ℕ) ≤ interpolationDegree d := Nat.le_of_lt_succ (a i).isLt
    simp only [exponent, Finsupp.coe_equivFunOnFinite_symm] at heq
    omega
  simp [hne]

/-- [A coordinate-specific degree map](hyp:d), [a multivariate polynomial](hyp:p), [its coordinatewise interpolation-degree bounds](hyp:hp), and [an evaluation point](hyp:x) imply that [interpolation from the fixed tensor grid reproduces the polynomial at that point](goal). -/
theorem interpolate_eval (d : ι → ℕ) (p : MvPolynomial ι ℝ)
    (hp : ∀ i, p.degreeOf i ≤ interpolationDegree d) (x : ι → ℝ) :
    MvPolynomial.eval x
      (interpolate d (fun b => MvPolynomial.eval (gridPoint d b) p)) =
      MvPolynomial.eval x p := by
  classical
  let D := interpolationDegree d
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : GridIndex d ≃ (Fin (Fintype.card ι) → Fin (D + 1)) :=
    Equiv.piCongrLeft' (fun _ => Fin (D + 1)) e
  let q : MvPolynomial (Fin (Fintype.card ι)) ℝ := MvPolynomial.rename e p
  have hdeg : ∀ j, q.degreeOf j ≤ D := by
    intro j
    change MvPolynomial.degreeOf j (MvPolynomial.rename e p) ≤ interpolationDegree d
    conv_lhs => rw [← e.apply_symm_apply j,
      MvPolynomial.degreeOf_rename_of_injective e.injective]
    exact hp (e.symm j)
  have hrec (a : GridIndex d) :
      p.coeff (exponent d a) =
        ∑ b : GridIndex d, gridWeight d a b *
          MvPolynomial.eval (gridPoint d b) p := by
    have he : (exponent d a).mapDomain e = tensorExponent (E a) := by
      ext j
      simp [exponent, tensorExponent, E, Finsupp.mapDomain_equiv_apply]
    have hc : tensorCoeffs q (E a) = p.coeff (exponent d a) := by
      rw [tensorCoeffs, ← he]
      exact MvPolynomial.coeff_rename_mapDomain e e.injective p (exponent d a)
    rw [← hc, tensorGrid_coeff_recovery q hdeg (E a)]
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    have hw : tensorGridWeight (E a) (E b) = gridWeight d a b := by
      simp only [tensorGridWeight, gridWeight]
      rw [← e.prod_comp]
      simp [E, D]
    have hv : MvPolynomial.eval (tensorGridPoint (E b)) q =
        MvPolynomial.eval (gridPoint d b) p := by
      change MvPolynomial.eval (tensorGridPoint (E b)) (MvPolynomial.rename e p) = _
      rw [MvPolynomial.eval_rename]
      have hpoint : tensorGridPoint (E b) ∘ e = gridPoint d b := by
        funext i
        simp [tensorGridPoint, gridPoint, E, D]
      rw [hpoint]
    rw [hw, hv]
  have hpoly : interpolate d (fun b => MvPolynomial.eval (gridPoint d b) p) = p := by
    apply MvPolynomial.ext
    intro γ
    by_cases hb : ∀ i, γ i ≤ D
    · let a : GridIndex d := fun i => ⟨γ i, Nat.lt_succ_of_le (hb i)⟩
      have ha : exponent d a = γ := by
        ext i
        simp [exponent, a]
      rw [← ha, coeff_interpolate]
      exact (hrec a).symm
    · push Not at hb
      obtain ⟨i, hi⟩ := hb
      rw [coeff_interpolate_eq_zero d _ γ ⟨i, hi⟩]
      symm
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact (not_le_of_gt hi) ((MvPolynomial.degreeOf_le_iff.mp (hp i)) γ hmem)
  rw [hpoly]


end Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

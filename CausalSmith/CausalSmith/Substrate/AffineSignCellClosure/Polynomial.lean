import CausalSmith.Substrate.AffineSignCellClosure.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree-one multivariate-polynomial bridge

This module compiles real multivariate polynomials of total degree at most one into the
explicit affine representation and checks that compilation preserves evaluation and cells.
-/

open scoped BigOperators
open Set

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- The affine function compiled from a real multivariate polynomial uses the constant
coefficient and its degree-one coordinate coefficients. -/
noncomputable def affineFnOfMvPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : AffineFn n where
  coeff i := MvPolynomial.coeff (Finsupp.single i 1) p
  constant := MvPolynomial.coeff 0 p

private lemma finsupp_eq_zero_or_single_of_sum_le_one {n : ℕ} (d : Fin n →₀ ℕ)
    (h : d.sum (fun _ e => e) ≤ 1) :
    d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
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
    MvPolynomial.coeff 0
      (∑ j, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) p) *
        MvPolynomial.X j) = 0 := by
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]

private lemma coeff_linear_sum_single {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.coeff (Finsupp.single i 1)
      (∑ j, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) p) *
        MvPolynomial.X j) =
      MvPolynomial.coeff (Finsupp.single i 1) p := by
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  · intro j hj hji
    have hs : Finsupp.single j 1 ≠ Finsupp.single i 1 :=
      fun h => hji (Finsupp.single_left_injective one_ne_zero h)
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, hs]
  · simp

/-- If a real multivariate polynomial has total degree at most one, evaluating its compiled
affine function equals evaluating the polynomial. -/
/- Proof strategy: expand with `MvPolynomial.eval_eq`. The total-degree bound forces every
supported exponent to be either zero or a single coordinate with exponent one; split these
two cases and identify their coefficients with the compiler fields. -/
theorem affineFnOfMvPolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ 1) (x : Fin n → ℝ) :
    (affineFnOfMvPolynomial p).eval x = MvPolynomial.eval x p := by
  classical
  have hp_eq :
      p = MvPolynomial.C (MvPolynomial.coeff 0 p) +
        ∑ i, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single i 1) p) *
          MvPolynomial.X i := by
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
        have hsum : d.sum (fun _ e => e) ≤ 1 :=
          (MvPolynomial.le_totalDegree hd_mem).trans hp
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
    (∑ i, MvPolynomial.coeff (Finsupp.single i 1) p * x i) +
        MvPolynomial.coeff 0 p =
      MvPolynomial.coeff 0 p +
        ∑ i, MvPolynomial.coeff (Finsupp.single i 1) p * x i := add_comm _ _
    _ = MvPolynomial.eval x
        (MvPolynomial.C (MvPolynomial.coeff 0 p) +
          ∑ i, MvPolynomial.C (MvPolynomial.coeff (Finsupp.single i 1) p) *
            MvPolynomial.X i) := by simp
    _ = MvPolynomial.eval x p := by rw [← hp_eq]

/-- A degree-at-most-one polynomial constraint packages the degree proof together with its
weak/strict mark. -/
structure PolynomialConstraint (n : ℕ) where
  /-- The polynomial left-hand side, normalized against zero. -/
  polynomial : MvPolynomial (Fin n) ℝ
  /-- Whether the normalized inequality is weak or strict. -/
  kind : ConstraintKind
  /-- The polynomial is affine because its total degree is at most one. -/
  degree_le_one : polynomial.totalDegree ≤ 1

/-- Compilation forgets only the polynomial syntax and retains the checked affine function
and the constraint mark. -/
noncomputable def PolynomialConstraint.toConstraint {n : ℕ}
    (c : PolynomialConstraint n) : Constraint n where
  fn := affineFnOfMvPolynomial c.polynomial
  kind := c.kind

/-- A finite checked polynomial system compiles entrywise to an affine constraint system. -/
noncomputable def affineSystemOfPolynomials {n : ℕ}
    (Γ : List (PolynomialConstraint n)) : AffineSystem n :=
  Γ.map PolynomialConstraint.toConstraint

/-- The direct strict cell of a checked polynomial system uses polynomial evaluation and
the original weak/strict comparisons. -/
def polynomialStrictCell {n : ℕ} (Γ : List (PolynomialConstraint n)) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, match c.kind with
    | .weak => MvPolynomial.eval x c.polynomial ≤ 0
    | .strict => MvPolynomial.eval x c.polynomial < 0}

/-- The direct weak cell of a checked polynomial system weakens every polynomial comparison. -/
def polynomialWeakCell {n : ℕ} (Γ : List (PolynomialConstraint n)) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ Γ, MvPolynomial.eval x c.polynomial ≤ 0}

/-- Compiling a finite checked polynomial system preserves its strict cell exactly. -/
theorem strictCell_affineSystemOfPolynomials {n : ℕ}
    (Γ : List (PolynomialConstraint n)) :
    strictCell (affineSystemOfPolynomials Γ) = polynomialStrictCell Γ := by
  ext x
  constructor
  · intro hx c hc
    have hmem : c.toConstraint ∈ affineSystemOfPolynomials Γ := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    have h := hx c.toConstraint hmem
    have hev := affineFnOfMvPolynomial_eval c.polynomial c.degree_le_one x
    cases hk : c.kind with
    | weak =>
        simpa [polynomialStrictCell, Constraint.strictHolds,
          PolynomialConstraint.toConstraint, hk, hev] using h
    | strict =>
        simpa [polynomialStrictCell, Constraint.strictHolds,
          PolynomialConstraint.toConstraint, hk, hev] using h
  · intro hx c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have h := hx d hd
    have hev := affineFnOfMvPolynomial_eval d.polynomial d.degree_le_one x
    cases hk : d.kind with
    | weak =>
        simpa [polynomialStrictCell, Constraint.strictHolds,
          PolynomialConstraint.toConstraint, hk, hev] using h
    | strict =>
        simpa [polynomialStrictCell, Constraint.strictHolds,
          PolynomialConstraint.toConstraint, hk, hev] using h

/-- Compiling a finite checked polynomial system preserves its weak cell exactly. -/
theorem weakCell_affineSystemOfPolynomials {n : ℕ}
    (Γ : List (PolynomialConstraint n)) :
    weakCell (affineSystemOfPolynomials Γ) = polynomialWeakCell Γ := by
  ext x
  constructor
  · intro hx c hc
    have hmem : c.toConstraint ∈ affineSystemOfPolynomials Γ := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    have h := hx c.toConstraint hmem
    simpa [polynomialWeakCell, Constraint.weakHolds,
      PolynomialConstraint.toConstraint,
      affineFnOfMvPolynomial_eval c.polynomial c.degree_le_one x] using h
  · intro hx c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have h := hx d hd
    simpa [polynomialWeakCell, Constraint.weakHolds,
      PolynomialConstraint.toConstraint,
      affineFnOfMvPolynomial_eval d.polynomial d.degree_le_one x] using h

end CausalSmith.Substrate.AffineSignCellClosure

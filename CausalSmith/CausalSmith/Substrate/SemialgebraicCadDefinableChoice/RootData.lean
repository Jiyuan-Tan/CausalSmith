import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.Univariate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Polynomial.Order

/-!
# Transport of univariate polynomial root data

This module isolates the fixed-polynomial lemma needed by parametric delineability.  An increasing
equivalence of the real line that preserves real-root multiplicities, together with degree and
leading-sign data, preserves the exact sign of a polynomial at corresponding points.
-/

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

private theorem SameExactSign.symm' {a b : ℝ} (h : SameExactSign a b) :
    SameExactSign b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem SameExactSign.trans' {a b c : ℝ}
    (hab : SameExactSign a b) (hbc : SameExactSign b c) :
    SameExactSign a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

private theorem SameExactSign.mul' {a b c d : ℝ}
    (h₁ : SameExactSign a b) (h₂ : SameExactSign c d) :
    SameExactSign (a * c) (b * d) := by
  rcases h₁ with ⟨hn₁, hz₁, hp₁⟩
  rcases h₂ with ⟨hn₂, hz₂, hp₂⟩
  constructor
  · simp only [mul_neg_iff]
    aesop
  constructor
  · simp only [mul_eq_zero]
    aesop
  · simp only [mul_pos_iff]
    aesop

private theorem sameExactSign_sub_orderIso (transport : ℝ ≃o ℝ) (x a : ℝ) :
    SameExactSign (x - a) (transport x - transport a) := by
  simp only [SameExactSign, sub_lt_zero, sub_eq_zero, sub_pos]
  exact ⟨transport.lt_iff_lt.symm, transport.injective.eq_iff.symm,
    transport.lt_iff_lt.symm⟩

private theorem sameExactSign_eval_rootProducts
    (transport : ℝ ≃o ℝ) (roots : Multiset ℝ) (x : ℝ) :
    SameExactSign
      (Polynomial.eval x
        ((roots.map fun a => Polynomial.X - Polynomial.C a).prod))
      (Polynomial.eval (transport x)
        (((roots.map transport).map fun a => Polynomial.X - Polynomial.C a).prod)) := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp [SameExactSign]
  | @cons a roots ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact (sameExactSign_sub_orderIso transport x a).mul' ih

private theorem sameExactSign_eval_leadingCoeff_of_roots_eq_zero
    (polynomial : Polynomial ℝ) (hPolynomial : polynomial ≠ 0)
    (hRoots : polynomial.roots = 0) (x : ℝ) :
    SameExactSign (polynomial.eval x) polynomial.leadingCoeff := by
  have hNoRoot : ∀ y : ℝ, ¬polynomial.IsRoot y := by
    intro y hy
    have hyMem : y ∈ polynomial.roots := (Polynomial.mem_roots hPolynomial).2 hy
    rw [hRoots] at hyMem
    simp at hyMem
  have hLeading : polynomial.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hPolynomial
  rcases lt_or_gt_of_ne hLeading with hLeadingNeg | hLeadingPos
  · have hEval : polynomial.eval x < 0 :=
      Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
        (fun y hy => (hNoRoot y hy).elim) hLeadingNeg.le
    simp [SameExactSign, hEval, hLeadingNeg, ne_of_lt hEval, ne_of_lt hLeadingNeg,
      not_lt_of_ge hEval.le, not_lt_of_ge hLeadingNeg.le]
  · have hEval : 0 < polynomial.eval x :=
      Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (fun y hy => (hNoRoot y hy).elim) hLeadingPos.le
    simp [SameExactSign, hEval, hLeadingPos, ne_of_gt hEval, ne_of_gt hLeadingPos,
      not_lt_of_ge hEval.le, not_lt_of_ge hLeadingPos.le]

/-- Two real polynomials have transported root data along an increasing equivalence when their
degrees and leading signs agree and every real-root multiplicity is carried by that equivalence. -/
def PolynomialRootDataTransportedBy (transport : ℝ ≃o ℝ)
    (left right : Polynomial ℝ) : Prop :=
  left.natDegree = right.natDegree ∧
    SameExactSign left.leadingCoeff right.leadingCoeff ∧
      ∀ x, left.rootMultiplicity x = right.rootMultiplicity (transport x)

/-- Transported root data is symmetric after replacing the increasing equivalence by its inverse. -/
theorem PolynomialRootDataTransportedBy.symm {transport : ℝ ≃o ℝ}
    {left right : Polynomial ℝ}
    (h : PolynomialRootDataTransportedBy transport left right) :
    PolynomialRootDataTransportedBy transport.symm right left := by
  refine ⟨h.1.symm, ⟨h.2.1.1.symm, h.2.1.2.1.symm, h.2.1.2.2.symm⟩, ?_⟩
  intro y
  simpa using (h.2.2 (transport.symm y)).symm

/-- An increasing equivalence preserving degree, leading sign, and every real-root multiplicity
also preserves the exact sign of polynomial values at corresponding real points.

This is the fixed-coefficient root-order lemma in the delineability chain.  One proof factors out
the ordered real roots with multiplicity: the remaining real polynomial has constant nonzero sign,
and the sign at positive infinity is fixed by the common leading sign and degree. -/
theorem sameExactSign_eval_of_rootDataTransportedBy (transport : ℝ ≃o ℝ)
    (left right : Polynomial ℝ)
    (h : PolynomialRootDataTransportedBy transport left right) (x : ℝ) :
    SameExactSign (Polynomial.eval x left) (Polynomial.eval (transport x) right) := by
  classical
  rcases h with ⟨hDegree, hLeading, hMultiplicity⟩
  by_cases hLeft : left = 0
  · subst left
    have hRightLeading : right.leadingCoeff = 0 := hLeading.2.1.mp (by simp)
    have hRight : right = 0 := Polynomial.leadingCoeff_eq_zero.mp hRightLeading
    subst right
    simp [SameExactSign]
  have hRightLeading : right.leadingCoeff ≠ 0 := by
    intro hZero
    exact Polynomial.leadingCoeff_ne_zero.mpr hLeft (hLeading.2.1.mpr hZero)
  have hRight : right ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hRightLeading
  have hRoots : right.roots = left.roots.map transport := by
    ext y
    obtain ⟨z, rfl⟩ := transport.surjective y
    rw [Polynomial.count_roots, ← hMultiplicity z, ← Polynomial.count_roots,
      Multiset.count_map_eq_count' transport left.roots transport.injective]
  obtain ⟨leftResidual, hLeftFactor, hLeftDegree, hLeftRoots⟩ :=
    Polynomial.exists_prod_multiset_X_sub_C_mul left
  obtain ⟨rightResidual, hRightFactor, hRightDegree, hRightRoots⟩ :=
    Polynomial.exists_prod_multiset_X_sub_C_mul right
  have hLeftProductMonic : Polynomial.Monic
      ((left.roots.map fun a => Polynomial.X - Polynomial.C a).prod) :=
    Polynomial.monic_multisetProd_X_sub_C left.roots
  have hRightProductMonic : Polynomial.Monic
      ((right.roots.map fun a => Polynomial.X - Polynomial.C a).prod) :=
    Polynomial.monic_multisetProd_X_sub_C right.roots
  have hLeftResidualNe : leftResidual ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hLeftFactor
    exact hLeft hLeftFactor.symm
  have hRightResidualNe : rightResidual ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hRightFactor
    exact hRight hRightFactor.symm
  have hLeftResidualLeading :
      leftResidual.leadingCoeff = left.leadingCoeff := by
    rw [← hLeftFactor, Polynomial.leadingCoeff_monic_mul hLeftProductMonic]
  have hRightResidualLeading :
      rightResidual.leadingCoeff = right.leadingCoeff := by
    rw [← hRightFactor, Polynomial.leadingCoeff_monic_mul hRightProductMonic]
  have hResidualSign :
      SameExactSign (leftResidual.eval x) (rightResidual.eval (transport x)) := by
    exact
      (sameExactSign_eval_leadingCoeff_of_roots_eq_zero
          leftResidual hLeftResidualNe hLeftRoots x).trans'
        ((hLeftResidualLeading ▸ hRightResidualLeading ▸ hLeading).trans'
          (sameExactSign_eval_leadingCoeff_of_roots_eq_zero
            rightResidual hRightResidualNe hRightRoots (transport x)).symm')
  rw [← hLeftFactor, ← hRightFactor, Polynomial.eval_mul, Polynomial.eval_mul, hRoots]
  exact (sameExactSign_eval_rootProducts transport left.roots x).mul' hResidualSign

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice

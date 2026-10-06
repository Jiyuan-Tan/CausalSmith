module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LegendreBasis
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Procedure

/-!
# Coefficients of iterated shifted-Legendre differentiation

The exact finite differentiation matrix acts on every degree-bounded polynomial
expansion. Iteration identifies all derivative coefficients before the chain
bound and Parseval steps in the factorial derivative estimate.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Differentiation in the unnormalized shifted-Legendre basis, retaining parity. Given [the displayed inputs and assumptions](hyp:k,l), [this definition specifies the stated object](goal). -/
def legendreDerivativeEntry (k l : ℕ) : ℝ :=
  if k < l ∧ Odd (l-k) then 2 * (2*(k : ℝ)+1) else 0

/-- The finite coefficient action of ordinary differentiation. Given [the displayed inputs and assumptions](hyp:m,c,k), [this definition specifies the stated object](goal). -/
def legendreDerivativeAction (m : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (m+1), legendreDerivativeEntry k l * c l

/-- The derivative of each basis polynomial has exactly the matrix's column. Given [the displayed inputs and assumptions](hyp:hleg,m,l,hl), [the stated mathematical conclusion holds](goal). -/
lemma forwardLegendrePolynomial_derivative_matrix (hleg : ClassicalLegendreFacts)
    (m l : ℕ) (hl : l ≤ m) :
    (forwardLegendrePolynomial l).derivative =
      ∑ k ∈ Finset.range (m+1),
        Polynomial.C (legendreDerivativeEntry k l) * forwardLegendrePolynomial k := by
  apply Polynomial.funext
  intro x
  rw [forwardLegendrePolynomial_derivative_eval, shiftedLegendre_derivative_expansion hleg]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    forwardLegendrePolynomial_eval]
  rw [Finset.sum_filter, Finset.mul_sum]
  symm
  calc
    _ = ∑ k ∈ Finset.range l,
        legendreDerivativeEntry k l * shiftedLegendre k x := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hn
      have hkl : ¬ k < l := by simpa using hn
      simp [legendreDerivativeEntry, hkl]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [legendreDerivativeEntry, Finset.mem_range.mp hk, true_and]
      split_ifs <;> ring

/-- Differentiating a finite basis expansion applies the coefficient matrix once. Given [the displayed inputs and assumptions](hyp:hleg,m,c), [the stated mathematical conclusion holds](goal). -/
lemma legendre_expansion_derivative_action (hleg : ClassicalLegendreFacts)
    (m : ℕ) (c : ℕ → ℝ) :
    (∑ l ∈ Finset.range (m+1),
      Polynomial.C (c l) * forwardLegendrePolynomial l).derivative =
      ∑ k ∈ Finset.range (m+1),
        Polynomial.C (legendreDerivativeAction m c k) * forwardLegendrePolynomial k := by
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul]
  have he : (∑ l ∈ Finset.range (m+1),
      Polynomial.C (c l) * (forwardLegendrePolynomial l).derivative) =
      ∑ l ∈ Finset.range (m+1), Polynomial.C (c l) *
        (∑ k ∈ Finset.range (m+1),
          Polynomial.C (legendreDerivativeEntry k l) * forwardLegendrePolynomial k) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [forwardLegendrePolynomial_derivative_matrix hleg m l
      (by have := Finset.mem_range.mp hl; omega)]
  rw [he]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [legendreDerivativeAction, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_mul]
  ring

/-- Iterating the matrix action gives every coefficient of the iterated derivative. Given [the displayed inputs and assumptions](hyp:hleg,m,j,c), [the stated mathematical conclusion holds](goal). -/
lemma legendre_expansion_iterated_derivative (hleg : ClassicalLegendreFacts)
    (m j : ℕ) (c : ℕ → ℝ) :
    polyDeriv j (∑ l ∈ Finset.range (m+1),
      Polynomial.C (c l) * forwardLegendrePolynomial l) =
      ∑ k ∈ Finset.range (m+1),
        Polynomial.C (((legendreDerivativeAction m)^[j]) c k) *
          forwardLegendrePolynomial k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [polyDeriv, Function.iterate_succ_apply', ← polyDeriv, ih,
      legendre_expansion_derivative_action hleg]
    simp only [Function.iterate_succ_apply']

/-- The canonical orthogonal coefficients reconstruct the polynomial itself. Given [the displayed inputs and assumptions](hyp:hleg,p,m,hm), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_legendre_coefficient_identity (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    p = ∑ k ∈ Finset.range (m+1),
      Polynomial.C ((2*(k : ℝ)+1) *
        (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre k x)) *
          forwardLegendrePolynomial k := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    forwardLegendrePolynomial_eval]
  exact polynomial_shiftedLegendre_expansion hleg p (m+1)
    (lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast Nat.lt_succ_of_le hm)) x

end CausalSmith.Stat.RdTruesideNoiseFrontier

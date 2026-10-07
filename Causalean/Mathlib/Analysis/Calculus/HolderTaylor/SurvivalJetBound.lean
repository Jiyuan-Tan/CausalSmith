module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.SurvivalDerivative

/-!
# Uniform jet bounds for an exponential interval primitive

The differential equation for an exponential primitive bounds each derivative
from lower derivatives. This module isolates the finite recurrence from the
Hölder argument in the survival closure theorem.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [an interval length d](hyp:d) that is [positive](hyp:hd),
[a nonnegative derivative envelope C](hyp:C,hC) and [a nonnegative value envelope E](hyp:E,hE).
Then [there is one nonnegative constant B such that, for every interval from a to a + d and every
integrand h that is k times continuously differentiable on it, whose within-interval derivatives
of every order at most k are bounded by C there, and whose survival-type function
exp(−∫ from a to t of h) is bounded by E there, every within-interval derivative of that
survival-type function of order at most k + 1 is bounded by B on the whole interval](goal). The
constant does not depend on the interval location or on the integrand. -/
theorem survival_jet_bound_of_integrand_jet_bound
    (k : ℕ) (d C E : ℝ) (hd : 0 < d) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (h : ℝ → ℝ),
        ContDiffOn ℝ k h (Set.Icc a (a + d)) →
        (∀ j ≤ k, ∀ t ∈ Set.Icc a (a + d),
          |iteratedDerivWithin j h (Set.Icc a (a + d)) t| ≤ C) →
        (∀ t ∈ Set.Icc a (a + d),
          |Real.exp (-(∫ x in a..t, h x))| ≤ E) →
        ∀ j ≤ k + 1, ∀ t ∈ Set.Icc a (a + d),
          |iteratedDerivWithin j
            (fun u : ℝ => Real.exp (-(∫ x in a..u, h x)))
            (Set.Icc a (a + d)) t| ≤ B := by
  let B : ℕ → ℝ := Nat.rec E (fun n b =>
    b + ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * C * b)
  have hBzero : B 0 = E := rfl
  have hBstep (n : ℕ) : B (n + 1) =
      B n + ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * C * B n := rfl
  have hBnonneg : ∀ n, 0 ≤ B n := by
    intro n
    induction n with
    | zero => simpa [hBzero] using hE
    | succ n ih =>
        rw [hBstep]
        exact add_nonneg ih (Finset.sum_nonneg fun i hi => by positivity)
  have hBmono (n : ℕ) : B n ≤ B (n + 1) := by
    rw [hBstep]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (hBnonneg n))
  refine ⟨B (k + 1), hBnonneg (k + 1), ?_⟩
  intro a h hh hjet hvalue
  let s := Set.Icc a (a + d)
  let S := fun u : ℝ => Real.exp (-(∫ x in a..u, h x))
  have hbound : ∀ n ≤ k + 1, ∀ j ≤ n, ∀ t ∈ s,
      |iteratedDerivWithin j S s t| ≤ B n := by
    intro n hn
    induction n with
    | zero =>
        intro j hj t ht
        have hj0 : j = 0 := by omega
        subst j
        simpa [S, s, hBzero] using hvalue t ht
    | succ n ih =>
        intro j hj t ht
        by_cases hjn : j ≤ n
        · exact (ih (by omega) j hjn t ht).trans (hBmono n)
        · have hjeq : j = n + 1 := by omega
          subst j
          have hnk : n ≤ k := by omega
          rw [survival_iteratedDerivWithin_succ k a d hd h hh n hnk t ht]
          rw [abs_neg]
          calc
            |∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℝ) * iteratedDerivWithin i h s t *
                  iteratedDerivWithin (n - i) S s t| ≤
                ∑ i ∈ Finset.range (n + 1),
                  |(Nat.choose n i : ℝ) * iteratedDerivWithin i h s t *
                    iteratedDerivWithin (n - i) S s t| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i ∈ Finset.range (n + 1),
                  (Nat.choose n i : ℝ) * C * B n := by
              apply Finset.sum_le_sum
              intro i hi
              have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
              have hhi := hjet i (hin.trans hnk) t ht
              have hSi := ih (by omega) (n - i) (Nat.sub_le _ _) t ht
              rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              calc
                (Nat.choose n i : ℝ) * |iteratedDerivWithin i h s t| *
                    |iteratedDerivWithin (n - i) S s t| =
                    (Nat.choose n i : ℝ) *
                      (|iteratedDerivWithin i h s t| *
                        |iteratedDerivWithin (n - i) S s t|) := by ring
                _ ≤ (Nat.choose n i : ℝ) * (C * B n) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hhi hSi (abs_nonneg _) hC) (Nat.cast_nonneg _)
                _ = (Nat.choose n i : ℝ) * C * B n := by ring
            _ ≤ B (n + 1) := by rw [hBstep]; exact le_add_of_nonneg_left (hBnonneg n)
  exact hbound (k + 1) le_rfl

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor

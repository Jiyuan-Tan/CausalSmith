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

/-- A uniform bound on all derivatives of the integrand through order `k`,
together with a uniform value bound on its exponential primitive, gives one
uniform bound on all derivatives of the exponential primitive through order
`k + 1`. The resulting constant is independent of the interval location and
of the integrand.
[The derivative order, length, envelopes, and sign assumptions](hyp:k,d,C,E,hd,hC,hE) yield [the stated survival-jet bound](goal). -/
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

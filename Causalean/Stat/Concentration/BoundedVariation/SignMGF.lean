module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential moment of a finite signed sum

The uniform law on Boolean sign vectors gives the basic sub-Gaussian estimate
used in the bounded-variation path maximal inequality.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The sign-average exponential moment of a finite Rademacher sum is at
most the Gaussian exponential moment with variance equal to the sum of
squared coefficients](goal).

This includes the empty family.
-/
theorem signMGF_le {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (∑ σ : Fin n → Bool,
      Real.exp (t * ∑ j, (if σ j then (1 : ℝ) else -1) * a j)) /
        (2 ^ n : ℝ) ≤
      Real.exp (t ^ 2 / 2 * ∑ j, (a j) ^ 2) := by
  classical
  have hfactor :
      (∑ σ : Fin n → Bool,
        Real.exp (t * ∑ j, (if σ j then (1 : ℝ) else -1) * a j)) /
          (2 ^ n : ℝ) = ∏ j, Real.cosh (t * a j) := by
    have hsum :
        (∑ σ : Fin n → Bool,
          Real.exp (t * ∑ j, (if σ j then (1 : ℝ) else -1) * a j)) =
          ∏ j, ∑ b : Bool, Real.exp (t * (if b then (1 : ℝ) else -1) * a j) := by
      simp_rw [Finset.mul_sum, Real.exp_sum, mul_assoc]
      simpa only [mul_assoc] using
        (Fintype.prod_sum fun j : Fin n =>
          fun b : Bool => Real.exp (t * (if b then (1 : ℝ) else -1) * a j)).symm
    rw [hsum]
    have htwo : (2 ^ n : ℝ) = ∏ _j : Fin n, (2 : ℝ) := by simp
    rw [htwo, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp
  rw [hfactor]
  calc
    (∏ j, Real.cosh (t * a j)) ≤ ∏ j, Real.exp ((t * a j) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (Real.cosh_pos _).le
      · intro j hj
        exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (t ^ 2 / 2 * ∑ j, (a j) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end Causalean.Stat.Concentration.BoundedVariation

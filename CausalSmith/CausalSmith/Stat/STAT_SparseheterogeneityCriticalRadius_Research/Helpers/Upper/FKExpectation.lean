module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightWeightIdentity

/-! Exact first moment of the light-cell factorial correction polynomial. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Multiplication by the count shifts the falling factorial based at its predecessor. -/
lemma natCast_mul_falling_pred (N ell : ℕ) :
    (N : ℝ) * (falling (N - 1) ell : ℝ) = (falling N (ell + 1) : ℝ) := by
  cases N with
  | zero => simp [falling]
  | succ N =>
      simp only [Nat.succ_sub_one, falling]
      exact_mod_cast (Nat.succ_descFactorial_succ N ell).symm

/-- Equation (15): the Poisson mean of `N * FK K R N` is
`λ * GK K (λ / R)`. -/
lemma poisson_mul_FK_mean (K : ℕ) (R : ℝ) (rate : NNReal) (hR : R ≠ 0) :
    (∫ N : ℕ, (N : ℝ) * FK K R N ∂poissonMeasure rate) =
      (rate : ℝ) * GK K ((rate : ℝ) / R) := by
  classical
  let μ := poissonMeasure rate
  calc
    (∫ N : ℕ, (N : ℝ) * FK K R N ∂μ) =
        ∫ N : ℕ, ∑ ell ∈ Finset.range (K - 1),
          (gCoeff K ell / R ^ ell) * (falling N (ell + 1) : ℝ) ∂μ := by
      congr 1
      funext N
      simp only [FK, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      calc
        (N : ℝ) * (gCoeff K ell * (falling (N - 1) ell : ℝ) / R ^ ell) =
            (gCoeff K ell / R ^ ell) *
              ((N : ℝ) * (falling (N - 1) ell : ℝ)) := by ring
        _ = _ := by rw [natCast_mul_falling_pred]
    _ = ∑ ell ∈ Finset.range (K - 1),
          (gCoeff K ell / R ^ ell) * (rate : ℝ) ^ (ell + 1) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro ell _
        rw [integral_const_mul]
        simp only [falling, μ]
        rw [
          Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment]
      · intro ell _
        exact (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
          rate (ell + 1)).const_mul _
    _ = (rate : ℝ) * GK K ((rate : ℝ) / R) := by
      unfold GK
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      rw [pow_succ, div_pow]
      field_simp [hR]

lemma poisson_mul_FK_integrable (K : ℕ) (R : ℝ) (rate : NNReal) :
    Integrable (fun N : ℕ => (N : ℝ) * FK K R N) (poissonMeasure rate) := by
  classical
  rw [show (fun N : ℕ => (N : ℝ) * FK K R N) = fun N =>
      ∑ ell ∈ Finset.range (K - 1),
        (gCoeff K ell / R ^ ell) * (falling N (ell + 1) : ℝ) by
    funext N
    simp only [FK, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ell _
    rw [← natCast_mul_falling_pred]
    ring]
  apply integrable_finsetSum
  intro ell _
  exact (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
    rate (ell + 1)).const_mul _

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

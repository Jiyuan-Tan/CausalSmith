module
public import Causalean.Stat.Concentration.BoundedVariation.SignedLevelEnergy

/-!
# Numerical dyadic chaining series

The square roots of the finite-class dyadic bounds form a summable numerical
series. The explicit bound leaves room for the final constant 4096.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

private theorem dyadic_linear_le_geometric (k : ℕ) :
    (k : ℝ) + 2 ≤ 4 * (9 / 8 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 6
    · interval_cases k <;> norm_num at *
    · have hk' : (6 : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_not_gt hk)
      have hp : (0 : ℝ) ≤ (9 / 8 : ℝ) ^ k := by positivity
      have h := mul_le_mul_of_nonneg_right ih (show (0 : ℝ) ≤ 9 / 8 by norm_num)
      push_cast
      rw [pow_succ]
      nlinarith

private theorem dyadic_log_sqrt_le_geometric (k : ℕ) :
    Real.sqrt (32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
      (2 : ℝ) ^ (k + 1)) ≤ 8 * (3 / 4 : ℝ) ^ k := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hlog : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
    have h := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ k + 1 by positivity)
    push_cast at h ⊢
    nlinarith
  have hnum : 1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ) ≤
      4 * (9 / 8 : ℝ) ^ k := by
    linarith [dyadic_linear_le_geometric k]
  have hbase : 32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
      (2 : ℝ) ^ (k + 1) ≤ (8 * (3 / 4 : ℝ) ^ k) ^ 2 := by
    calc
      _ ≤ 32 * (4 * (9 / 8 : ℝ) ^ k) / (2 : ℝ) ^ (k + 1) := by
        apply div_le_div_of_nonneg_right
        · nlinarith
        · positivity
      _ = (8 * (3 / 4 : ℝ) ^ k) ^ 2 := by
        rw [pow_succ]
        ring_nf
        rw [← mul_pow, mul_comm k 2, pow_mul]
        norm_num
  have htarget : 0 ≤ 8 * (3 / 4 : ℝ) ^ k := by positivity
  exact (Real.sqrt_le_iff).2 ⟨htarget, hbase⟩

/-- [The square roots of the dyadic logarithmic energy factors
32 (1 + log 2^(k+1)) / 2^(k+1) form a summable sequence in k](goal).
-/
theorem dyadic_log_sqrt_summable :
    Summable (fun k : ℕ => Real.sqrt
      (32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
        (2 : ℝ) ^ (k + 1))) := by
  /- Use `log(2^(k+1)) ≤ k+1`, then compare the square root of the
  polynomial factor with a geometric sequence of ratio strictly between
  `1/sqrt 2` and `1`. -/
  apply Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _) (fun k =>
    dyadic_log_sqrt_le_geometric k)
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).mul_left 8

/-- [The sum over all levels k of the square roots of
32 (1 + log 2^(k+1)) / 2^(k+1) is at most 40](goal).

This is the dyadic factor in the L₂ triangle bound, independent of the
number of paths and signs.
-/
theorem dyadic_log_sqrt_tsum_le_40 :
    (∑' k : ℕ, Real.sqrt
      (32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
        (2 : ℝ) ^ (k + 1))) ≤ 40 := by
  /- A geometric majorant sums to 32, which is below 40. -/
  calc
    _ ≤ ∑' k : ℕ, 8 * (3 / 4 : ℝ) ^ k := by
      apply Summable.tsum_le_tsum (fun k => dyadic_log_sqrt_le_geometric k)
      · exact dyadic_log_sqrt_summable
      · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
          (by norm_num : (3 / 4 : ℝ) < 1)).mul_left 8
    _ = 32 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)]
      norm_num
    _ ≤ 40 := by norm_num

end Causalean.Stat.Concentration.BoundedVariation

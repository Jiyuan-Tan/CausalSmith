module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.AuditWeightPointwise

/-! A coarse exponential envelope for the reciprocal-polynomial coefficients. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

/-- Each coefficient used by `GK K` is bounded by `2^(4K)`. -/
lemma abs_gCoeff_le_pow_four_degree {K ell : ℕ} (hK : 2 ≤ K)
    (hell : ell < K - 1) :
    |gCoeff K ell| ≤ (2 : ℝ) ^ (4 * K) := by
  have hK0 : (0 : ℝ) < K := by positivity
  have hden : (1 : ℝ) ≤ (K : ℝ) * (K + ell + 2 : ℕ) := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have hsum1 : (1 : ℝ) ≤ (K + ell + 2 : ℕ) := by
      exact_mod_cast (show 1 ≤ K + ell + 2 by omega)
    calc
      1 = 1 * 1 := by ring
      _ ≤ (K : ℝ) * (K + ell + 2 : ℕ) := by gcongr
  have hchooseNat : Nat.choose (K + ell + 2) (2 * ell + 4) ≤
      2 ^ (K + ell + 2) := Nat.choose_le_two_pow _ _
  have hchoose : (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) ≤
      (2 : ℝ) ^ (K + ell + 2) := by exact_mod_cast hchooseNat
  have hexponents : 2 * ell + 3 + (K + ell + 2) ≤ 4 * K := by omega
  have hpowers : (2 : ℝ) ^ (2 * ell + 3) *
      (2 : ℝ) ^ (K + ell + 2) ≤ (2 : ℝ) ^ (4 * K) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hexponents
  have habs : |gCoeff K ell| =
      (2 : ℝ) ^ (2 * ell + 3) *
          (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) /
        ((K : ℝ) * (K + ell + 2 : ℕ)) := by
    rw [gCoeff, abs_div, abs_mul, abs_mul, abs_pow]
    simp only [abs_neg, abs_one, one_pow]
    rw [abs_of_nonneg (pow_nonneg (by norm_num) _),
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    ring
  rw [habs]
  have hnum0 : 0 ≤ (2 : ℝ) ^ (2 * ell + 3) *
      (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) := by positivity
  calc
    (2 : ℝ) ^ (2 * ell + 3) *
          (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) /
        ((K : ℝ) * (K + ell + 2 : ℕ)) ≤
      (2 : ℝ) ^ (2 * ell + 3) *
          (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) := by
        exact div_le_self hnum0 hden
    _ ≤ (2 : ℝ) ^ (2 * ell + 3) *
          (2 : ℝ) ^ (K + ell + 2) := by gcongr
    _ ≤ _ := hpowers

/-- Equation (27): the absolute coefficient sum has exponential growth. -/
lemma sum_abs_gCoeff_le (K : ℕ) (hK : 2 ≤ K) :
    (∑ ell ∈ Finset.range (K - 1), |gCoeff K ell|) ≤
      (K : ℝ) * (2 : ℝ) ^ (4 * K) := by
  calc
    _ ≤ ∑ _ell ∈ Finset.range (K - 1), (2 : ℝ) ^ (4 * K) := by
      gcongr with ell hell
      exact abs_gCoeff_le_pow_four_degree hK (Finset.mem_range.mp hell)
    _ = ((K - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * K) := by simp
    _ ≤ (K : ℝ) * (2 : ℝ) ^ (4 * K) := by
      gcongr
      omega

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

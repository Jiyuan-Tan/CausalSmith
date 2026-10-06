module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.GKSmallDegree

/-! Generic coefficient form of the reciprocal-polynomial residual. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

/-- Coefficients of the squared multiple-angle residual polynomial. -/
@[expose] noncomputable def gResidualCoeff (K r : ℕ) : ℝ :=
  (-1 : ℝ) ^ r * 2 ^ (2 * r + 1) *
    (Nat.choose (K + r + 1) (2 * r + 2) : ℝ) /
    ((K : ℝ) * (K + r + 1 : ℕ))

lemma gResidualCoeff_def (K r : ℕ) :
    gResidualCoeff K r =
      (-1 : ℝ) ^ r * 2 ^ (2 * r + 1) *
        (Nat.choose (K + r + 1) (2 * r + 2) : ℝ) /
        ((K : ℝ) * (K + r + 1 : ℕ)) := rfl

/-- The constant residual coefficient is one at every positive degree. -/
private lemma cast_choose_succ_two (K : ℕ) :
    (Nat.choose (K + 1) 2 : ℝ) = (K + 1 : ℕ) * K / 2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [show K + 1 + 1 = (K + 1) + 1 by omega,
        Nat.choose_succ_succ]
      push_cast
      rw [ih]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
      ring

lemma gResidualCoeff_zero (K : ℕ) (hK : 0 < K) :
    gResidualCoeff K 0 = 1 := by
  simp only [gResidualCoeff, pow_zero, one_mul]
  rw [cast_choose_succ_two]
  push_cast
  field_simp
  ring

/-- Each nonconstant residual coefficient is the negative of the corresponding
coefficient of `GK`. -/
lemma gResidualCoeff_succ (K r : ℕ) :
    gResidualCoeff K (r + 1) = -gCoeff K r := by
  unfold gResidualCoeff gCoeff
  rw [pow_succ]
  push_cast
  ring

/-- Residual coefficients vanish from degree `K` onward. -/
lemma gResidualCoeff_eq_zero_of_le {K r : ℕ} (hKr : K ≤ r) :
    gResidualCoeff K r = 0 := by
  unfold gResidualCoeff
  rw [Nat.choose_eq_zero_of_lt]
  · ring
  · omega

/-- Generic coefficient identity underlying equation (21). -/
lemma one_sub_mul_GK_eq_residual_sum (K : ℕ) (hK : 0 < K) (x : ℝ) :
    1 - x * GK K x =
      ∑ r ∈ Finset.range K, gResidualCoeff K r * x ^ r := by
  have hKeq : K = (K - 1) + 1 := by omega
  rw [hKeq, Finset.sum_range_succ', ← hKeq]
  rw [gResidualCoeff_zero K hK]
  simp only [pow_zero, mul_one]
  unfold GK
  rw [Finset.mul_sum]
  simp_rw [gResidualCoeff_succ, pow_succ]
  simp only [sub_eq_add_neg]
  rw [add_comm]
  apply congrArg (fun y : ℝ => y + 1)
  calc
    -(∑ r ∈ Finset.range (K - 1), x * (gCoeff K r * x ^ r)) =
        ∑ r ∈ Finset.range (K - 1), -(x * (gCoeff K r * x ^ r)) := by
      rw [Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

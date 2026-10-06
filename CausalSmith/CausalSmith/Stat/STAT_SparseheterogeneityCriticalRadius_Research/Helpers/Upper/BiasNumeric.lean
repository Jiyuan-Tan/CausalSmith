module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyLightEnvelope

/-! Elementary numerical inequalities used to sum the three bias regimes. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

lemma exp_neg_natCast_le_inv (K : ℕ) (hK : 0 < K) :
    Real.exp (-(K : ℝ)) ≤ 1 / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKexp : (K : ℝ) ≤ Real.exp (K : ℝ) := by
    linarith [Real.add_one_le_exp (K : ℝ)]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le hKr hKexp

lemma exp_neg_sixteen_mul_le_inv (K : ℕ) (hK : 0 < K) :
    Real.exp (-16 * (K : ℝ)) ≤ 1 / (K : ℝ) := by
  calc
    _ ≤ Real.exp (-(K : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith
    _ ≤ _ := exp_neg_natCast_le_inv K hK

lemma exp_neg_sixteen_mul_le_inv_sq (K : ℕ) (hK : 0 < K) :
    Real.exp (-16 * (K : ℝ)) ≤ (1 / (K : ℝ)) ^ 2 := by
  have hhalf : Real.exp (-8 * (K : ℝ)) ≤ 1 / (K : ℝ) := by
    calc
      _ ≤ Real.exp (-(K : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        linarith
      _ ≤ _ := exp_neg_natCast_le_inv K hK
  have hhalf0 : 0 ≤ Real.exp (-8 * (K : ℝ)) := Real.exp_nonneg _
  have hinv0 : 0 ≤ 1 / (K : ℝ) := by positivity
  calc
    _ = Real.exp (-8 * (K : ℝ)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := (sq_le_sq₀ hhalf0 hinv0).mpr hhalf

lemma light_classifier_exp_le_inv (K : ℕ) (hK : 0 < K) :
    Real.exp ((1 - Real.log 4) * (256 * K : ℕ)) ≤ 1 / (K : ℝ) := by
  have hlog : (5 / 4 : ℝ) ≤ Real.log 4 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_gt_d9]
  calc
    _ ≤ Real.exp (-16 * (K : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hcoef : 1 - Real.log 4 ≤ (-1 / 4 : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef
        (show (0 : ℝ) ≤ 256 * K by positivity)
      nlinarith
    _ ≤ _ := exp_neg_sixteen_mul_le_inv K hK

/-- Exponential classifier decay absorbs the polynomial factor in the heavy
regime. -/
lemma heavy_polynomial_decay (K : ℕ) (hK : 0 < K) {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (-512 * (K : ℝ) * y) *
        ((2 : ℝ) ^ (4 * K) * y ^ K) ≤
      Real.exp (-16 * (K : ℝ)) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hpow2 : (2 : ℝ) ^ (4 * K) =
      Real.exp ((4 * K : ℕ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
  have hpowy : y ^ K = Real.exp ((K : ℝ) * Real.log y) := by
    rw [Real.exp_nat_mul, Real.exp_log hypos]
  rw [hpow2, hpowy, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hKr : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith [mul_nonneg hKr (sub_nonneg.mpr hy)]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

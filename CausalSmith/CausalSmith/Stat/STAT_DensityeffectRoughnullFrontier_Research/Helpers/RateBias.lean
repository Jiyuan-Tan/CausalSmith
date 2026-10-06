module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateArithmetic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Geometric control of the sparse correction bias in equations (50)--(51).
The bounds retain the frozen ranks and have constants independent of the band count.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The sparse dyadic quotient is exact as a real quotient on the used bands. -/
-- @node: tuned_sparse_rank_cast_eq
lemma tuned_sparse_rank_cast_eq (m t : ℕ) (ht : t ≤ tunedT m) :
    ((tunedK m / 2 ^ (5 * t) : ℕ) : ℝ) =
      (tunedL m : ℝ) ^ 10 / (2 : ℝ) ^ (5 * t) := by
  have he : (tunedK m / 2 ^ (5 * t)) * 2 ^ (5 * t) = tunedK m := by
    rw [tunedK_quotient_eq m t ht, ← pow_add, Nat.sub_add_cancel (by omega),
      ← tunedK_eq_pow_tunedT]
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ (5 * t) ≠ 0)).2
  exact_mod_cast he

/-- Taking the inverse fifth power of the sparse rank gives its exact dyadic decay. -/
-- @node: tuned_sparse_rank_inverse_fifth
lemma tuned_sparse_rank_inverse_fifth (m t : ℕ) (ht : t ≤ tunedT m) :
    (((tunedK m / 2 ^ (5 * t) : ℕ) : ℝ)) ^ (-1 / 5 : ℝ) =
      (tunedL m : ℝ) ^ (-2 : ℤ) * (2 : ℝ) ^ t := by
  have hL : (0 : ℝ) < tunedL m := by
    simp only [tunedL, Nat.cast_pow, Nat.cast_ofNat]; positivity
  rw [tuned_sparse_rank_cast_eq m t ht,
    Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul hL.le,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ((5 * t : ℕ) : ℝ) * (-1 / 5 : ℝ) = -(t : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  norm_num

/-- The maximum with the pilot rank can only reduce the inverse-power bias. -/
-- @node: tunedKt_inverse_fifth_le
lemma tunedKt_inverse_fifth_le (m t : ℕ) (ht : t ≤ tunedT m) (htpos : 0 < t) :
    (tunedKt m t : ℝ) ^ (-1 / 5 : ℝ) ≤
      (tunedL m : ℝ) ^ (-2 : ℤ) * (2 : ℝ) ^ t := by
  rw [← tuned_sparse_rank_inverse_fifth m t ht]
  apply Real.rpow_le_rpow_of_nonpos
  · rw [tunedK_quotient_eq m t ht, Nat.cast_pow, Nat.cast_ofNat]; positivity
  · exact_mod_cast (show tunedK m / 2 ^ (5 * t) ≤ tunedKt m t by
      simp only [tunedKt, if_neg (by omega : t ≠ 0)]; exact le_max_right _ _)
  · norm_num

/-- Each high-band bias summand is bounded by a geometric term of ratio one half. -/
-- @node: tuned_high_band_bias_term_le
lemma tuned_high_band_bias_term_le (m t : ℕ) (ht : t < tunedT m) :
    (tunedKt m (t + 1) : ℝ) ^ (-1 / 5 : ℝ) /
        ((2 ^ t * tunedL m : ℕ) : ℝ) ^ 2 ≤
      2 * (tunedL m : ℝ) ^ (-4 : ℤ) * (1 / (2 : ℝ)) ^ t := by
  have hL : (0 : ℝ) < tunedL m := by
    simp only [tunedL, Nat.cast_pow, Nat.cast_ofNat]; positivity
  calc
    _ ≤ ((tunedL m : ℝ) ^ (-2 : ℤ) * (2 : ℝ) ^ (t + 1)) /
        ((2 ^ t * tunedL m : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (tunedKt_inverse_fifth_le m (t + 1) (by omega)
        (by omega)) (by positivity)
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ,
        zpow_neg, zpow_ofNat, one_div, inv_pow]
      field_simp


/-- Summing the high-band bias has no factor depending on the number of bands. -/
-- @node: tuned_high_band_bias_sum_le
lemma tuned_high_band_bias_sum_le (m : ℕ) :
    (∑ t ∈ Finset.range (tunedT m), (tunedKt m (t + 1) : ℝ) ^ (-1 / 5 : ℝ) /
        ((2 ^ t * tunedL m : ℕ) : ℝ) ^ 2) ≤
      4 * (tunedL m : ℝ) ^ (-4 : ℤ) := by
  calc
    _ ≤ ∑ t ∈ Finset.range (tunedT m),
        2 * (tunedL m : ℝ) ^ (-4 : ℤ) * (1 / (2 : ℝ)) ^ t :=
      Finset.sum_le_sum (fun t ht => tuned_high_band_bias_term_le m t
        (Finset.mem_range.mp ht))
    _ = 2 * (tunedL m : ℝ) ^ (-4 : ℤ) *
        (∑ t ∈ Finset.range (tunedT m), (1 / (2 : ℝ)) ^ t) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le (tunedT m))
        (show 0 ≤ 2 * (tunedL m : ℝ) ^ (-4 : ℤ) by positivity)
      linarith

/-- The square root of the entire high-band bias is at most twice L inverse squared. -/
-- @node: tuned_high_band_bias_sqrt_le
lemma tuned_high_band_bias_sqrt_le (m : ℕ) :
    Real.sqrt (∑ t ∈ Finset.range (tunedT m),
      (tunedKt m (t + 1) : ℝ) ^ (-1 / 5 : ℝ) /
        ((2 ^ t * tunedL m : ℕ) : ℝ) ^ 2) ≤
      2 * (tunedL m : ℝ) ^ (-2 : ℤ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have he : (2 * (tunedL m : ℝ) ^ (-2 : ℤ)) ^ 2 =
      4 * (tunedL m : ℝ) ^ (-4 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat]; ring
  rw [he]
  exact tuned_high_band_bias_sum_le m

/-- The initial correction rank has exactly the balanced inverse-square bias. -/
-- @node: tunedK_inverse_fifth_eq
lemma tunedK_inverse_fifth_eq (m : ℕ) :
    (tunedK m : ℝ) ^ (-1 / 5 : ℝ) = (tunedL m : ℝ) ^ (-2 : ℤ) := by
  rw [tunedK, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
  norm_num

/-- Downward rounding costs only a fixed factor for the third-order inverse-power bias. -/
-- @node: tunedQ_inverse_fifth_le
lemma tunedQ_inverse_fifth_le (m : ℕ) (hm : 1 ≤ m) :
    (tunedQ m : ℝ) ^ (-1 / 5 : ℝ) ≤
      (2 : ℝ) ^ (1 / 5 : ℝ) * (m : ℝ) ^ (-1 / 5 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hhalf : (m : ℝ) / 2 ≤ tunedQ m := by
    have h := roleSize_lt_two_mul_tunedQ m
    linarith
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (m : ℝ) / 2)
    hhalf (by norm_num : (-1 / 5 : ℝ) ≤ 0)
  rw [Real.div_rpow hmpos.le (by norm_num),
    show (-1 / 5 : ℝ) = -(1 / 5 : ℝ) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
  simpa only [mul_comm, neg_div] using h

/-- The frozen bias allowance reduces to the three terms of equation (51). -/
-- @node: tuned_bias_allowance_le_components
lemma tuned_bias_allowance_le_components (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (m : ℕ) (hm : 1 ≤ m) :
    BAllow C h m (tunedK m) (tunedL m) (tunedT m) (tunedQ m) (tunedKt m) ≤
      C * (3 * (tunedL m : ℝ) ^ (-2 : ℤ) + h ^ 4 +
        (2 : ℝ) ^ (1 / 5 : ℝ) * h * (m : ℝ) ^ (-1 / 5 : ℝ)) := by
  rw [BAllow, if_neg (by omega : m ≠ 0), tunedK_inverse_fifth_eq]
  apply mul_le_mul_of_nonneg_left _ hC
  have hsum := tuned_high_band_bias_sqrt_le m
  have hq := mul_le_mul_of_nonneg_left (tunedQ_inverse_fifth_le m hm) hh
  nlinarith

/-- The initial outcome bias is already at the exact role-size norm rate. -/
-- @node: tunedL_inverse_square_role_rate
lemma tunedL_inverse_square_role_rate (m : ℕ) (hm : 1 ≤ m) :
    (tunedL m : ℝ) ^ (-2 : ℤ) ≤ (m : ℝ) ^ (-8 / 29 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hmpos _)
    (tunedL_rpow_lower m hm) (by norm_num : (-2 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hmpos.le] at h
  norm_num at h
  simpa only [zpow_neg, zpow_ofNat, neg_div] using h

/-- The public tuned bias satisfies the role-size reduction in equation (51),
with its actual pilot allowance and the fixed moment multiplier. -/
-- @node: tunedB_role_bias_components
lemma tunedB_role_bias_components (n : ℕ) (hn : 3 ≤ roleSize n) :
    let m := roleSize n
    let h := hAllow (2 ^ 16) m (tunedMx m) (tunedMy m)
    tunedB n ≤ (2 : ℝ) ^ 24 * (3 * (m : ℝ) ^ (-8 / 29 : ℝ) + h ^ 4 +
      (2 : ℝ) ^ (1 / 5 : ℝ) * h * (m : ℝ) ^ (-1 / 5 : ℝ)) := by
  dsimp only
  have hh : 0 ≤ hAllow (2 ^ 16) (roleSize n) (tunedMx (roleSize n))
      (tunedMy (roleSize n)) := by
    rw [hAllow, if_neg (by omega : ¬ roleSize n < 3)]
    positivity
  have h := tuned_bias_allowance_le_components (2 ^ 24) _ (by positivity) hh
    (roleSize n) (by omega)
  change tunedB n ≤ _ at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hL := tunedL_inverse_square_role_rate (roleSize n) (by omega)
  linarith

end CausalSmith.Stat.DensityEffectRoughNull

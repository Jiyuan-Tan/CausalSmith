module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.BandCovarianceTrace
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateArithmetic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Geometric summation of the sparse correction trace and the projection-error rate,
as used in equations (54)--(55) of the sharp-frontier proof.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A sparse correction rank loses at least one dyadic factor per band. -/
-- @node: tuned_sparse_rank_le
lemma tuned_sparse_rank_le (m t : ℕ) :
    ((tunedK m / 2 ^ (5 * (t + 1)) : ℕ) : ℝ) ≤
      (tunedK m : ℝ) / (2 : ℝ) ^ (t + 1) := by
  calc
    _ ≤ (tunedK m : ℝ) / ((2 ^ (5 * (t + 1)) : ℕ) : ℝ) := Nat.cast_div_le
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      norm_cast
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The maximum defining a correction rank costs at most the sum of squared ranks. -/
-- @node: tunedKt_succ_sq_le
lemma tunedKt_succ_sq_le (m t : ℕ) :
    (tunedKt m (t + 1) : ℝ) ^ 2 ≤ (tunedMx m : ℝ) ^ 2 +
      ((tunedK m : ℝ) / (2 : ℝ) ^ (t + 1)) ^ 2 := by
  have h := tuned_sparse_rank_le m t
  have hs := pow_le_pow_left₀ (by positivity) h 2
  simp only [tunedKt, Nat.add_one_ne_zero, if_false, Nat.cast_max]
  rcases le_total (tunedMx m : ℝ) ((tunedK m / 2 ^ (5 * (t + 1)) : ℕ) : ℝ) with hx | hx
  · rw [max_eq_right hx]
    exact hs.trans (le_add_of_nonneg_left (by positivity))
  · rw [max_eq_left hx]
    exact le_add_of_nonneg_right (by positivity)

/-- After multiplication by band dimension the sparse contribution decays geometrically. -/
-- @node: tuned_sparse_band_trace_le
lemma tuned_sparse_band_trace_le (m t : ℕ) :
    (bandDimension (tunedL m) (t + 1) : ℝ) *
      ((tunedK m : ℝ) / (2 : ℝ) ^ (t + 1)) ^ 2 =
      (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 / 4 * (1 / (2 : ℝ)) ^ t := by
  simp only [bandDimension, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ, div_pow]
  field_simp
  ring

/-- The complete correction trace has the two contributions in equation (54),
with a constant independent of the number of bands. -/
-- @node: tuned_band_trace_bound
lemma tuned_band_trace_bound (m : ℕ) :
    (∑ t ∈ Finset.range (tunedT m + 1),
      (bandDimension (tunedL m) t : ℝ) * (tunedKt m t : ℝ) ^ 2) ≤
      2 * (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 +
        (tunedJ m : ℝ) * (tunedMx m : ℝ) ^ 2 := by
  have hdim : (∑ t ∈ Finset.range (tunedT m + 1),
      (bandDimension (tunedL m) t : ℝ)) = (tunedJ m : ℝ) := by
    exact_mod_cast (sum_bandDimension (tunedL m) (tunedT m)).trans
      (tunedJ_eq_multiband_rank m).symm
  have hhigh : (∑ t ∈ Finset.range (tunedT m),
      (bandDimension (tunedL m) (t + 1) : ℝ) * (tunedKt m (t + 1) : ℝ) ^ 2) ≤
      (∑ t ∈ Finset.range (tunedT m),
        (bandDimension (tunedL m) (t + 1) : ℝ) * (tunedMx m : ℝ) ^ 2) +
        (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 / 2 := by
    calc
      _ ≤ ∑ t ∈ Finset.range (tunedT m),
          (bandDimension (tunedL m) (t + 1) : ℝ) *
            ((tunedMx m : ℝ) ^ 2 + ((tunedK m : ℝ) / (2 : ℝ) ^ (t + 1)) ^ 2) :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left
          (tunedKt_succ_sq_le m t) (by positivity))
      _ = (∑ t ∈ Finset.range (tunedT m),
          (bandDimension (tunedL m) (t + 1) : ℝ) * (tunedMx m : ℝ) ^ 2) +
          (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 / 4 *
            (∑ t ∈ Finset.range (tunedT m), (1 / (2 : ℝ)) ^ t) := by
        simp_rw [mul_add, Finset.sum_add_distrib, tuned_sparse_band_trace_le]
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have hg := mul_le_mul_of_nonneg_left (sum_geometric_two_le (tunedT m))
          (show 0 ≤ (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 / 4 by positivity)
        linarith
  rw [Finset.sum_range_succ'] at hdim ⊢
  simp only [show bandDimension (tunedL m) 0 = tunedL m from rfl, tunedKt_zero] at hdim ⊢
  rw [← Finset.sum_mul] at hhigh
  nlinarith [sq_nonneg (tunedMx m : ℝ),
    mul_nonneg (Nat.cast_nonneg (tunedL m) : (0 : ℝ) ≤ tunedL m)
      (sq_nonneg (tunedK m : ℝ))]

/-- The outcome projection remainder already fits the exact role-size rate. -/
-- @node: tunedJ_role_rate_bound
lemma tunedJ_role_rate_bound (m : ℕ) (hm : 1 ≤ m) :
    (tunedJ m : ℝ) ^ (-2 : ℤ) ≤ (m : ℝ) ^ (-16 / 29 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hLpos : (0 : ℝ) < tunedL m := by simp only [tunedL, Nat.cast_pow, Nat.cast_ofNat]; positivity
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hmpos _)
    (tunedL_rpow_lower m hm) (by norm_num : (-4 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hmpos.le] at h
  norm_num at h
  rw [tunedJ, Nat.cast_pow, ← Real.rpow_intCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
  norm_num
  exact h

/-- Role-size rounding changes only the constant in the projection remainder rate. -/
-- @node: tunedJ_frontier_rate_bound
lemma tunedJ_frontier_rate_bound (n : ℕ) (hn : 1 ≤ roleSize n) :
    (tunedJ (roleSize n) : ℝ) ^ (-2 : ℤ) ≤
      (26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n := by
  apply (tunedJ_role_rate_bound _ hn).trans
  simpa only [neg_div, neg_neg, frontierRate] using
    roleSize_rpow_le_sampleSize_rpow n hn (-16 / 29) (by norm_num)

/-- Upward rounding bounds the final outcome rank by four times its balancing power. -/
-- @node: tunedJ_rpow_upper
lemma tunedJ_rpow_upper (m : ℕ) (hm : 1 ≤ m) :
    (tunedJ m : ℝ) ≤ 4 * (m : ℝ) ^ (8 / 29 : ℝ) := by
  have h := pow_le_pow_left₀ (by positivity) (tunedL_rpow_upper m hm).le 2
  simpa only [tunedJ, Nat.cast_pow, mul_pow,
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ m),
    show (4 / 29 : ℝ) * (2 : ℕ) = 8 / 29 by norm_num,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- The low-band squared trace is governed by the twenty-first power of L. -/
-- @node: tuned_low_band_trace_rpow_upper
lemma tuned_low_band_trace_rpow_upper (m : ℕ) (hm : 1 ≤ m) :
    (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 ≤
      (2 : ℝ) ^ 21 * (m : ℝ) ^ (84 / 29 : ℝ) := by
  have h := pow_le_pow_left₀ (by positivity) (tunedL_rpow_upper m hm).le 21
  have he : (tunedL m : ℝ) * (tunedK m : ℝ) ^ 2 = (tunedL m : ℝ) ^ 21 := by
    simp only [tunedK, Nat.cast_pow, ← pow_mul]
    ring
  rw [he]
  simpa only [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ m),
    show (4 / 29 : ℝ) * (21 : ℕ) = 84 / 29 by norm_num] using h

/-- The ordinary final-rank sampling variance is strictly below the leading squared rate. -/
-- @node: tunedJ_div_role_sq_bound
lemma tunedJ_div_role_sq_bound (m : ℕ) (hm : 1 ≤ m) :
    (tunedJ m : ℝ) / (m : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ (-32 / 29 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := div_le_div_of_nonneg_right (tunedJ_rpow_upper m hm)
    (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)
  have he : (m : ℝ) ^ (8 / 29 : ℝ) / (m : ℝ) ^ 2 = (m : ℝ) ^ (-50 / 29 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hmpos]
    norm_num
  have hp : (m : ℝ) ^ (-50 / 29 : ℝ) ≤ (m : ℝ) ^ (-32 / 29 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by norm_num)
  calc
    _ ≤ 4 * ((m : ℝ) ^ (8 / 29 : ℝ) / (m : ℝ) ^ 2) := by simpa only [mul_div_assoc] using h
    _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hp (by norm_num)

/-- Equation (54), scaled by the fourth inverse role size, has the squared sharp rate. -/
-- @node: tuned_scaled_trace_rate_bound
lemma tuned_scaled_trace_rate_bound (m : ℕ) (hm : 3 ≤ m) :
    (m : ℝ) ^ (-4 : ℤ) * (∑ t ∈ Finset.range (tunedT m + 1),
      (bandDimension (tunedL m) t : ℝ) * (tunedKt m t : ℝ) ^ 2) ≤
      ((2 : ℝ) ^ 22 + 4) * (m : ℝ) ^ (-32 / 29 : ℝ) := by
  have hmone : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmx : (tunedMx m : ℝ) ≤ m := by exact_mod_cast (tuned_rank_compatibility m hm).1
  have hmx2 := pow_le_pow_left₀ (by positivity) hmx 2
  have hlow := mul_le_mul_of_nonneg_left (tuned_low_band_trace_rpow_upper m hmone)
    (show 0 ≤ (m : ℝ) ^ (-4 : ℤ) by positivity)
  have he : (m : ℝ) ^ (-4 : ℤ) * (m : ℝ) ^ (84 / 29 : ℝ) =
      (m : ℝ) ^ (-32 / 29 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hmpos]
    norm_num
  have hlow' : (m : ℝ) ^ (-4 : ℤ) * ((tunedL m : ℝ) * (tunedK m : ℝ) ^ 2) ≤
      (2 : ℝ) ^ 21 * (m : ℝ) ^ (-32 / 29 : ℝ) := by
    rw [mul_left_comm ((m : ℝ) ^ (-4 : ℤ)) ((2 : ℝ) ^ 21), he] at hlow
    exact hlow
  have hhigh := mul_le_mul_of_nonneg_left hmx2
    (show 0 ≤ (m : ℝ) ^ (-4 : ℤ) * (tunedJ m : ℝ) by positivity)
  have hid : (m : ℝ) ^ (-4 : ℤ) * (tunedJ m : ℝ) * (m : ℝ) ^ 2 =
      (tunedJ m : ℝ) / (m : ℝ) ^ 2 := by
    simp only [zpow_neg, zpow_ofNat]
    field_simp
  rw [hid] at hhigh
  have hhigh' := hhigh.trans (tunedJ_div_role_sq_bound m hmone)
  have htotal := mul_le_mul_of_nonneg_left (tuned_band_trace_bound m)
    (show 0 ≤ (m : ℝ) ^ (-4 : ℤ) by positivity)
  nlinarith

/-- The frozen trace allowance satisfies equation (55) at every nontrivial role size. -/
-- @node: tunedV_sqrt_role_rate_bound
lemma tunedV_sqrt_role_rate_bound (n : ℕ) (hn : 3 ≤ roleSize n) :
    Real.sqrt (tunedV n) ≤ (2 : ℝ) ^ 36 *
      (roleSize n : ℝ) ^ (-16 / 29 : ℝ) := by
  let m := roleSize n
  have hm : 3 ≤ m := hn
  have hmone : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hJ := tunedJ_div_role_sq_bound m hmone
  have htrace := tuned_scaled_trace_rate_bound m hm
  have hv : tunedV n ≤ (2 : ℝ) ^ 72 * (m : ℝ) ^ (-32 / 29 : ℝ) := by
    simp only [tunedV, VAllow, if_neg (show roleSize n ≠ 0 by omega)]
    change 2 * ((2 : ℝ) ^ 24) ^ 2 *
      ((tunedJ m : ℝ) / (m : ℝ) ^ 2 + (m : ℝ) ^ (-4 : ℤ) * _) ≤ _
    have h := mul_le_mul_of_nonneg_left (add_le_add hJ htrace)
      (show 0 ≤ 2 * ((2 : ℝ) ^ 24) ^ 2 by positivity)
    have hp := Real.rpow_nonneg hmpos.le (-32 / 29 : ℝ)
    norm_num at h ⊢
    nlinarith
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, hv.trans_eq ?_⟩
  rw [mul_pow, ← Real.rpow_mul_natCast hmpos.le]
  norm_num

/-- Role-size conversion preserves the sharp square-root trace rate. -/
-- @node: tunedV_sqrt_frontier_rate_bound
lemma tunedV_sqrt_frontier_rate_bound (n : ℕ) (hn : 3 ≤ roleSize n) :
    Real.sqrt (tunedV n) ≤ ((2 : ℝ) ^ 36 * (26 : ℝ) ^ (16 / 29 : ℝ)) *
      frontierRate n := by
  have hrole := roleSize_rpow_le_sampleSize_rpow n (by omega : 1 ≤ roleSize n)
    (-16 / 29) (by norm_num)
  have hrole' : (roleSize n : ℝ) ^ (-16 / 29 : ℝ) ≤
      (26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n := by
    simpa only [neg_div, neg_neg, frontierRate] using hrole
  calc
    _ ≤ (2 : ℝ) ^ 36 * (roleSize n : ℝ) ^ (-16 / 29 : ℝ) := tunedV_sqrt_role_rate_bound n hn
    _ ≤ (2 : ℝ) ^ 36 * ((26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n) :=
      mul_le_mul_of_nonneg_left hrole' (by positivity)
    _ = _ := by ring

end CausalSmith.Stat.DensityEffectRoughNull

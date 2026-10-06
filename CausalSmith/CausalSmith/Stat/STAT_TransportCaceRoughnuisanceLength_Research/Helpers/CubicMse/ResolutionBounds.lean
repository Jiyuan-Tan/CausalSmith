module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Blocks

/-! # Dyadic resolutions and the deterministic pilot bias rate

These bounds implement equation (1) of the marked-cubic MSE proof, including
its exact floor-based resolutions and the block-size conversion to sample size.
-/

public section

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Every block is nonempty above the threshold.  Under [the displayed assumptions and inputs](hyp:n,hn,b), [the stated conclusion holds](goal). -/
-- @node: blockSize_pos_of_threshold
lemma blockSize_pos_of_threshold (n : ℕ) (hn : threshold ≤ n) (b : Fin 4) :
    0 < blockSize n b := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  exact_mod_cast lt_of_lt_of_le (div_pos hnpos (by norm_num)) (block_size_lower n hn b)

/-- The exact block size never exceeds the sample size.  Under [the displayed assumptions and inputs](hyp:n,b), [the stated conclusion holds](goal). -/
-- @node: blockSize_le_sampleSize
lemma blockSize_le_sampleSize (n : ℕ) (b : Fin 4) : blockSize n b ≤ n := by
  fin_cases b <;> simp only [blockSize] <;> omega

/-- Rounding down a base-two logarithm loses at most a factor of two.  Under [the displayed assumptions and inputs](hyp:n,hn,p,hp), [the stated conclusion holds](goal). -/
-- @node: dyadicResolution_power_bounds
lemma dyadicResolution_power_bounds (n : ℕ) (hn : threshold ≤ n)
    (p : ℝ) (hp : 0 ≤ p) :
    (blockSize n 0 : ℝ) ^ p / 2 ≤ (dyadicResolution n p : ℝ) ∧
      (dyadicResolution n p : ℝ) ≤ (blockSize n 0 : ℝ) ^ p := by
  have hmpos : (0 : ℝ) < blockSize n 0 :=
    Nat.cast_pos.mpr (blockSize_pos_of_threshold n hn 0)
  have hmone : (1 : ℝ) ≤ blockSize n 0 := by
    exact_mod_cast (blockSize_pos_of_threshold n hn 0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ := p * (Real.log (blockSize n 0 : ℝ) / Real.log 2)
  have hq : 0 ≤ q := mul_nonneg hp (div_nonneg (Real.log_nonneg hmone) hlog2.le)
  have heq : (2 : ℝ) ^ q = (blockSize n 0 : ℝ) ^ p := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hmpos]
    congr 1
    dsimp [q]
    field_simp
  have hlow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.floor_le hq)
  have hhigh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.lt_floor_add_one q).le
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_natCast, heq] at hhigh
  rw [Real.rpow_natCast, heq] at hlow
  simp only [dyadicResolution, if_neg (Nat.not_lt_of_ge hn), Nat.cast_pow,
    Nat.cast_ofNat]
  constructor
  · linarith
  · exact hlow

/-- The pilot resolution has exactly the bounds used for its moments.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: pilotResolution_power_bounds
lemma pilotResolution_power_bounds (n : ℕ) (hn : threshold ≤ n) :
    (blockSize n 0 : ℝ) ^ (4 / 5 : ℝ) / 2 ≤ (pilotResolution n : ℝ) ∧
      (pilotResolution n : ℝ) ≤ (blockSize n 0 : ℝ) ^ (4 / 5 : ℝ) := by
  exact dyadicResolution_power_bounds n hn (4 / 5) (by norm_num)

/-- The quadratic resolution has exactly the bounds used for its variance and bias.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: quadraticResolution_power_bounds
lemma quadraticResolution_power_bounds (n : ℕ) (hn : threshold ≤ n) :
    (blockSize n 0 : ℝ) ^ (4 / 3 : ℝ) / 2 ≤ (quadraticResolution n : ℝ) ∧
      (quadraticResolution n : ℝ) ≤ (blockSize n 0 : ℝ) ^ (4 / 3 : ℝ) := by
  exact dyadicResolution_power_bounds n hn (4 / 3) (by norm_num)

/-- The inverse pilot resolution supplies the deterministic eighth-power bias rate.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: pilotResolution_inv_le_sample_rate
lemma pilotResolution_inv_le_sample_rate (n : ℕ) (hn : threshold ≤ n) :
    1 / (pilotResolution n : ℝ) ≤
      2 * (5 : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hmpos : (0 : ℝ) < blockSize n 0 :=
    Nat.cast_pos.mpr (blockSize_pos_of_threshold n hn 0)
  have hKpos : (0 : ℝ) < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  have hlow := (pilotResolution_power_bounds n hn).1
  have hm := Real.rpow_le_rpow (div_pos hnpos (by norm_num)).le
    (block_size_lower n hn 0) (by norm_num : (0 : ℝ) ≤ 4 / 5)
  have hpow : (n : ℝ) ^ (4 / 5 : ℝ) / (5 : ℝ) ^ (4 / 5 : ℝ) / 2 ≤
      (pilotResolution n : ℝ) := by
    rw [← Real.div_rpow hnpos.le (by norm_num)]
    linarith
  have h5 : (0 : ℝ) < (5 : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hnPow : (0 : ℝ) < (n : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hnpos _
  rw [Real.rpow_neg hnpos.le, ← one_div]
  apply (div_le_iff₀ hKpos).2
  rw [show 2 * (5 : ℝ) ^ (4 / 5 : ℝ) * (1 / (n : ℝ) ^ (4 / 5 : ℝ)) *
      (pilotResolution n : ℝ) =
      (2 * (5 : ℝ) ^ (4 / 5 : ℝ) * (pilotResolution n : ℝ)) /
        (n : ℝ) ^ (4 / 5 : ℝ) by ring]
  apply (le_div_iff₀ hnPow).2
  have hmul := (div_le_iff₀ h5).mp ((div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hpow)
  nlinarith

/-- Every nonnegative power of the pilot fluctuation scale has its explicit sample-size rate.  Under [the displayed assumptions and inputs](hyp:n,hn,p,hp), [the stated conclusion holds](goal). -/
-- @node: pilotResolution_ratio_rpow_le
lemma pilotResolution_ratio_rpow_le (n : ℕ) (hn : threshold ≤ n)
    (p : ℝ) (hp : 0 ≤ p) :
    ((pilotResolution n : ℝ) / (blockSize n 0 : ℝ)) ^ p ≤
      (5 : ℝ) ^ (p / 5) * (n : ℝ) ^ (-(p / 5)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hmpos : (0 : ℝ) < blockSize n 0 :=
    Nat.cast_pos.mpr (blockSize_pos_of_threshold n hn 0)
  have hratio : (pilotResolution n : ℝ) / (blockSize n 0 : ℝ) ≤
      (blockSize n 0 : ℝ) ^ (-(1 / 5 : ℝ)) := by
    calc
      _ ≤ (blockSize n 0 : ℝ) ^ (4 / 5 : ℝ) / (blockSize n 0 : ℝ) :=
        div_le_div_of_nonneg_right (pilotResolution_power_bounds n hn).2 hmpos.le
      _ = _ := by
        nth_rw 2 [← Real.rpow_one (blockSize n 0 : ℝ)]
        rw [← Real.rpow_sub hmpos]
        norm_num
  have hpow := Real.rpow_le_rpow (by positivity :
      (0 : ℝ) ≤ (pilotResolution n : ℝ) / (blockSize n 0 : ℝ)) hratio hp
  rw [← Real.rpow_mul hmpos.le] at hpow
  have hexp : (-(1 / 5 : ℝ)) * p = -(p / 5) := by ring
  rw [hexp] at hpow
  have hsample := Real.rpow_le_rpow_of_nonpos (div_pos hnpos (by norm_num))
    (block_size_lower n hn 0) (by linarith : -(p / 5) ≤ 0)
  refine hpow.trans (hsample.trans_eq ?_)
  rw [Real.div_rpow hnpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
  field_simp

/-- Both histogram fluctuation terms in the eighth-moment roadmap are bounded at rate `n⁻⁴ᐟ⁵`.  Under [the displayed assumptions and inputs](hyp:n,hn), [the stated conclusion holds](goal). -/
-- @node: pilotResolution_eighth_fluctuation_scales
lemma pilotResolution_eighth_fluctuation_scales (n : ℕ) (hn : threshold ≤ n) :
    ((pilotResolution n : ℝ) / (blockSize n 0 : ℝ)) ^ (4 : ℕ) ≤
      (5 : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ)) ∧
    ((pilotResolution n : ℝ) / (blockSize n 0 : ℝ)) ^ (7 : ℕ) ≤
      (5 : ℝ) ^ (7 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  constructor
  · simpa only [Real.rpow_ofNat] using
      pilotResolution_ratio_rpow_le n hn 4 (by norm_num)
  · have h := pilotResolution_ratio_rpow_le n hn 7 (by norm_num)
    rw [Real.rpow_ofNat] at h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
    · norm_num

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

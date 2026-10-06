module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Blocks

/-! # Elementary bounds for the cubic dyadic resolution -/

@[expose] public section

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:n,hn), [the stated result about cubic resolution le block size holds](goal). -/

lemma cubicResolution_le_blockSize (n : ℕ) (hn : threshold ≤ n) :
    cubicResolution n ≤ blockSize n 0 := by
  have hnpos : (0 : ℝ) < n := by
    norm_num [threshold] at hn
    exact_mod_cast (show 0 < n by omega)
  have hm_lower := block_size_lower n hn 0
  have hmpos : (0 : ℝ) < blockSize n 0 :=
    lt_of_lt_of_le (div_pos hnpos (by norm_num)) hm_lower
  have hm_one : (1 : ℝ) ≤ blockSize n 0 := by
    norm_num [threshold] at hn
    norm_num [blockSize]
    omega
  have hlogm : 0 ≤ Real.log (blockSize n 0 : ℝ) := Real.log_nonneg hm_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ := Real.log (blockSize n 0 : ℝ) / Real.log 2
  have hq : 0 ≤ q := div_nonneg hlogm hlog2.le
  have hfloor : ((Nat.floor q : ℕ) : ℝ) ≤ q := Nat.floor_le hq
  have hrpow : (2 : ℝ) ^ ((Nat.floor q : ℕ) : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  have hpowq : (2 : ℝ) ^ q = blockSize n 0 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show Real.log 2 * q = Real.log (blockSize n 0 : ℝ) by
      dsimp [q]
      field_simp]
    exact Real.exp_log hmpos
  unfold cubicResolution dyadicResolution
  simp only [if_neg (Nat.not_lt_of_ge hn)]
  simp only [one_mul]
  change 2 ^ Nat.floor q ≤ blockSize n 0
  have hcast : ((2 ^ Nat.floor q : ℕ) : ℝ) ≤ (blockSize n 0 : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact hrpow.trans_eq hpowq
  exact_mod_cast hcast
/-- Given [the supplied inputs](hyp:n,hn), [the stated result about cubic resolution le n holds](goal). -/

lemma cubicResolution_le_n (n : ℕ) (hn : threshold ≤ n) :
    cubicResolution n ≤ n := by
  exact (cubicResolution_le_blockSize n hn).trans (by
    simp only [blockSize]
    omega)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

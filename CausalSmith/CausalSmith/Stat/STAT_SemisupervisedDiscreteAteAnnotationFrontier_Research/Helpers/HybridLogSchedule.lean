module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridCalibrationConstants

/-! Logarithmic comparisons for the paper's binary degree schedule. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma log_two_le_one : Real.log (2 : Real) ≤ 1 := by
  rw [← Real.log_exp 1]
  exact Real.strictMonoOn_log.monotoneOn (by norm_num) (Real.exp_pos 1)
    (by nlinarith [Real.exp_one_gt_d9])

/-- The binary length dominates the natural logarithmic scale.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma logEN_le_binLen (n : Nat) (hn : 1 ≤ n) :
    logEN n ≤ binLen n := by
  have hnR : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpow : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
  have hpowpos : 0 < ((2 : Real) ^ Nat.clog 2 n) := pow_pos (by norm_num) _
  have hlog : Real.log (n : Real) ≤
      Real.log ((2 : Real) ^ Nat.clog 2 n) :=
    Real.strictMonoOn_log.monotoneOn hnR hpowpos (by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hc : 0 ≤ (Nat.clog 2 n : Real) := by positivity
  have hmul : (Nat.clog 2 n : Real) * Real.log 2 ≤ Nat.clog 2 n := by
    nlinarith [log_two_le_one]
  rw [logEN, Real.log_mul (by positivity : Real.exp 1 ≠ 0) hnR.ne']
  simp only [Real.log_exp]
  norm_num [binLen]
  linarith

/-- Conversely, binary length is at most a fixed multiple of `log(e n)`.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma binLen_le_three_logEN (n : Nat) (hn : 1 ≤ n) :
    (binLen n : Real) ≤ 3 * logEN n := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [binLen, logEN]
  have hn2 : 2 ≤ n := by omega
  have hcpos : 0 < Nat.clog 2 n := Nat.clog_pos (by omega) (by omega)
  have hpow := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) (by omega : 1 < n)
  have hpowR : (0 : Real) < (2 ^ (Nat.clog 2 n - 1) : Nat) := by positivity
  have hnR : (0 : Real) < n := by positivity
  have hlog : Real.log ((2 ^ (Nat.clog 2 n - 1) : Nat) : Real) <
      Real.log (n : Real) := Real.strictMonoOn_log hpowR hnR (by exact_mod_cast hpow)
  rw [show (((2 ^ (Nat.clog 2 n - 1) : Nat) : Real)) =
      (2 : Real) ^ (Nat.clog 2 n - 1) by norm_num, Real.log_pow] at hlog
  have hlog2 : (1 / 2 : Real) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hcR : (1 : Real) ≤ Nat.clog 2 n := by exact_mod_cast hcpos
  have hscale : logEN n = 1 + Real.log (n : Real) := by
    rw [logEN, Real.log_mul (by positivity : Real.exp 1 ≠ 0) hnR.ne']
    simp
  norm_num [binLen]
  rw [hscale]
  rw [Nat.cast_sub (by omega : 1 ≤ Nat.clog 2 n)] at hlog
  push_cast at hlog
  nlinarith

/-- Once the unrounded target degree exceeds two, `Ldeg` is the floor branch.  [the stated conditions](hyp:h) [the stated conclusion](goal). -/
lemma Ldeg_eq_floor {n : Nat} (h : 2 ≤ cCirc * binLen n) :
    Ldeg n = Int.toNat ⌊cCirc * binLen n⌋ := by
  rw [Ldeg, max_eq_right]
  have hi : (2 : Int) ≤ ⌊cCirc * binLen n⌋ := by
    rw [Int.le_floor]
    exact_mod_cast h
  simpa using Int.toNat_le_toNat hi

/-- Elementary lower and upper bounds for the rounded degree.  [the stated conditions](hyp:h) [the stated conclusion](goal). -/
lemma Ldeg_bounds {n : Nat} (h : 2 ≤ cCirc * binLen n) :
    cCirc * binLen n / 2 ≤ (Ldeg n : Real) ∧
      (Ldeg n : Real) ≤ cCirc * binLen n := by
  have hf2 : (2 : Int) ≤ ⌊cCirc * binLen n⌋ := by
    rw [Int.le_floor]
    exact_mod_cast h
  have hf0 : (0 : Int) ≤ ⌊cCirc * binLen n⌋ := le_trans (by norm_num) hf2
  have hcast : ((Int.toNat ⌊cCirc * binLen n⌋ : Nat) : Real) =
      ((⌊cCirc * binLen n⌋ : Int) : Real) := by
    exact_mod_cast Int.toNat_of_nonneg hf0
  rw [Ldeg_eq_floor h, hcast]
  constructor
  · have hfloor := Int.lt_floor_add_one (cCirc * binLen n)
    have hx : (2 : Real) ≤ cCirc * binLen n := h
    have hfloorR : cCirc * binLen n <
        ((⌊cCirc * binLen n⌋ : Int) : Real) + 1 := by exact_mod_cast hfloor
    linarith
  · exact Int.floor_le _

/-- The target degree scale eventually exceeds the max/floor transition.  [the stated conclusion](goal). -/
lemma eventually_two_le_cCirc_binLen :
    ∀ᶠ n : Nat in Filter.atTop, 2 ≤ cCirc * binLen n := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 512 : Nat)] with n hn
  have hclog : 512 ≤ Nat.clog 2 n := by
    calc
      512 = Nat.clog 2 (2 ^ 512) := (Nat.clog_pow 2 512 (by omega)).symm
      _ ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hn
  have hclogR : (512 : Real) ≤ Nat.clog 2 n := by exact_mod_cast hclog
  norm_num [cCirc, binLen]
  linarith

/-- A twelfth power of the logarithmic schedule is eventually dominated by
the sample size.  [the stated conclusion](goal). -/
lemma eventually_logEN_pow_twelve_le :
    ∀ᶠ n : Nat in Filter.atTop, logEN n ^ 12 ≤ (n : Real) := by
  have hsmall : ∀ᶠ n : Nat in Filter.atTop,
      |Real.log (n : Real) ^ 12| ≤ (1 / 4096 : Real) * |(n : Real)| := by
    have hreal := (Real.isLittleO_pow_log_id_atTop (n := 12)).bound
      (by norm_num : (0 : Real) < 1 / 4096)
    exact tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [Filter.eventually_ge_atTop 3, hsmall] with n hn hlog
  have hnR : (0 : Real) < n := by positivity
  have hlogn : 1 ≤ Real.log (n : Real) := by
    rw [← Real.log_exp 1]
    apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hnR
    have hn3 : (3 : Real) ≤ n := by exact_mod_cast hn
    nlinarith [Real.exp_one_lt_d9]
  have hscale : logEN n = 1 + Real.log (n : Real) := by
    rw [logEN, Real.log_mul (by positivity : Real.exp 1 ≠ 0) hnR.ne']
    simp
  have htwo : logEN n ≤ 2 * Real.log (n : Real) := by rw [hscale]; linarith
  have hnonneg : 0 ≤ logEN n := by rw [hscale]; positivity
  have hp := pow_le_pow_left₀ hnonneg htwo 12
  rw [mul_pow] at hp
  norm_num at hp
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [abs_of_nonneg (pow_nonneg (Real.log_nonneg hn1) _),
    abs_of_nonneg hnR.le] at hlog
  calc
    logEN n ^ 12 ≤ 4096 * Real.log (n : Real) ^ 12 := hp
    _ ≤ (n : Real) := by nlinarith

/-- Consequently the rounded degree has polynomial powers negligible against
the sample size.  [the stated conclusion](goal). -/
lemma eventually_Ldeg_pow_twelve_le :
    ∀ᶠ n : Nat in Filter.atTop, (Ldeg n : Real) ^ 12 ≤ n := by
  filter_upwards [eventually_two_le_cCirc_binLen,
    eventually_logEN_pow_twelve_le, Filter.eventually_ge_atTop 1] with n hdeg hlog hn
  have hL := (Ldeg_bounds hdeg).2
  have hbin := binLen_le_three_logEN n hn
  have hnonneg : 0 ≤ (Ldeg n : Real) := by positivity
  have htarget : (Ldeg n : Real) ≤ logEN n := by
    have hlog0 : 0 ≤ logEN n := by
      rw [logEN]
      apply (Real.log_pos ?_).le
      have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
      calc
        1 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        _ ≤ Real.exp 1 * n :=
          (le_mul_iff_one_le_right (Real.exp_pos 1)).2 hnR
    rw [cCirc] at hL
    nlinarith
  exact (pow_le_pow_left₀ hnonneg htarget 12).trans hlog

/-- The deliberately small degree constant makes four powers of the
factorial-moment base fit below the sample size.  [the stated conditions](hyp:hdeg) [the stated conclusion](goal). -/
lemma starA_pow_four_Ldeg_lt {n : Nat}
    (hdeg : 2 ≤ cCirc * binLen n) :
    (starA : Real) ^ (4 * Ldeg n) < n := by
  have hn2 : 2 ≤ n := by
    by_contra hn
    interval_cases n <;> norm_num [binLen, cCirc] at hdeg
  have hL := (Ldeg_bounds hdeg).2
  have hclog : 52 * Ldeg n ≤ Nat.clog 2 n - 1 := by
    have hb : (512 : Real) ≤ binLen n := by
      rw [cCirc] at hdeg
      nlinarith
    have hc : ((Nat.clog 2 n : Nat) : Real) = binLen n - 1 := by
      simp [binLen]
    rw [cCirc] at hL
    have hcpos : 1 ≤ Nat.clog 2 n := Nat.one_le_iff_ne_zero.mpr (by
      exact ne_of_gt (Nat.clog_pos (by omega) (by omega)))
    have hr : ((52 * Ldeg n : Nat) : Real) ≤
        ((Nat.clog 2 n - 1 : Nat) : Real) := by
      rw [Nat.cast_sub hcpos]
      push_cast
      rw [hc]
      nlinarith
    exact_mod_cast hr
  have hbase : (starA : Real) ≤ 2 ^ 13 := by norm_num [starA]
  have hpow : (starA : Real) ^ (4 * Ldeg n) ≤
      (2 : Real) ^ (52 * Ldeg n) := by
    calc
      (starA : Real) ^ (4 * Ldeg n) ≤ (2 ^ 13 : Real) ^ (4 * Ldeg n) := by
        exact pow_le_pow_left₀ (by positivity) hbase _
      _ = (2 : Real) ^ (52 * Ldeg n) := by rw [← pow_mul]; congr 1; omega
  have hmono : (2 : Real) ^ (52 * Ldeg n) ≤
      (2 : Real) ^ (Nat.clog 2 n - 1) := by
    exact pow_le_pow_right₀ (by norm_num) hclog
  have hlast : (2 : Real) ^ (Nat.clog 2 n - 1) < n := by
    exact_mod_cast Nat.pow_pred_clog_lt_self (by omega : 1 < 2) (by omega : 1 < n)
  exact hpow.trans_lt (hmono.trans_lt hlast)

/-- C5's two moment tests hold eventually.  [the stated conclusion](goal). -/
lemma eventually_factorial_moment_tests :
    ∀ᶠ n : Nat in Filter.atTop,
      (Ldeg n : Real) ^ 4 * starA ^ (2 * Ldeg n) ≤ n ∧
      (Ldeg n : Real) ^ 6 * starA ^ (2 * Ldeg n) ≤ n := by
  filter_upwards [eventually_two_le_cCirc_binLen,
    eventually_Ldeg_pow_twelve_le] with n hdeg hL12
  have hA4 := (starA_pow_four_Ldeg_lt hdeg).le
  let X : Real := (Ldeg n : Real) ^ 6
  let Y : Real := (starA : Real) ^ (2 * Ldeg n)
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hn0 : 0 ≤ (n : Real) := by positivity
  have hXsq : X ^ 2 ≤ n := by simpa [X, ← pow_mul] using hL12
  have hYsq : Y ^ 2 ≤ n := by
    dsimp [Y]
    rw [← pow_mul]
    rw [show 2 * Ldeg n * 2 = 4 * Ldeg n by omega]
    exact hA4
  have hXY : X * Y ≤ n := by
    nlinarith [sq_nonneg (X - Y), sq_nonneg (X * Y - n)]
  constructor
  · have hL46 : (Ldeg n : Real) ^ 4 ≤ (Ldeg n : Real) ^ 6 := by
      have hL1 : (1 : Real) ≤ Ldeg n := by exact_mod_cast (show 1 ≤ Ldeg n by
        exact (by omega : 1 ≤ 2).trans (Ldeg_ge_two n))
      exact pow_le_pow_right₀ hL1 (by omega)
    exact (mul_le_mul_of_nonneg_right hL46 hY0).trans (by simpa [X, Y] using hXY)
  · simpa [X, Y] using hXY

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

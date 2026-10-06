module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridEventualCalibration

/-! Deterministic exponential absorption for heavy cells. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- A convenient explicit logarithmic bound for the factorial constant.  [the stated conclusion](goal). -/
lemma log_starA_le_thirteen : Real.log (starA : Real) ≤ 13 := by
  have hbase : (starA : Real) ≤ (2 : Real) ^ 13 := by norm_num [starA]
  have hApos : (0 : Real) < starA := by norm_num [starA]
  have hpowpos : (0 : Real) < 2 ^ 13 := pow_pos (by norm_num) _
  have hlog := Real.strictMonoOn_log.monotoneOn
    hApos hpowpos hbase
  rw [Real.log_pow] at hlog
  have := log_two_le_one
  norm_num at hlog
  nlinarith

/-- C22 with the explicit constants chosen by the calibration.  [the stated conditions](hyp:heps,hy) [the stated conclusion](goal). -/
lemma factorial_growth_mul_heavy_exp_le {eps y : Real} {L : Nat}
    (heps : 0 < eps) (hy : 1 ≤ y) :
    (starA : Real) ^ L * (1 + y) ^ (2 * L) *
        Real.exp (-(Hconst eps : Real) * L * y / 4) ≤
      Real.exp (-24 * L * y / cCirc) := by
  have hA : (0 : Real) < starA := by norm_num [starA]
  have hypos : 0 < 1 + y := by linarith
  have hlogy : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos hypos
    linarith
  have hH := (Hconst_spec heps).2.1
  have hc : 0 < cCirc := by norm_num [cCirc]
  have hL0 : 0 ≤ (L : Real) := by positivity
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hexponent :
      (L : Real) * Real.log (starA : Real) +
          (2 * L : Nat) * Real.log (1 + y) -
          (Hconst eps : Real) * L * y / 4 ≤
        -24 * L * y / cCirc := by
    norm_num [cCirc, Nat.cast_mul] at hH ⊢
    have hAlog := log_starA_le_thirteen
    have hLy : (L : Real) ≤ L * y := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hAlog hL0
    have h2 := mul_le_mul_of_nonneg_left hlogy
      (show (0 : Real) ≤ 2 * L by positivity)
    nlinarith [mul_nonneg hL0 hy0,
      mul_nonneg (sub_nonneg.mpr hH) (mul_nonneg hL0 hy0)]
  rw [show (starA : Real) ^ L =
      Real.exp ((L : Real) * Real.log (starA : Real)) by
        rw [Real.exp_nat_mul, Real.exp_log hA],
    show (1 + y) ^ (2 * L) =
      Real.exp (((2 * L : Nat) : Real) * Real.log (1 + y)) by
        rw [Real.exp_nat_mul, Real.exp_log hypos],
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hexponent using 1 <;> norm_num [Nat.cast_mul] <;> ring

/-- Polynomial forms of the two square-root comparisons in C34.  [the stated conditions](hyp:h4,h6) [the stated conclusion](goal). -/
lemma moment_tests_square_forms {n L : Nat}
    (h4 : (L : Real) ^ 4 * starA ^ (2 * L) ≤ n)
    (h6 : (L : Real) ^ 6 * starA ^ (2 * L) ≤ n) :
    (((L : Real) ^ 2 * starA ^ L) ^ 2 ≤ n) ∧
      (((L : Real) ^ 3 * starA ^ L) ^ 2 ≤ n) := by
  constructor
  · simpa [mul_pow, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using h4
  · simpa [mul_pow, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using h6

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

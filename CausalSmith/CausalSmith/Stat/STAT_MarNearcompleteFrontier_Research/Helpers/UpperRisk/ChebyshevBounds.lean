module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.Moments

/-! # Light-cell Chebyshev calibration obligations -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

/-- For [a positive sample size](hyp:_hn) and [a nonzero evaluation point](hyp:hz), [the polynomial quotient equals its displayed Chebyshev formula](goal). -/
lemma qPoly_eval_formula (n : ℕ) (_hn : 1 ≤ n) (z : ℝ) (hz : z ≠ 0) :
    (qPoly n).eval z =
      (1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
        (1 - 2 * z / polyThreshold n)) /
        (2 * (polyDegree n : ℝ) ^ 2 * z / polyThreshold n) := by
  let p : Polynomial ℝ := 1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
    (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)
  have hp0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [p, Polynomial.Chebyshev.T_eval_one]
  have hdiv := Polynomial.divX_mul_X_add p
  have heval := congrArg (Polynomial.eval z) hdiv
  simp only [Polynomial.eval_mul, Polynomial.eval_X, hp0, map_zero, add_zero] at heval
  have hB : polyThreshold n ≠ 0 := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    have he' : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hl : 0 < ell n := by exact Real.log_pos (by simpa [ell] using he')
    unfold polyThreshold
    positivity
  have hk : (polyDegree n : ℝ) ≠ 0 := by
    exact_mod_cast (show polyDegree n ≠ 0 by unfold polyDegree; omega)
  have hp_eval : p.eval z =
      1 - (Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).eval
        (1 - 2 * z / polyThreshold n) := by
    simp [p, Polynomial.eval_sub, Polynomial.eval_comp]
    congr 1
    field_simp
  change (p.divX * Polynomial.C (polyThreshold n / (2 * (polyDegree n : ℝ) ^ 2))).eval z = _
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hp_eval, ← heval]
  field_simp

end CausalSmith.Stat.MarNearcompleteFrontier

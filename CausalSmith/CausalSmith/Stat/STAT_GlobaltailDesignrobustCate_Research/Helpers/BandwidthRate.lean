module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Risk

/-! # Dyadic bandwidth rounding and rate balance

These lemmas implement equations (S6)--(S8) of the sharp-minimax roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

-- @node: effectiveDimension_pos
/-- The effective dimension is positive on the parameter domain. -/
lemma effectiveDimension_pos {d : ℕ} {γ : ℝ} (hd : 1 ≤ d) (hγ : 1 < γ) :
    0 < effectiveDimension d γ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold effectiveDimension
  exact div_pos (mul_pos hd' (by linarith)) (by linarith)

-- @node: dyadicWidth_rounding
/-- Rounding a positive width at most one down to a dyadic width loses less
than a factor of two. -/
lemma dyadicWidth_rounding {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w / 2 < dyadicWidth (Nat.ceil (Real.log w⁻¹ / Real.log 2)) ∧
      dyadicWidth (Nat.ceil (Real.log w⁻¹ / Real.log 2)) ≤ w := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log w⁻¹ / Real.log 2 := by
    apply div_nonneg _ hlog.le
    apply Real.log_nonneg
    exact (one_le_inv₀ hw).2 hw1
  have hp : (2 : ℝ) ^ Nat.ceil (Real.log w⁻¹ / Real.log 2) =
      Real.exp (Real.log 2 * (Nat.ceil (Real.log w⁻¹ / Real.log 2) : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have hlo : w⁻¹ ≤ (2 : ℝ) ^ Nat.ceil (Real.log w⁻¹ / Real.log 2) := by
    rw [hp, ← Real.exp_log (inv_pos.mpr hw)]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left
      (Nat.le_ceil (Real.log w⁻¹ / Real.log 2)) hlog.le
    simpa [mul_div_cancel₀ _ hlog.ne'] using this
  have hhi : (2 : ℝ) ^ Nat.ceil (Real.log w⁻¹ / Real.log 2) < 2 / w := by
    rw [hp]
    calc
      _ < Real.exp (Real.log 2 * (Real.log w⁻¹ / Real.log 2 + 1)) := by
        apply Real.exp_lt_exp.mpr
        exact mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one ha) hlog
      _ = 2 / w := by
        rw [mul_add, mul_div_cancel₀ _ hlog.ne', mul_one, Real.exp_add,
          Real.exp_log (inv_pos.mpr hw), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
  have hp0 : (0 : ℝ) < 2 ^ Nat.ceil (Real.log w⁻¹ / Real.log 2) := by positivity
  unfold dyadicWidth
  constructor
  · apply (lt_div_iff₀ hp0).2
    have := (lt_div_iff₀ hw).mp hhi
    nlinarith
  · apply (div_le_iff₀ hp0).2
    have := (div_le_iff₀ hw).mp (show 1 / w ≤ _ from by simpa only [one_div] using hlo)
    nlinarith

-- @node: rateBandwidth_bounds
/-- The chosen bandwidth lies between half the continuous balancing width
and that width, for every positive sample size. -/
lemma rateBandwidth_bounds {d n : ℕ} {β γ : ℝ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) :
    rateWidth d n β γ / 2 < rateBandwidth d n β γ ∧
      rateBandwidth d n β γ ≤ rateWidth d n β γ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := effectiveDimension_pos hd hγ
  apply dyadicWidth_rounding
  · unfold rateWidth
    exact Real.rpow_pos_of_pos hn' _
  · unfold rateWidth
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by
      have : 0 < 2 * β + effectiveDimension d γ := by linarith
      exact (div_neg_of_neg_of_pos (by norm_num) this).le)

-- @node: rateWidth_bias_eq
/-- Raising the continuous balancing width to the smoothness exponent gives
the target rate exactly. -/
lemma rateWidth_bias_eq {d n : ℕ} {β γ : ℝ} (hn : 1 ≤ n) :
    (rateWidth d n β γ) ^ β = rate d n β γ := by
  have hn' : (0 : ℝ) ≤ n := by positivity
  unfold rateWidth rate
  rw [← Real.rpow_mul hn']
  congr 1
  ring

-- @node: rateBandwidth_bias_le
/-- Dyadic rounding can only decrease the bias term. -/
lemma rateBandwidth_bias_le {d n : ℕ} {β γ : ℝ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) :
    (rateBandwidth d n β γ) ^ β ≤ rate d n β γ := by
  rw [← rateWidth_bias_eq hn]
  apply Real.rpow_le_rpow
  · unfold rateBandwidth dyadicWidth
    positivity
  · exact (rateBandwidth_bounds hd hn hβ hγ).2
  · exact hβ.le

-- @node: inverse_sqrt_mul_rpow
/-- Separate the sample size and bandwidth factors in the stochastic scale. -/
lemma inverse_sqrt_mul_rpow {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (D : ℝ) :
    1 / Real.sqrt (a * h ^ D) = a ^ (-(1 / 2 : ℝ)) * h ^ (-D / 2) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (by positivity),
    Real.mul_rpow ha.le (Real.rpow_nonneg hh.le _), ← Real.rpow_mul hh.le]
  congr 2
  ring

-- @node: rateWidth_stochastic_eq
/-- The continuous balancing width makes the stochastic scale equal the rate. -/
lemma rateWidth_stochastic_eq {d n : ℕ} {β γ : ℝ}
    (hn : 1 ≤ n) (hden : 2 * β + effectiveDimension d γ ≠ 0) :
    1 / Real.sqrt ((n : ℝ) * (rateWidth d n β γ) ^ (effectiveDimension d γ)) =
      rate d n β γ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [inverse_sqrt_mul_rpow hn' (by unfold rateWidth; positivity)]
  unfold rateWidth rate
  rw [← Real.rpow_mul hn'.le, ← Real.rpow_add hn']
  congr 1
  field_simp
  ring

-- @node: rateBandwidth_stochastic_le
/-- Rounding costs at most the factor `2^(D/2)` in the stochastic term. -/
lemma rateBandwidth_stochastic_le {d n : ℕ} {β γ : ℝ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) :
    1 / Real.sqrt ((n : ℝ) * (rateBandwidth d n β γ) ^ (effectiveDimension d γ)) ≤
      (2 : ℝ) ^ (effectiveDimension d γ / 2) * rate d n β γ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hw : 0 < rateWidth d n β γ := by unfold rateWidth; positivity
  have hh : 0 < rateBandwidth d n β γ := by unfold rateBandwidth dyadicWidth; positivity
  have hD := effectiveDimension_pos hd hγ
  have hden : 2 * β + effectiveDimension d γ ≠ 0 := ne_of_gt (by linarith)
  rw [inverse_sqrt_mul_rpow hn' hh]
  calc
    _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (rateWidth d n β γ / 2) ^ (-effectiveDimension d γ / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
        (rateBandwidth_bounds hd hn hβ hγ).1.le (by linarith)
    _ = (2 : ℝ) ^ (effectiveDimension d γ / 2) * rate d n β γ := by
      rw [Real.div_rpow hw.le (by norm_num), neg_div,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      rw [← rateWidth_stochastic_eq hn hden, inverse_sqrt_mul_rpow hn' hw]
      rw [neg_div]
      ring

end CausalSmith.Stat.GlobalTailDesignRobustCate

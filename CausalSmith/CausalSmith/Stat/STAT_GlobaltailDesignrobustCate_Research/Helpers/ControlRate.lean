module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BandwidthRate

/-! # Absorbing the control-arm logarithm

Roadmap (C19): the effective dimension exceeds the design dimension.
The logarithm in the control-arm bound (C18) is therefore absorbed by
the treated stochastic scale, and dyadic rounding gives the sharp rate.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- Weak overlap leaves a strictly positive gap between effective and
design dimension. -/
-- @node: designDimension_lt_effectiveDimension
lemma designDimension_lt_effectiveDimension {d : ℕ} {γ : ℝ}
    (hd : 1 ≤ d) (hγ : 1 < γ) : (d : ℝ) < effectiveDimension d γ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold effectiveDimension
  apply (lt_div_iff₀ (by linarith : 0 < γ - 1)).2
  nlinarith

/-- A positive dimension gap absorbs the logarithmic multiplicity of
control cells, uniformly over positive bandwidths. -/
-- @node: controlLog_variance_le
lemma controlLog_variance_le {n h D d : ℝ}
    (hn : 0 < n) (hh : 0 < h) (hgap : d < D) :
    Real.log (2 / h) / (n * h ^ d) ≤
      ((2 : ℝ) ^ (D - d) / (D - d)) / (n * h ^ D) := by
  have hlog := Real.log_le_rpow_div (x := 2 / h) (by positivity) (sub_pos.mpr hgap)
  calc
    _ ≤ ((2 / h) ^ (D - d) / (D - d)) / (n * h ^ d) :=
      div_le_div_of_nonneg_right hlog (by positivity)
    _ = _ := by
      rw [Real.div_rpow (by norm_num) hh.le, Real.rpow_sub hh]
      have hhd : h ^ d ≠ 0 := (Real.rpow_pos_of_pos hh d).ne'
      have hhD : h ^ D ≠ 0 := (Real.rpow_pos_of_pos hh D).ne'
      field_simp

/-- The square-root control noise is bounded by a fixed multiple of the
effective-dimensional stochastic scale. -/
-- @node: controlLog_noise_le
lemma controlLog_noise_le {n h D d : ℝ}
    (hn : 0 < n) (hh : 0 < h) (hgap : d < D) :
    Real.sqrt (Real.log (2 / h) / (n * h ^ d)) ≤
      Real.sqrt ((2 : ℝ) ^ (D - d) / (D - d)) /
        Real.sqrt (n * h ^ D) := by
  calc
    _ ≤ Real.sqrt (((2 : ℝ) ^ (D - d) / (D - d)) / (n * h ^ D)) :=
      Real.sqrt_le_sqrt (controlLog_variance_le hn hh hgap)
    _ = _ := Real.sqrt_div (by positivity) _

/-- At the paper's rounded bandwidth, the logarithmic control noise has
the sharp rate. This quantitative form of (C19) suffices for (C20). -/
-- @node: controlLog_rateBandwidth_le
lemma controlLog_rateBandwidth_le {d n : ℕ} {β γ : ℝ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) :
    Real.sqrt (Real.log (2 / rateBandwidth d n β γ) /
      ((n : ℝ) * (rateBandwidth d n β γ) ^ (d : ℝ))) ≤
      (Real.sqrt ((2 : ℝ) ^ (effectiveDimension d γ - d) /
        (effectiveDimension d γ - d)) *
        (2 : ℝ) ^ (effectiveDimension d γ / 2)) * rate d n β γ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh : 0 < rateBandwidth d n β γ := by
    unfold rateBandwidth dyadicWidth
    positivity
  calc
    _ ≤ _ := controlLog_noise_le hn' hh (designDimension_lt_effectiveDimension hd hγ)
    _ = Real.sqrt ((2 : ℝ) ^ (effectiveDimension d γ - d) /
        (effectiveDimension d γ - d)) *
        (1 / Real.sqrt ((n : ℝ) * (rateBandwidth d n β γ) ^
          (effectiveDimension d γ))) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (rateBandwidth_stochastic_le hd hn hβ hγ) (Real.sqrt_nonneg _)

end CausalSmith.Stat.GlobalTailDesignRobustCate

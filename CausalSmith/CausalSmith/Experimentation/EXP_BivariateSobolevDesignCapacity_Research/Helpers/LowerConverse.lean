module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.Vanishing

/-! # Lower constants and the dimension converse

A positive comparison-scale lower bound forces the square-root dimension condition,
even when the risks are extended real and the dimension sequence oscillates.
-/

public section
noncomputable section
open Filter
open scoped ENNReal Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The sharper lower constant dominates its positive endpoint value.](goal) Under [the stated conditions](hyp:hs1). -/
-- @node: cLower_uniform_positive
lemma cLower_uniform_positive (s : ℝ) (hs1 : s ≤ 1) :
    0 < cLower 1 ∧ cLower 1 ≤ cLower s := by
  have hbase : 0 < 48 + 32 * Real.pi ^ 2 := by positivity
  have hpow : (16384 : ℝ) ^ s ≤ (16384 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  constructor
  · unfold cLower
    positivity
  · unfold cLower
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hbase (Real.rpow_pos_of_pos (by norm_num) s))
      (mul_le_mul_of_nonneg_left hpow hbase.le)

/-- [ Vanishing extended-real risks bounded below by the comparison scale require
sub-square-root dimension growth.](goal) Under [the stated conditions](hyp:hs,hs1,hd,risk,hlower,hvanish). -/
-- @node: dimension_necessity_of_scale_lower
lemma dimension_necessity_of_scale_lower (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (ds : ℕ → ℕ) (hd : ∀ n, 2 ≤ ds n) (risk : ℕ → ℝ≥0∞)
    (hlower : ∀ᶠ n in atTop,
      ENNReal.ofReal (cLower s * bScale n (ds n) s) ≤ risk n)
    (hvanish : Tendsto risk atTop (𝓝 0)) :
    Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ))
      (fun n => Real.sqrt (n : ℝ)) := by
  have hc : 0 < cLower s :=
    lt_of_lt_of_le (cLower_uniform_positive s hs1).1 (cLower_uniform_positive s hs1).2
  have hscale_nonneg (n : ℕ) : 0 ≤ bScale n (ds n) s := by
    unfold bScale
    exact le_min (by norm_num) (Real.rpow_nonneg (by positivity) _)
  have he : Tendsto (fun n => ENNReal.ofReal (cLower s * bScale n (ds n) s))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hvanish
      (Filter.Eventually.of_forall (fun _ => bot_le)) hlower
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  have hr' : Tendsto (fun n => cLower s * bScale n (ds n) s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal
      (mul_nonneg hc.le (hscale_nonneg _)), ENNReal.toReal_zero] using hr
  have hb : Tendsto (fun n => aScale n (ds n) s) atTop (𝓝 0) := by
    have h := hr'.div_const (cLower s)
    simpa only [zero_div, mul_div_cancel_left₀ _ hc.ne', bScale, aScale] using h
  exact (scale_vanishing s hs hs1 ds hd).2.mp
    ((scale_vanishing s hs hs1 ds hd).1.mp hb)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

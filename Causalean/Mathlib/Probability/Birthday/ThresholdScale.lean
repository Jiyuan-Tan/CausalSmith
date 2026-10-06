module
public import Causalean.Mathlib.Probability.Birthday.LimitScale
public import Causalean.Mathlib.Probability.Birthday.Rounding

/-!
# Calibrating the birthday collision scale

The logarithmic tolerance constant is positive, the calibrated pair scale
diverges, and positive integer ceilings preserve its collision scale.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- A [tolerance strictly between zero and one](hyp:hdelta) has a
[positive logarithmic collision scale](goal). -/
theorem neg_log_one_sub_pos {delta : ℝ} (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    0 < -Real.log (1 - delta) := by
  have hpos : 0 < 1 - delta := by linarith [hdelta.2]
  have hlt : 1 - delta < 1 := by linarith [hdelta.1]
  exact neg_pos.mpr (Real.log_neg hpos hlt)

/-- For [valid success probabilities](hyp:heta), a
[diverging expected count](hyp:hmean), and a [tolerance between zero and
one](hyp:hdelta), the [calibrated pair scale](goal) diverges. -/
theorem calibratedScale_tendsto_atTop
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {delta : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun j => pairScale (Tseq j) (etaseq j) /
      (-Real.log (1 - delta))) atTop atTop := by
  have hden : Tendsto (fun j => mean (Tseq j) (etaseq j) ^ 2 / 2)
      atTop atTop := by
    simpa [pow_two] using
      (tendsto_mul_self_atTop.comp hmean).atTop_div_const
        (by norm_num : (0 : ℝ) < 2)
  have hpair : Tendsto (fun j => pairScale (Tseq j) (etaseq j))
      atTop atTop := by
    exact Filter.Tendsto.num hden zero_lt_one
      (pairScale_div_half_mean_sq_tendsto_one Tseq etaseq heta hmean)
  exact hpair.atTop_div_const (neg_log_one_sub_pos hdelta)

/-- For [valid success probabilities](hyp:heta), a
[diverging expected count](hyp:hmean), a [tolerance between zero and
one](hyp:hdelta), and a [positive multiplier](hyp:hc), the [pair scale per
positive-ceiling alphabet](goal) tends to the logarithmic scale divided by
that multiplier. -/
theorem pairScale_div_positiveCeil_tendsto
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {delta c : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c) :
    Tendsto (fun j => pairScale (Tseq j) (etaseq j) /
      (positiveCeil (c * (pairScale (Tseq j) (etaseq j) /
        (-Real.log (1 - delta)))) : ℝ))
      atTop (nhds ((-Real.log (1 - delta)) / c)) := by
  let L : ℝ := -Real.log (1 - delta)
  let a : ℕ → ℝ := fun j => pairScale (Tseq j) (etaseq j) / L
  have hL : 0 < L := neg_log_one_sub_pos hdelta
  have ha : Tendsto a atTop atTop :=
    calibratedScale_tendsto_atTop Tseq etaseq heta hmean hdelta
  have hround : Tendsto (fun j => (positiveCeil (c * a j) : ℝ) / a j)
      atTop (nhds c) := positiveCeil_mul_div_tendsto a ha hc
  have hlim : Tendsto (fun j => L / ((positiveCeil (c * a j) : ℝ) / a j))
      atTop (nhds (L / c)) := tendsto_const_nhds.div hround hc.ne'
  change Tendsto (fun j => pairScale (Tseq j) (etaseq j) /
    (positiveCeil (c * a j) : ℝ)) atTop (nhds (L / c))
  apply hlim.congr'
  filter_upwards [ha.eventually_gt_atTop 0] with j hj
  have hceil : (positiveCeil (c * a j) : ℝ) ≠ 0 := by
    exact_mod_cast (positiveCeil_pos (c * a j)).ne'
  have hane : a j ≠ 0 := hj.ne'
  have hident : pairScale (Tseq j) (etaseq j) = a j * L := by
    dsimp [a]
    field_simp [hL.ne']
  rw [hident]
  field_simp

end Causalean.Mathlib.Probability.Birthday

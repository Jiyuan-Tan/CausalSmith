module
public import Causalean.Mathlib.Probability.Birthday.Limit
public import Causalean.Mathlib.Probability.Birthday.ThresholdFinite
public import Causalean.Mathlib.Probability.Birthday.ThresholdScale

/-!
# Asymptotic inversion of the least birthday threshold

The least positive alphabet size that meets a fixed collision tolerance is
asymptotic to the binomial pair scale divided by its logarithmic constant.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For [valid success probabilities](hyp:heta), a
[diverging expected draw count](hyp:hmean), and a [tolerance strictly between
zero and one](hyp:hdelta), the [least positive alphabet threshold divided by
the calibrated pair scale](goal) converges to one. -/
theorem mStar_div_calibratedScale_tendsto_one
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {delta : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun j => (mStar (Tseq j) (etaseq j) delta : ℝ) /
      (pairScale (Tseq j) (etaseq j) / (-Real.log (1 - delta))))
      atTop (nhds 1) := by
  -- Set L = -log (1-delta) > 0 and a_j = pairScale_j/L, with a_j → ∞.
  -- Fix 0 < c₋ < 1 < c₊. At positiveCeil(c*a_j), `repeat_tendsto`
  -- and `pairScale_div_positiveCeil_tendsto` give limit 1-exp(-L/c).
  -- This is strictly above delta for c₋ and strictly below it for c₊;
  -- use `Real.exp_neg_log` / `Real.exp_log` and monotonicity of exp to
  -- identify delta = 1-exp(-L). Eventual strict inequalities and
  -- `repeat_le_iff_mStar_le` imply
  -- positiveCeil(c₋*a_j) < mStar_j ≤ positiveCeil(c₊*a_j).
  -- Divide by eventually positive a_j and apply
  -- `positiveCeil_mul_div_tendsto` for the two boundaries. To show
  -- convergence to 1, use `LinearOrderedAddCommGroup.tendsto_nhds`:
  -- for each ε>0 choose c₋ = 1-min (ε/2) (1/2) and c₊ = 1+ε/2,
  -- and combine the eventual bounds with the limits c₋ and c₊.
  let L : ℝ := -Real.log (1 - delta)
  let a : ℕ → ℝ := fun j => pairScale (Tseq j) (etaseq j) / L
  let r : ℕ → ℝ := fun j => (mStar (Tseq j) (etaseq j) delta : ℝ) / a j
  have hL : 0 < L := neg_log_one_sub_pos hdelta
  have ha : Tendsto a atTop atTop :=
    calibratedScale_tendsto_atTop Tseq etaseq heta hmean hdelta
  have hexp : Real.exp (-L) = 1 - delta := by
    dsimp [L]
    rw [neg_neg, Real.exp_log (by linarith [hdelta.2])]
  have hboundary (c : ℝ) (hc : 0 < c) :
      Tendsto (fun j => birthdayRepeat (Tseq j)
        (positiveCeil (c * a j)) (etaseq j)) atTop
        (nhds (1 - Real.exp (-(L / c)))) := by
    apply repeat_tendsto Tseq (fun j => positiveCeil (c * a j)) etaseq
      heta hmean (fun j => positiveCeil_pos _)
    · simpa only [a, L] using
        pairScale_div_positiveCeil_tendsto Tseq etaseq heta hmean hdelta hc
    · exact div_pos hL hc
  have hbelow (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
      ∀ᶠ j in atTop, (positiveCeil (c * a j) : ℝ) / a j < r j := by
    have hq : L < L / c := by
      apply (lt_div_iff₀ hc).2
      nlinarith [mul_pos hL (sub_pos.mpr hc1)]
    have hlimit : delta < 1 - Real.exp (-(L / c)) := by
      have he := Real.exp_strictMono (show -(L / c) < -L by linarith)
      linarith [hexp]
    have hev := (hboundary c hc).eventually (eventually_gt_nhds hlimit)
    filter_upwards [hev, ha.eventually_gt_atTop 0] with j hj haj
    have hm : positiveCeil (c * a j) < mStar (Tseq j) (etaseq j) delta := by
      by_contra hn
      have hle := (repeat_le_iff_mStar_le (Tseq j)
        (positiveCeil (c * a j)) (etaseq j) delta
        (heta j) hdelta.1 (positiveCeil_pos _)).2 (Nat.le_of_not_gt hn)
      exact (not_le_of_gt hj) hle
    exact (div_lt_div_iff_of_pos_right haj).2 (by exact_mod_cast hm)
  have habove (c : ℝ) (hc : 1 < c) :
      ∀ᶠ j in atTop, r j ≤ (positiveCeil (c * a j) : ℝ) / a j := by
    have hc0 : 0 < c := by linarith
    have hq : L / c < L := by
      apply (div_lt_iff₀ hc0).2
      nlinarith [mul_pos hL (sub_pos.mpr hc)]
    have hlimit : 1 - Real.exp (-(L / c)) < delta := by
      have he := Real.exp_strictMono (show -L < -(L / c) by linarith)
      linarith [hexp]
    have hev := (hboundary c hc0).eventually (eventually_lt_nhds hlimit)
    filter_upwards [hev, ha.eventually_gt_atTop 0] with j hj haj
    have hm : mStar (Tseq j) (etaseq j) delta ≤ positiveCeil (c * a j) :=
      (repeat_le_iff_mStar_le (Tseq j) (positiveCeil (c * a j))
        (etaseq j) delta (heta j) hdelta.1 (positiveCeil_pos _)).1 hj.le
    exact (div_le_div_iff_of_pos_right haj).2 (by exact_mod_cast hm)
  change Tendsto r atTop (nhds 1)
  apply tendsto_order.2
  constructor
  · intro b hb
    let c : ℝ := max (1 / 2) ((b + 1) / 2)
    have hc : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hc1 : c < 1 := max_lt (by norm_num) (by dsimp [c] at *; linarith)
    have hbc : b < c := by
      dsimp [c]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    filter_upwards [hbelow c hc hc1,
      (positiveCeil_mul_div_tendsto a ha hc).eventually (eventually_gt_nhds hbc)]
      with j hj hjc
    exact lt_trans hjc hj
  · intro b hb
    let c : ℝ := (b + 1) / 2
    have hc : 1 < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    filter_upwards [habove c hc,
      (positiveCeil_mul_div_tendsto a ha (by linarith : 0 < c)).eventually
        (eventually_lt_nhds hcb)]
      with j hj hjc
    exact lt_of_le_of_lt hj hjc

end Causalean.Mathlib.Probability.Birthday

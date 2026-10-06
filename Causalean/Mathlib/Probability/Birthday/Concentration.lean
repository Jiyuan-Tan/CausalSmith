module
public import Causalean.Mathlib.Probability.Birthday.Moments

/-!
# Binomial concentration at a diverging mean

The variance identity and a relative-deviation estimate are stated for the
finite averaging operator used by the birthday kernel.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For a [valid success probability](hyp:heta), pointwise [ordered count
functions](hyp:hfg) have [ordered binomial averages](goal). -/
theorem binomialAverage_mono (T : ℕ) (eta : ℝ) (f g : ℕ → ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hfg : ∀ r, r ≤ T → f r ≤ g r) :
    binomialAverage T eta f ≤ binomialAverage T eta g := by
  unfold binomialAverage
  apply Finset.sum_le_sum
  intro r hr
  have hw : 0 ≤ Causalean.Mathlib.Probability.binomialWeight T eta r := by
    simp only [Causalean.Mathlib.Probability.binomialWeight]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta.1 _))
      (pow_nonneg (sub_nonneg.mpr heta.2) _)
  have hrT : r ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  exact mul_le_mul_of_nonneg_left (hfg r hrT) hw

/-- For a [valid success probability](hyp:heta), a [nonnegative count
function](hyp:hf) has a [nonnegative binomial average](goal). -/
theorem binomialAverage_nonneg (T : ℕ) (eta : ℝ) (f : ℕ → ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ r, r ≤ T → 0 ≤ f r) :
    0 ≤ binomialAverage T eta f := by
  have h := binomialAverage_mono T eta (fun _ => 0) f heta (by
    intro r hr
    exact hf r hr)
  simpa [binomialAverage] using h

/-- For a [valid success probability](hyp:heta) and [positive alphabet](hyp:hm),
the [averaged repeat probability](goal) is at most the expected pair count
divided by the alphabet size. -/
theorem repeat_le_pairScale_div (T m : ℕ) (eta : ℝ)
    (hm : 0 < m) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    birthdayRepeat T m eta ≤ pairScale T eta / (m : ℝ) := by
  have h := binomialAverage_mono T eta (repeatKernel m)
    (fun r => (r.choose 2 : ℝ) / (m : ℝ)) heta (by
      intro r _
      exact repeatKernel_le_pairs m r hm)
  rw [← birthdayRepeat] at h
  have havg : binomialAverage T eta (fun r => (r.choose 2 : ℝ) / (m : ℝ)) =
      pairScale T eta / (m : ℝ) := by
    unfold binomialAverage
    calc
      _ = (∑ r ∈ Finset.range (T + 1),
          Causalean.Mathlib.Probability.binomialWeight T eta r *
            (r.choose 2 : ℝ)) / (m : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [← binomialAverage, binomialAverage_pairs]
  exact h.trans_eq havg

/-- The [binomial average for a trial count](hyp:T) and
[success probability](hyp:eta) of the [squared centered count](goal) is the
ordinary binomial variance. -/
theorem binomialAverage_centered_sq (T : ℕ) (eta : ℝ) :
    binomialAverage T eta (fun r => ((r : ℝ) - mean T eta) ^ 2) =
      mean T eta * (1 - eta) := by
  have hpoly (r : ℕ) : ((r : ℝ) - mean T eta) ^ 2 =
      2 * (r.choose 2 : ℝ) + (1 - 2 * mean T eta) * r + mean T eta ^ 2 := by
    rw [Nat.cast_choose_two ℝ]
    ring
  have hsum : binomialAverage T eta (fun r => ((r : ℝ) - mean T eta) ^ 2) =
      2 * binomialAverage T eta (fun r => (r.choose 2 : ℝ)) +
      (1 - 2 * mean T eta) * binomialAverage T eta (fun r => (r : ℝ)) +
      mean T eta ^ 2 * binomialAverage T eta (fun _ => 1) := by
    unfold binomialAverage
    calc
      _ = ∑ r ∈ Finset.range (T + 1),
          (2 * (Causalean.Mathlib.Probability.binomialWeight T eta r *
            (r.choose 2 : ℝ)) +
          (1 - 2 * mean T eta) *
            (Causalean.Mathlib.Probability.binomialWeight T eta r * (r : ℝ)) +
          mean T eta ^ 2 *
            (Causalean.Mathlib.Probability.binomialWeight T eta r * 1)) := by
        apply Finset.sum_congr rfl
        intro r _
        change Causalean.Mathlib.Probability.binomialWeight T eta r *
          ((r : ℝ) - mean T eta) ^ 2 = _
        rw [hpoly]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum, binomialAverage_pairs, binomialAverage_count, binomialAverage_one]
  unfold pairScale mean
  rw [Nat.cast_choose_two ℝ]
  ring

/-- For a [valid success probability](hyp:heta), the
[binomial mass outside a band](goal) with [positive radius](hyp:ha) is at most variance
divided by the squared band radius. -/
theorem binomialAverage_deviation_le (T : ℕ) {eta a : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (ha : 0 < a) :
    binomialAverage T eta
        (fun r => if a ≤ |(r : ℝ) - mean T eta| then 1 else 0) ≤
      mean T eta * (1 - eta) / a ^ 2 := by
  have hpoint (r : ℕ) :
      (if a ≤ |(r : ℝ) - mean T eta| then (1 : ℝ) else 0) ≤
        ((r : ℝ) - mean T eta) ^ 2 / a ^ 2 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    split_ifs with h
    · apply (le_div_iff₀ ha2).2
      have hs : a ^ 2 ≤ |(r : ℝ) - mean T eta| ^ 2 := by nlinarith
      nlinarith [sq_abs ((r : ℝ) - mean T eta)]
    · exact div_nonneg (sq_nonneg _) (le_of_lt ha2)
  have h := binomialAverage_mono T eta
    (fun r => if a ≤ |(r : ℝ) - mean T eta| then 1 else 0)
    (fun r => ((r : ℝ) - mean T eta) ^ 2 / a ^ 2) heta
    (by intro r _; exact hpoint r)
  have havg : binomialAverage T eta
      (fun r => ((r : ℝ) - mean T eta) ^ 2 / a ^ 2) =
      mean T eta * (1 - eta) / a ^ 2 := by
    unfold binomialAverage
    calc
      _ = (∑ r ∈ Finset.range (T + 1),
          Causalean.Mathlib.Probability.binomialWeight T eta r *
            ((r : ℝ) - mean T eta) ^ 2) / a ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [← binomialAverage, binomialAverage_centered_sq]
  exact h.trans_eq havg

/-- For [valid success probabilities](hyp:heta), a
[diverging expected count](hyp:hmean) makes [every relative-deviation binomial mass for a positive relative radius](hyp:heps) [vanish](goal). -/
theorem binomial_relative_deviation_tendsto_zero
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ)
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto
      (fun j => binomialAverage (Tseq j) (etaseq j)
        (fun r => if eps * mean (Tseq j) (etaseq j) ≤
          |(r : ℝ) - mean (Tseq j) (etaseq j)| then 1 else 0))
      atTop (nhds 0) := by
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < mean (Tseq j) (etaseq j) :=
    hmean.eventually_gt_atTop 0
  have hupper : Tendsto
      (fun j => (eps ^ 2)⁻¹ * (mean (Tseq j) (etaseq j))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (eps ^ 2)⁻¹)).mul
      (tendsto_inv_atTop_zero.comp hmean)
  apply squeeze_zero' _ _ hupper
  · filter_upwards with j
    exact binomialAverage_nonneg (Tseq j) (etaseq j) _ (heta j)
      (by intro r _; split_ifs <;> norm_num)
  · filter_upwards [hpos] with j hj
    have hband : 0 < eps * mean (Tseq j) (etaseq j) := mul_pos heps hj
    have hdev := binomialAverage_deviation_le (Tseq j) (heta j) hband
    have heps0 : eps ≠ 0 := ne_of_gt heps
    have hmu0 : mean (Tseq j) (etaseq j) ≠ 0 := ne_of_gt hj
    have hfac : mean (Tseq j) (etaseq j) * (1 - etaseq j) /
        (eps * mean (Tseq j) (etaseq j)) ^ 2 =
        (1 - etaseq j) * ((eps ^ 2)⁻¹ * (mean (Tseq j) (etaseq j))⁻¹) := by
      field_simp
    rw [hfac] at hdev
    exact hdev.trans (by
      have hc : 0 ≤ (eps ^ 2)⁻¹ * (mean (Tseq j) (etaseq j))⁻¹ := by
        positivity
      have heta1 : 1 - etaseq j ≤ 1 := by linarith [(heta j).1]
      simpa using mul_le_mul_of_nonneg_right heta1 hc)

end Causalean.Mathlib.Probability.Birthday

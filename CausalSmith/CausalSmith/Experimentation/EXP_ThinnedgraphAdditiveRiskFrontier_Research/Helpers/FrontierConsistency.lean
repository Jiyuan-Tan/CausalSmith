module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ElbowAlgebra
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Sequence limits for the explicit precision scale

The elbow comparison turns vanishing precision scale into the two ratio limits,
including the infinite value of the inverse-retention ratio at zero retention.
-/

public section

open scoped ENNReal
open Filter
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- The precision scale is nonnegative on the retention domain.  [For the stated data and conditions](hyp:n,d,q,hq), [the stated conclusion holds](goal). -/
-- @node: frontierScale_nonneg
lemma frontierScale_nonneg (n d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    0 ≤ frontierScale n d q := by
  have hp : 0 ≤ 1 - (1 - q) ^ d := by
    exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hq.2) (by linarith [hq.1]))
  unfold frontierScale
  split_ifs <;> positivity

/-- The scale vanishes exactly when both population and audit ratios vanish.  [For the stated data and conditions](hyp:dseq,qseq,ha), [the stated conclusion holds](goal). -/
-- @node: frontierScale_tendsto_iff
lemma frontierScale_tendsto_iff (dseq : ℕ → ℕ) (qseq : ℕ → ℝ)
    (ha : AdmissibleSequences dseq qseq) :
    Tendsto (fun n => frontierScale n (dseq n) (qseq n)) atTop (nhds 0) ↔
      (Tendsto (fun n => (dseq n : ℝ) ^ 2 / n) atTop (nhds 0) ∧
       Tendsto (fun n => if qseq n = 0 then (⊤ : ℝ≥0∞)
         else ENNReal.ofReal (dseq n / (n * qseq n))) atTop (nhds 0)) := by
  have hadm : ∀ᶠ n in atTop, 4 ≤ n := eventually_ge_atTop 4
  constructor
  · intro hF
    have hsmall := (tendsto_order.mp hF).2 (1 / 2) (by norm_num)
    have hpos : ∀ᶠ n in atTop, 0 < qseq n := by
      filter_upwards [hsmall] with n hn
      by_contra h
      norm_num [frontierScale, h] at hn
    have hsum : ∀ᶠ n in atTop,
        (dseq n : ℝ) ^ 2 / n + dseq n / (n * qseq n) ≤
          2 * frontierScale n (dseq n) (qseq n) := by
      filter_upwards [hadm, hpos, hsmall] with n hn hq hs
      obtain ⟨hd, hdu, hqdom⟩ := ha n hn
      have hb := ((frontier_elbow n (dseq n) hn hd hdu).2.2 (qseq n) hq hqdom.2).1
      have hx : (dseq n : ℝ) ^ 2 / n + dseq n / (n * qseq n) < 1 := by
        by_contra h
        rw [min_eq_left (le_of_not_gt h)] at hb
        linarith
      rw [min_eq_right hx.le] at hb
      linarith
    have htwice : Tendsto (fun n => 2 * frontierScale n (dseq n) (qseq n))
        atTop (nhds 0) := by simpa using hF.const_mul 2
    have hxnonneg : ∀ n, 0 ≤ (dseq n : ℝ) ^ 2 / n := by intro n; positivity
    have hynonneg : ∀ᶠ n in atTop, 0 ≤ (dseq n : ℝ) / (n * qseq n) := by
      filter_upwards [hpos] with n hq
      positivity
    have hx := squeeze_zero' (Eventually.of_forall hxnonneg) (by
      filter_upwards [hsum, hynonneg] with n hs hy
      linarith) htwice
    have hy : Tendsto (fun n => (dseq n : ℝ) / (n * qseq n)) atTop (nhds 0) :=
      squeeze_zero' hynonneg (by
        filter_upwards [hsum] with n hs
        linarith [hxnonneg n]) htwice
    refine ⟨hx, ?_⟩
    have hy' := ENNReal.tendsto_ofReal hy
    simp only [ENNReal.ofReal_zero] at hy'
    apply hy'.congr'
    filter_upwards [hpos] with n hq
    simp [ne_of_gt hq]
  · rintro ⟨hx, hy⟩
    have hsmall := (tendsto_order.mp hy).2 1 (by norm_num)
    have hpos : ∀ᶠ n in atTop, 0 < qseq n := by
      filter_upwards [hadm, hsmall] with n hn hs
      have hq := (ha n hn).2.2.1
      have hne : qseq n ≠ 0 := by
        intro h
        simp [h] at hs
      exact lt_of_le_of_ne hq (Ne.symm hne)
    have hyreal : Tendsto (fun n => (dseq n : ℝ) / (n * qseq n))
        atTop (nhds 0) := by
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hy
      simp only [ENNReal.toReal_zero] at ht
      apply ht.congr'
      filter_upwards [hpos] with n hq
      simp [ne_of_gt hq, ENNReal.toReal_ofReal (by positivity :
        0 ≤ (dseq n : ℝ) / (n * qseq n))]
    have hsum := hx.add hyreal
    simp only [zero_add] at hsum
    have hbound : ∀ᶠ n in atTop, frontierScale n (dseq n) (qseq n) ≤
        (1 - Real.exp (-1))⁻¹ * ((dseq n : ℝ) ^ 2 / n + dseq n / (n * qseq n)) := by
      filter_upwards [hadm, hpos] with n hn hq
      obtain ⟨hd, hdu, hqdom⟩ := ha n hn
      have hb := ((frontier_elbow n (dseq n) hn hd hdu).2.2 (qseq n) hq hqdom.2).2
      exact hb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by
        have hc : 0 < 1 - Real.exp (-1) := by
          linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
        positivity))
    apply squeeze_zero' ?_ hbound
      (by simpa using hsum.const_mul (1 - Real.exp (-1))⁻¹)
    filter_upwards [hadm] with n hn
    exact frontierScale_nonneg n (dseq n) (qseq n) (ha n hn).2.2

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

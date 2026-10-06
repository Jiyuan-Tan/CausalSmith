module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Precision-scale endpoint and elbow algebra
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The source reveal probability is bounded above by the union bound.  [For the stated data and conditions](hyp:d,q,hq), [the stated conclusion holds](goal). -/
-- @node: reveal_probability_le_mul
lemma reveal_probability_le_mul (d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    1 - (1 - q) ^ d ≤ (d : ℝ) * q := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp := pow_nonneg (sub_nonneg.mpr hq.2) d
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hq.2)
    rw [pow_succ, Nat.cast_succ]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ d) (sq_nonneg q)]

/-- Exponential convexity gives a uniform chord lower bound for reveal probabilities.  [For the stated data and conditions](hyp:d,q,hq), [the stated conclusion holds](goal). -/
-- @node: reveal_probability_ge_chord
lemma reveal_probability_ge_chord (d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (1 - Real.exp (-1)) * min 1 ((d : ℝ) * q) ≤ 1 - (1 - q) ^ d := by
  have hbase : 1 - q ≤ Real.exp (-q) := by
    linarith [Real.add_one_le_exp (-q)]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hq.2) hbase d
  rw [← Real.exp_nat_mul] at hpow
  have hx : 0 ≤ (d : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq.1
  by_cases h : (d : ℝ) * q ≤ 1
  · have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (sub_nonneg.mpr h) hx (by ring : (1 - (d : ℝ) * q) + (d : ℝ) * q = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_neg_one, Real.exp_zero,
      mul_one] at hc
    rw [min_eq_right h]
    have he : (d : ℝ) * -q = -((d : ℝ) * q) := by ring
    rw [he] at hpow
    nlinarith
  · have he : (d : ℝ) * -q ≤ -1 := by nlinarith
    have hc := Real.exp_le_exp.mpr he
    rw [min_eq_left (le_of_not_ge h)]
    linarith

/-- Endpoint formulas and the explicit positive-retention elbow comparison.  [For the stated data and conditions](hyp:n,d,hn,hd,hdu), [the stated conclusion holds](goal). -/
-- @node: frontier_elbow
lemma frontier_elbow (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) :
    frontierScale n d 0 = 1 ∧ frontierScale n d 1 = min 1 ((d : ℝ) ^ 2 / n) ∧
    ∀ q : ℝ, 0 < q → q ≤ 1 →
      (1 / 2 : ℝ) * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)) ≤ frontierScale n d q ∧
      frontierScale n d q ≤ (1 - Real.exp (-1))⁻¹ * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)) := by
  have hd0 : d ≠ 0 := by omega
  refine ⟨by simp [frontierScale], by simp [frontierScale, hd0], ?_⟩
  intro q hq hq1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let p := 1 - (1 - q) ^ d
  let c := 1 - Real.exp (-1)
  have hc : 0 < c := by
    dsimp [c]
    linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
  have hc1 : c ≤ 1 := by dsimp [c]; linarith [Real.exp_pos (-1)]
  have hp1 : p ≤ 1 := sub_le_self _ (pow_nonneg (by linarith) d)
  have hpdq : p ≤ (d : ℝ) * q := reveal_probability_le_mul d q ⟨hq.le, hq1⟩
  have hpc : c * min 1 ((d : ℝ) * q) ≤ p :=
    reveal_probability_ge_chord d q ⟨hq.le, hq1⟩
  have hp : 0 < p := lt_of_lt_of_le (mul_pos hc (lt_min (by norm_num) (mul_pos hdpos hq))) hpc
  let x := (d : ℝ) ^ 2 / n
  let y := (d : ℝ) / (n * q)
  let v := (d : ℝ) ^ 2 / (n * p)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hxv : x ≤ v := by
    dsimp [x, v]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hnpos hp)
      (by nlinarith)
  have hyv : y ≤ v := by
    dsimp [y, v]
    apply (div_le_div_iff₀ (mul_pos hnpos hq) (mul_pos hnpos hp)).2
    nlinarith [mul_le_mul_of_nonneg_left hpdq (mul_pos hnpos hdpos).le]
  have hcv : c * v ≤ x + y := by
    by_cases ht : (d : ℝ) * q ≤ 1
    · rw [min_eq_right ht] at hpc
      have hcy : c * v ≤ y := by
        dsimp [v, y]
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (mul_pos hnpos hp) (mul_pos hnpos hq)).2
        nlinarith [mul_le_mul_of_nonneg_left hpc (mul_pos hnpos hdpos).le]
      linarith
    · rw [min_eq_left (le_of_not_ge ht)] at hpc
      have hcx : c * v ≤ x := by
        dsimp [v, x]
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (mul_pos hnpos hp) hnpos).2
        nlinarith [mul_le_mul_of_nonneg_left hpc (mul_nonneg hnpos.le (sq_nonneg (d : ℝ)))]
      linarith
  simp only [frontierScale, if_pos hq]
  change (1 / 2 : ℝ) * min 1 (x + y) ≤ min 1 v ∧
    min 1 v ≤ c⁻¹ * min 1 (x + y)
  constructor
  · by_cases ht : 1 ≤ v
    · rw [min_eq_left ht]
      linarith [min_le_left (1 : ℝ) (x + y)]
    · rw [min_eq_right (le_of_not_ge ht)]
      linarith [min_le_right (1 : ℝ) (x + y)]
  · apply (le_inv_mul_iff₀ hc).2
    apply le_min
    · exact (mul_le_mul_of_nonneg_right hc1 (le_min (by norm_num) hv)).trans
        (by simpa using min_le_left (1 : ℝ) v)
    · exact (mul_le_mul_of_nonneg_left (min_le_right 1 v) hc.le).trans hcv

/-- The observable risk envelope is at most twenty-four times the explicit
precision scale after truncation at one.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hq), [the stated conclusion holds](goal). -/
-- @node: upperEnvelope_le_frontierScale
lemma upperEnvelope_le_frontierScale (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc 0 1) :
    min 1 (upperEnvelope n d q) ≤ ENNReal.ofReal (24 * frontierScale n d q) := by
  by_cases hpos : 0 < q
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    let p := 1 - (1 - q) ^ d
    have hp1 : p ≤ 1 := sub_le_self _ (pow_nonneg (sub_nonneg.mpr hq.2) d)
    have hpdq : p ≤ (d : ℝ) * q := reveal_probability_le_mul d q hq
    have hc : 0 < 1 - Real.exp (-1) := by
      linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
    have hp : 0 < p := lt_of_lt_of_le
      (mul_pos hc (lt_min (by norm_num) (mul_pos hdpos hpos)))
      (reveal_probability_ge_chord d q hq)
    let v := (d : ℝ) ^ 2 / (n * p)
    have hx : (d : ℝ) ^ 2 / n ≤ v := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hnpos hp)
      nlinarith
    have hy : (d : ℝ) / (n * q) ≤ v := by
      apply (div_le_div_iff₀ (mul_pos hnpos hpos) (mul_pos hnpos hp)).2
      nlinarith [mul_le_mul_of_nonneg_left hpdq (mul_pos hnpos hdpos).le]
    have ha : 5 * ((d : ℝ) + 1) ^ 2 / n ≤ 20 * ((d : ℝ) ^ 2 / n) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith
    have hb : 4 * d * (1 - q) / (n * q) ≤ 4 * ((d : ℝ) / (n * q)) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (mul_pos hnpos hpos).le
      nlinarith [mul_nonneg hdpos.le hq.1]
    have hu : 5 * ((d : ℝ) + 1) ^ 2 / n +
        4 * d * (1 - q) / (n * q) ≤ 24 * v := by
      linarith
    rw [upperEnvelope, if_pos hpos, frontierScale, if_pos hpos]
    change min 1 (ENNReal.ofReal _) ≤ ENNReal.ofReal (24 * min 1 v)
    by_cases hv : v ≤ 1
    · rw [min_eq_right hv]
      exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal hu)
    · rw [min_eq_left (le_of_not_ge hv)]
      exact (min_le_left _ _).trans (by norm_num)
  · simp [upperEnvelope, frontierScale, hpos]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

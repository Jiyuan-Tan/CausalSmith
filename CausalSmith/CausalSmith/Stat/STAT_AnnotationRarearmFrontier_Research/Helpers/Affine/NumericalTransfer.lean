module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalSeparation
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Numerical prefix-failure and squared-gap bounds for the fixed-size affine transfer.
These are the final numerical estimates following equations (10)--(12).
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:S,hS), Above unit label scale, the weighted failure envelope is bounded at scale one.  This gives [the stated result](goal).-/
-- @node: affine_weighted_prefix_failure_bound
lemma affine_weighted_prefix_failure_bound (S : Real) (hS : 1 ≤ S) :
    S * Real.exp (-124 * S) ≤ Real.exp (-124) := by
  have hlin : S ≤ Real.exp (124 * (S - 1)) := by
    have h := Real.add_one_le_exp (124 * (S - 1))
    linarith
  calc
    _ ≤ Real.exp (124 * (S - 1)) * Real.exp (-124 * S) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- [Under the stated inputs and conditions](hyp:n,eps,heps,heps',hS), The two prefix failures cost at most 10⁻²⁴ divided by the label scale.  This gives [the stated result](goal).-/
-- @node: affine_fixed_size_failure_small
lemma affine_fixed_size_failure_small (n : Nat) (eps : Real)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) (hS : 1 ≤ (n : Real) * eps) :
    2 * Real.exp (-31 * (n : Real)) ≤
      (1 : Real) / 1000000000000000000000000 / ((n : Real) * eps) := by
  have hn : 4 * ((n : Real) * eps) ≤ n := by
    have h := mul_le_mul_of_nonneg_left heps' (Nat.cast_nonneg n : (0 : Real) ≤ n)
    linarith
  have he124 : (2 : Real) ^ 124 ≤ Real.exp 124 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2)
      (le_of_lt Real.exp_one_gt_two) 124
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hsmall : 2 * Real.exp (-124 : Real) ≤
      (1 : Real) / 1000000000000000000000000 := by
    rw [Real.exp_neg, ← one_div]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (Real.exp_pos 124)).mpr
    norm_num at he124 ⊢
    linarith
  apply (le_div_iff₀ (by linarith : 0 < (n : Real) * eps)).mpr
  have hmono := Real.exp_le_exp.mpr (show -31 * (n : Real) ≤
    -124 * ((n : Real) * eps) by linarith)
  have hweighted := affine_weighted_prefix_failure_bound ((n : Real) * eps) hS
  have hm := mul_le_mul_of_nonneg_right hmono (show 0 ≤ (n : Real) * eps by positivity)
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,m), In the affine regime, the squared raw target gap dominates 10⁻²⁰/S.  This gives [the stated result](goal).-/
-- @node: affine_raw_target_mean_gap_sq_lower
lemma affine_raw_target_mean_gap_sq_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    (1 : Real) / 100000000000000000000 / ((n : Real) * eps) ≤ gap ^ 2 := by
  intro nu gap
  let x := (d : Real) / (((n : Real) + m) * eps * logScale n eps)
  have hgap : min x 1 / 10000000000 ≤ gap :=
    affine_raw_target_mean_gap_uniform n m d eps hn hd heps heps' hS sigma
  have hell := affine_logScale_one_le n eps heps.le
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hclip : 0 ≤ min x 1 := le_min hx0 (by norm_num)
  have hsq := pow_le_pow_left₀ (div_nonneg hclip (by norm_num)) hgap 2
  have hmin : 1 / ((n : Real) * eps) ≤ (min x 1) ^ 2 := by
    by_cases hx1 : x ≤ 1
    · rw [min_eq_left hx1]; exact hx.le
    · rw [min_eq_right (le_of_not_ge hx1)]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hS
      simpa using h
  have hscaled := mul_le_mul_of_nonneg_left hmin
    (by norm_num : (0 : Real) ≤ 1 / 100000000000000000000)
  simp only [div_eq_mul_inv] at hscaled hsq ⊢
  norm_num at hscaled hsq ⊢
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,m), Prefix failures consume at most half of the raw testing lower bound.  This gives [the stated result](goal).-/
-- @node: affine_fixed_size_failure_gap
lemma affine_fixed_size_failure_gap (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    2 * Real.exp (-31 * (n : Real)) ≤ gap ^ 2 / 128 := by
  intro nu gap
  have hf := affine_fixed_size_failure_small n eps heps heps' hS
  have hg := affine_raw_target_mean_gap_sq_lower n m d eps hn hd heps heps' hS hx sigma
  change (1 : Real) / 100000000000000000000 / ((n : Real) * eps) ≤ gap ^ 2 at hg
  have hpos : 0 ≤ 1 / ((n : Real) * eps) := by positivity
  simp only [div_eq_mul_inv] at hf hg hpos ⊢
  norm_num at hf hg hpos ⊢
  nlinarith

end CausalSmith.Stat.AnnotationRarearmFrontier

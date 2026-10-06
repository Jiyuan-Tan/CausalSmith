module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Basic

/-!
Abstract sequence algebra for risks uniformly comparable to the frontier.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


open Filter Asymptotics

/-- [Under the stated inputs and conditions](hyp:n,eps,hn,heps), The logarithmic diagnostic is positive for every positive label scale.  This gives [the stated result](goal).-/
-- @node: phase_logScale_pos
lemma phase_logScale_pos (n : Nat) (eps : Real) (hn : 1 ≤ n) (heps : 0 < eps) :
    0 < logScale n eps := by
  apply Real.log_pos
  have hS : 0 < labelScale n eps := mul_pos (by exact_mod_cast hn) heps
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  change 1 < Real.exp 1 + labelScale n eps
  linarith

/-- [Under the stated inputs and conditions](hyp:eps,n,m,d), The frontier always dominates the capped rare-label benchmark.  This gives [the stated result](goal).-/
-- @node: phase_labelBenchmark_le_frontier
lemma phase_labelBenchmark_le_frontier (n m d : Nat) (eps : Real) :
    labelBenchmark n eps ≤ frontierRate n m d eps := by
  apply min_le_min_left
  simpa only [one_div] using le_add_of_nonneg_right
    (sq_nonneg ((d : Real) / (((n : Real) + m) * eps * logScale n eps)))

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,hd,n,m,d), At the dimension saturation threshold the capped frontier equals one.  This gives [the stated result](goal).-/
-- @node: phase_frontier_saturation
lemma phase_frontier_saturation (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps)
    (hd : ((n : Real) + m) * eps * logScale n eps ≤ d) :
    frontierRate n m d eps = 1 := by
  have hS : 0 < labelScale n eps := mul_pos (by exact_mod_cast hn) heps
  have hD : 0 < ((n : Real) + m) * eps * logScale n eps :=
    mul_pos (mul_pos (by positivity) heps) (phase_logScale_pos n eps hn heps)
  have hx : 1 ≤ (d : Real) / (((n : Real) + m) * eps * logScale n eps) :=
    (le_div_iff₀ hD).mpr (by simpa using hd)
  apply min_eq_left
  nlinarith [one_div_pos.mpr hS]

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,hbudget,d,n,m), The marginal-budget plateau bounds the frontier by twice the capped label benchmark.  This gives [the stated result](goal).-/
-- @node: phase_frontier_plateau
lemma phase_frontier_plateau (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps)
    (hbudget : (d : Real) * Real.sqrt ((n : Real) * eps) / (eps * logScale n eps) ≤
      (n : Real) + m) :
    frontierRate n m d eps ≤ 2 * labelBenchmark n eps := by
  let S : Real := labelScale n eps
  let D : Real := ((n : Real) + m) * eps * logScale n eps
  let x : Real := (d : Real) / D
  have hS : 0 < S := mul_pos (by exact_mod_cast hn) heps
  have hlog : 0 < eps * logScale n eps := mul_pos heps (phase_logScale_pos n eps hn heps)
  have hD : 0 < D := by
    dsimp [D]
    rw [mul_assoc]
    exact mul_pos (by positivity) hlog
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hsquare : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS.le
  have hdim : (d : Real) * Real.sqrt S ≤ D := by
    simpa [D, S, labelScale, mul_assoc] using (div_le_iff₀ hlog).mp hbudget
  have hx : x * Real.sqrt S ≤ 1 := by
    dsimp [x]
    rw [div_mul_eq_mul_div]
    exact (div_le_one hD).mpr hdim
  have hxpos : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hD.le
  have hsq : x ^ 2 ≤ 1 / S := by
    apply (le_div_iff₀ hS).mpr
    have hprod : (x * Real.sqrt S) ^ 2 = x ^ 2 * S := by rw [mul_pow, hsquare]
    nlinarith [mul_nonneg (mul_nonneg hxpos hsqrt.le) (sub_nonneg.mpr hx)]
  change min 1 (1 / S + x ^ 2) ≤ 2 * min 1 S⁻¹
  by_cases hinv : S⁻¹ ≤ 1
  · rw [min_eq_right hinv]
    exact (min_le_right _ _).trans (by simpa only [one_div] using (show
      1 / S + x ^ 2 ≤ 2 * (1 / S) by linarith))
  · rw [min_eq_left (le_of_not_ge hinv)]
    exact (min_le_left _ _).trans (by norm_num)

/--
[Under the stated inputs and conditions](hyp:v,Rr,hc,_hC,hcmp,c,C), [Any sequence risk uniformly comparable to the displayed frontier has the consistency
phase](goal).
-/
-- @node: consistency_of_frontier_comparison
lemma consistency_of_frontier_comparison (v : ExperimentSeq) (Rr : Nat → Real)
    (c C : Real) (hc : 0 < c) (_hC : 0 < C)
    (hcmp : ∀ k, c * frontierRate (v k).n (v k).m (v k).d (v k).eps ≤ Rr k ∧
      Rr k ≤ C * frontierRate (v k).n (v k).m (v k).d (v k).eps) :
    Tendsto Rr atTop (nhds 0) ↔
      Tendsto (fun k => labelScale (v k).n (v k).eps) atTop atTop ∧
      (fun k => ((v k).d : Real)) =o[atTop]
        (fun k => (((v k).n : Real) + (v k).m) * (v k).eps * logScale (v k).n (v k).eps) := by
  let S : Nat → Real := fun k => labelScale (v k).n (v k).eps
  let D : Nat → Real := fun k =>
    (((v k).n : Real) + (v k).m) * (v k).eps * logScale (v k).n (v k).eps
  let z : Nat → Real := fun k => ((v k).d : Real) / D k
  let r : Nat → Real := fun k => frontierRate (v k).n (v k).m (v k).d (v k).eps
  have hS : ∀ k, 0 < S k := by
    intro k
    have hn : (0 : Real) < (v k).n := by exact_mod_cast (v k).n_pos
    exact mul_pos hn (v k).eps_pos
  have hD : ∀ k, 0 < D k := by
    intro k
    have hn : (0 : Real) < (v k).n := by exact_mod_cast (v k).n_pos
    have hell : 0 < logScale (v k).n (v k).eps := by
      apply Real.log_pos
      have hexp : (1 : Real) < Real.exp 1 := by
        exact Real.one_lt_exp_iff.mpr zero_lt_one
      change 1 < Real.exp 1 + S k
      linarith [hS k]
    exact mul_pos (mul_pos (by positivity) (v k).eps_pos) hell
  have hz : ∀ k, 0 ≤ z k := fun k => div_nonneg (Nat.cast_nonneg _) (hD k).le
  have hr : ∀ k, 0 ≤ r k := fun k =>
    (frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos).le
  have hlittle :
      (fun k => ((v k).d : Real)) =o[atTop] D ↔ Tendsto z atTop (nhds 0) :=
    isLittleO_iff_tendsto (fun k hk => False.elim ((hD k).ne' hk))
  have hrate : Tendsto Rr atTop (nhds 0) ↔ Tendsto r atTop (nhds 0) := by
    constructor
    · intro hR
      apply squeeze_zero hr (fun k => (le_div_iff₀ hc).2 ?_)
        (by simpa using hR.div_const c)
      simpa only [mul_comm] using (hcmp k).1
    · intro hR
      apply squeeze_zero (fun k => le_trans (mul_nonneg hc.le (hr k)) (hcmp k).1)
        (fun k => (hcmp k).2)
      simpa using hR.const_mul C
  rw [hrate, hlittle]
  constructor
  · intro hR
    -- A vanishing capped rate eventually lies strictly below its cap.
    have hcap : ∀ᶠ k in atTop, r k = 1 / S k + z k ^ 2 := by
      filter_upwards [hR.eventually_lt_const (by norm_num : (0 : Real) < 1)] with k hk
      dsimp [r, frontierRate, S, z, D] at hk ⊢
      exact min_eq_right (le_of_lt (by simpa only [min_lt_iff, lt_self_iff_false,
        false_or] using hk))
    have hsum : Tendsto (fun k => 1 / S k + z k ^ 2) atTop (nhds 0) :=
      hR.congr' hcap
    have hinv : Tendsto (fun k => (S k)⁻¹) atTop (nhds 0) := by
      apply squeeze_zero (fun k => inv_nonneg.mpr (hS k).le)
        (fun k => ?_) hsum
      simpa only [one_div] using le_add_of_nonneg_right (sq_nonneg (z k))
    have hsq : Tendsto (fun k => z k ^ 2) atTop (nhds 0) :=
      squeeze_zero (fun k => sq_nonneg _) (fun k =>
        le_add_of_nonneg_left (div_nonneg (by norm_num) (hS k).le)) hsum
    have hzlim : Tendsto z atTop (nhds 0) := by
      have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (hz _)] using ht
    have hinvpos : Tendsto (fun k => (S k)⁻¹) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hinv,
        Eventually.of_forall (fun k => inv_pos.mpr (hS k))⟩
    have hdiverge := tendsto_inv_nhdsGT_zero.comp hinvpos
    exact ⟨by simpa only [Function.comp_def, inv_inv] using hdiverge, hzlim⟩
  · rintro ⟨hdiverge, hzlim⟩
    have hinv : Tendsto (fun k => 1 / S k) atTop (nhds 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp hdiverge)
    have hsum : Tendsto (fun k => 1 / S k + z k ^ 2) atTop (nhds 0) := by
      simpa using hinv.add (hzlim.pow 2)
    apply squeeze_zero hr (fun k => min_le_right _ _) hsum

end CausalSmith.Stat.AnnotationRarearmFrontier

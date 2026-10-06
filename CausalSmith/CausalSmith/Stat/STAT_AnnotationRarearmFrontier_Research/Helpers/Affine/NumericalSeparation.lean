module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Concentration

/-!
Uniform numerical target separation for the affine priors, as in equation (10).
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:n,eps,heps), The logarithmic scale is at least one for nonnegative overlap.  This gives [the stated result](goal).-/
-- @node: affine_logScale_one_le
lemma affine_logScale_one_le (n : Nat) (eps : Real) (heps : 0 ≤ eps) :
    1 ≤ logScale n eps := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ Real.exp 1 + labelScale n eps by
      apply le_add_of_nonneg_right; unfold labelScale; positivity)
  simpa only [logScale, Real.log_exp] using h

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), The scheduled baseline mass is bounded below in terms of the public indices.  This gives [the stated result](goal).-/
-- @node: affine_tuning_b0_lower
lemma affine_tuning_b0_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    1 / (230400000 * ((n : Real) + m) * eps * logScale n eps) ≤
      (affineTuning n m d eps).b0 := by
  obtain ⟨hMlo, hMhi, hLlo, hLhi, _, _, _, _⟩ :=
    affine_tuning_bounds n m d eps hn hd heps heps'
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ m := Nat.cast_nonneg m
  have hell : 0 < logScale n eps := lt_of_lt_of_le (by norm_num)
    (affine_logScale_one_le n eps heps.le)
  have hMp : 0 < (affineTuning n m d eps).M := by linarith
  have hLp : 0 < ((affineTuning n m d eps).L : Real) := by linarith
  rw [affine_tuning_b0_identity n m d eps hn hd heps heps']
  apply one_div_le_one_div_of_le (by positivity)
  have hprod := mul_le_mul hMhi hLhi (by positivity : 0 ≤ ((affineTuning n m d eps).L : Real))
    (by positivity : 0 ≤ 256 * ((n : Real) + m))
  nlinarith [mul_le_mul_of_nonneg_right hprod heps.le]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,m,d), The floor cap retains at least half of its reciprocal mass budget.  This gives [the stated result](goal).-/
-- @node: affine_tuning_floor_mass_lower
lemma affine_tuning_floor_mass_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps) :
    1 / 200 ≤ (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) : Real) *
      (affineTuning n m d eps).b0 := by
  have hb := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.1
  have hK := affine_tuning_Kstar_pos n m d eps hn hd heps heps' hS
  have hf : 1 ≤ Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) := by
    change 0 < min (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0))) at hK
    omega
  have hfR : (1 : Real) ≤ Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) := by
    exact_mod_cast hf
  have hlt := Nat.lt_floor_add_one (1 / (100 * (affineTuning n m d eps).b0))
  have hhalf : 1 / (100 * (affineTuning n m d eps).b0) ≤
      2 * (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) : Real) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hhalf hb.le
  have hid : (1 / (100 * (affineTuning n m d eps).b0)) *
      (affineTuning n m d eps).b0 = 1 / 100 := by field_simp
  rw [hid] at hmul
  linarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,d,m), The actual rare-cell mass budget dominates the clipped public affine scale.  This gives [the stated result](goal).-/
-- @node: affine_tuning_total_mass_lower
lemma affine_tuning_total_mass_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps) :
    min ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) 1 / 460800000 ≤
      ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 := by
  have hb := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.1
  have hblo := affine_tuning_b0_lower n m d eps hn hd heps heps'
  have hfloor := affine_tuning_floor_mass_lower n m d eps hn hd heps heps' hS
  have hdR : (d : Real) / 2 ≤ (d - 1 : Nat) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    have : (2 : Real) ≤ d := by exact_mod_cast hd
    linarith
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ m := Nat.cast_nonneg m
  have hell : 0 < logScale n eps := lt_of_lt_of_le (by norm_num)
    (affine_logScale_one_le n eps heps.le)
  have hcell : (d : Real) / (((n : Real) + m) * eps * logScale n eps) / 460800000 ≤
      ((d - 1 : Nat) : Real) * (affineTuning n m d eps).b0 := by
    have hprod := mul_le_mul hdR hblo (by positivity) (by positivity)
    calc
      _ = (d : Real) / 2 * (1 / (230400000 * ((n : Real) + m) * eps * logScale n eps)) := by
        field_simp
        <;> ring
      _ ≤ _ := hprod
  change _ ≤ ((min (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0))) : Nat) : Real) * _
  by_cases hcap : d - 1 ≤ Nat.floor (1 / (100 * (affineTuning n m d eps).b0))
  · rw [min_eq_left hcap]
    exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans hcell
  · rw [min_eq_right (le_of_not_ge hcap)]
    have hclip : min ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) 1 /
        460800000 ≤ (1 : Real) / 200 := by
      have := min_le_right ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) 1
      linarith
    exact hclip.trans hfloor

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hS), The raw target mean gap has the uniform numerical scale claimed in equation (10).  This gives [the stated result](goal). -/
-- @node: affine_raw_target_mean_gap_uniform
lemma affine_raw_target_mean_gap_uniform (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    min ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) 1 / 10000000000 ≤
      (∫ lat, affineRawTarget n m d eps sigma true lat
        ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) -
      (∫ lat, affineRawTarget n m d eps sigma false lat
        ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) := by
  have hmass := affine_tuning_total_mass_lower n m d eps hn hd heps heps' hS
  have hgap := affine_raw_target_mean_gap n m d eps hn hd heps heps' sigma
  have hell : 0 < logScale n eps := lt_of_lt_of_le (by norm_num)
    (affine_logScale_one_le n eps heps.le)
  have hclip : 0 ≤ min ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) 1 := by
    apply le_min <;> positivity
  linarith

end CausalSmith.Stat.AnnotationRarearmFrontier

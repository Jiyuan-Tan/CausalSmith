module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.LightVariance
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Poisson pilot misclassification probabilities at the public bandwidth cutoff.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:htp,hB,hs,tp,B,s), [A heavy cell is selected as light with exponentially small probability](goal).
-/
-- @node: pilot_false_light_tail
lemma pilot_false_light_tail (tp B s : Real) (htp : 0 < tp) (hB : 0 < B) (hs : B < s) :
    (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4))) ≤
      Real.exp (-tp * s / 4) := by
  have hspos : 0 < s := hB.trans hs
  have hmean : 0 ≤ tp * s := (mul_pos htp hspos).le
  have hcut : (Nat.floor (tp * B / 4) : Real) <
      (Real.toNNReal (tp * s) : Real) / 4 := by
    rw [Real.coe_toNNReal _ hmean]
    have hfloor := Nat.floor_le (show 0 ≤ tp * B / 4 by positivity)
    have hmul := mul_lt_mul_of_pos_left hs htp
    linarith
  have htail := Causalean.Stat.Concentration.Poisson.poisson_le_cutoff_of_cutoff_lt_quarter
    (Real.toNNReal (tp * s)) (Nat.floor (tp * B / 4)) hcut
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
  simpa only [Measure.real, Set.Iic, Real.coe_toNNReal _ hmean,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), neg_mul] using hreal

/-- [Under the stated inputs and conditions](hyp:k,htp,ht,hs,tp,t,s), The heavy-branch probability times its inverse-count bias has a cutoff-only bound,
including at zero cell mass.  This gives [the stated result](goal).-/
-- @node: pilot_false_heavy_weighted_tail
lemma pilot_false_heavy_weighted_tail (tp t s : Real) (k : Nat)
    (htp : 0 < tp) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Ioi k) *
      Real.exp (-t * s) ≤ Real.exp (-Real.log (1 + t / tp) * (k : Real)) := by
  have h := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    (Real.toNNReal (tp * s)) k (r := t / tp) (by positivity)
  have heq : -(t / tp) * (Real.toNNReal (tp * s) : Real) = -t * s := by
    rw [Real.coe_toNNReal _ (mul_nonneg htp.le hs)]
    field_simp
  simpa only [heq, Set.Ioi] using h

/-- [Under the stated inputs and conditions](hyp:L,hL,htp,ht,hs,hratio,hscale,tp,t,B,s), The public bandwidth makes the weighted heavy-branch error exponentially small
in the degree, uniformly over every nonnegative cell mass.  This gives [the stated result](goal).-/
-- @node: pilot_false_heavy_absorption
lemma pilot_false_heavy_absorption (L : Nat) (tp t B s : Real)
    (hL : 4 ≤ L) (htp : 0 < tp) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hratio : 1 / 3 ≤ t / tp) (hscale : (2 : Real) ^ 20 * L ≤ tp * B) :
    (poissonMeasure (Real.toNNReal (tp * s))).real
        (Set.Ioi (Nat.floor (tp * B / 4))) * Real.exp (-t * s) ≤
      Real.exp (-30000 * (L : Real)) := by
  have hLreal : (4 : Real) ≤ L := by exact_mod_cast hL
  have hfloor := Nat.lt_floor_add_one (tp * B / 4)
  have hk : (2 : Real) ^ 20 * L / 8 ≤ (Nat.floor (tp * B / 4) : Real) := by
    norm_num at hscale ⊢
    linarith
  have hlog : (2 / 7 : Real) ≤ Real.log (1 + t / tp) := by
    have hbase := Real.le_log_one_add_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 3)
    norm_num at hbase
    exact hbase.trans (Real.log_le_log (by norm_num) (by linarith))
  calc
    _ ≤ Real.exp (-Real.log (1 + t / tp) * (Nat.floor (tp * B / 4) : Real)) :=
      pilot_false_heavy_weighted_tail tp t s _ htp ht hs
    _ ≤ Real.exp (-30000 * (L : Real)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right hlog
        (Nat.cast_nonneg (Nat.floor (tp * B / 4)) : (0 : Real) ≤ _)
      norm_num at hk
      nlinarith

/-- [Under the stated inputs and conditions](hyp:hS,htp,ht,hs,hratio,hscale,S,tp,t,B,s), Degree calibration turns the opposite pilot error into the required inverse
 twentieth power of the label scale.  This gives [the stated result](goal).-/
-- @node: pilot_false_heavy_public_scale
lemma pilot_false_heavy_public_scale (S tp t B s : Real)
    (hS : Real.exp 4096 ≤ S) (htp : 0 < tp) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hratio : 1 / 3 ≤ t / tp)
    (hscale : (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B) :
    (poissonMeasure (Real.toNNReal (tp * s))).real
        (Set.Ioi (Nat.floor (tp * B / 4))) * Real.exp (-t * s) ≤ (S ^ 20)⁻¹ := by
  let L := Nat.floor (Real.log S / 1024)
  have hcal := hybrid_degree_calibration S hS
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS
  have hL : 4 ≤ L := hcal.1
  have hy : Real.log S < 1280 * (L : Real) := hcal.2.1
  calc
    _ ≤ Real.exp (-30000 * (L : Real)) :=
      pilot_false_heavy_absorption L tp t B s hL htp ht hs hratio hscale
    _ ≤ (S ^ 20)⁻¹ := by
      apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).1
      rw [Real.log_exp, Real.log_inv, Real.log_pow]
      have hLnonneg : (0 : Real) ≤ L := Nat.cast_nonneg L
      norm_num
      linarith

/-- [Under the stated inputs and conditions](hyp:L,htp,ht,tp,t), The estimator's actual minimum-pool bandwidth satisfies the pilot scale condition.  This gives [the stated result](goal).-/
-- @node: hybrid_bandwidth_pilot_scale
lemma hybrid_bandwidth_pilot_scale (L : Nat) (tp t : Real)
    (htp : 0 < tp) (ht : 0 < t) :
    (2 : Real) ^ 20 * L ≤ tp * ((2 : Real) ^ 20 * L / min tp t) := by
  have hmin : 0 < min tp t := lt_min htp ht
  have hratio : 1 ≤ tp / min tp t := (one_le_div hmin).2 (min_le_left _ _)
  have hmul := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 ≤ (2 : Real) ^ 20 * L)
  calc
    _ ≤ (2 : Real) ^ 20 * L * (tp / min tp t) := by simpa using hmul
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:hS,htp,ht,hs,hratio,S,tp,t,s), With the prescribed bandwidth and pilot cutoff, the heavy selection probability
 times the inverse-count bias is at most the inverse twentieth power of S.  This gives [the stated result](goal).-/
-- @node: hybrid_false_heavy_bias_bound
lemma hybrid_false_heavy_bias_bound (S tp t s : Real)
    (hS : Real.exp 4096 ≤ S) (htp : 0 < tp) (ht : 0 < t)
    (hs : 0 ≤ s) (hratio : 1 / 3 ≤ t / tp) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    (1 - (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k0)) *
      Real.exp (-t * s) ≤ (S ^ 20)⁻¹ := by
  dsimp only
  have hcompl (k : Nat) :
      1 - (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k) =
        (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Ioi k) := by
    rw [← Set.compl_Iic, measureReal_compl (measurableSet_Iic)]
    simp
  rw [hcompl]
  exact pilot_false_heavy_public_scale S tp t _ s hS htp ht.le hs hratio
    (hybrid_bandwidth_pilot_scale _ tp t htp ht)

end CausalSmith.Stat.AnnotationRarearmFrontier

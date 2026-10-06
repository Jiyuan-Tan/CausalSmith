module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.PilotTails

/-!
Exponential absorption of false-light polynomial moments outside the bandwidth.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:L,hL,htp,hB,hs,hscale,tp,B,s), [The heavy-cell pilot tail absorbs the full factorial second-moment growth](goal).
-/
-- @node: false_light_absorption
lemma false_light_absorption (L : Nat) (tp B s : Real) (hL : 4 ≤ L)
    (htp : 0 < tp) (hB : 0 < B) (hs : B < s) (hscale : (2 : Real) ^ 20 * L ≤ tp * B) :
    Real.exp (-tp * s / 4) * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2) ≤
      Real.exp (-200000 * (L : Real)) := by
  have hLreal : (4 : Real) ≤ L := by exact_mod_cast hL
  have hLpos : 0 < (L : Real) := by linarith
  have hz : 1 < s / B := (one_lt_div hB).2 hs
  have hlogz : Real.log (1 + s / B) ≤ s / B := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + s / B)
    linarith
  have hlogtwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hscaled : (2 : Real) ^ 20 * L * (s / B) ≤ tp * s := by
    have h := mul_le_mul_of_nonneg_right hscale (by linarith : 0 ≤ s / B)
    have heq : tp * B * (s / B) = tp * s := by field_simp
    rwa [heq] at h
  apply (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp,
    Real.log_pow, Real.log_pow, Real.log_pow]
  norm_num at hscaled ⊢
  have hpoly : ((2 : Real) * L + 2) * Real.log (1 + s / B) ≤
      ((2 : Real) * L + 2) * (s / B) :=
    mul_le_mul_of_nonneg_left hlogz (by positivity)
  have hpower : (L : Real) * (24 * Real.log 2) ≤ 24 * L := by
    nlinarith
  have hdegree : ((2 : Real) * L + 2) * (s / B) ≤
      (5 / 2 : Real) * L * (s / B) := by
    nlinarith
  have hratio : (L : Real) ≤ L * (s / B) := by nlinarith
  nlinarith


end CausalSmith.Stat.AnnotationRarearmFrontier

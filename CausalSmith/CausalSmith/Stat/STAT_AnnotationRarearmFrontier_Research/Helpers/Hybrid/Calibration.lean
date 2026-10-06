module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Estimator

/-!
Numerical degree and exponential absorption calibrated in S, uniformly in overlap.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:S,hS), [The rare-label degree yields the numerical absorption needed in the hybrid proof](goal).
-/
-- @node: hybrid_degree_calibration
lemma hybrid_degree_calibration (S : Real) (hS : Real.exp 4096 ≤ S) :
    let L := Nat.floor (Real.log S / 1024)
    4 ≤ L ∧ Real.log S < 1280 * (L : Real) ∧
      ((2 : Real) ^ 24) ^ L * (L : Real) ^ 3 ≤ Real.sqrt S ∧
      Real.exp (-200000 * (L : Real)) ≤ (S ^ 20)⁻¹ := by
  let L := Nat.floor (Real.log S / 1024)
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS
  have hy : 4096 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).2 hS
  have hL : 4 ≤ L := Nat.le_floor (by dsimp; linarith)
  have hLreal : (4 : Real) ≤ L := by exact_mod_cast hL
  have hLpos : 0 < (L : Real) := by linarith
  have hfloor : (L : Real) ≤ Real.log S / 1024 :=
    Nat.floor_le (by linarith)
  have hceil : Real.log S / 1024 < (L : Real) + 1 :=
    Nat.lt_floor_add_one _
  have hyupper : Real.log S < 1280 * (L : Real) := by linarith
  refine ⟨hL, hyupper, ?_, ?_⟩
  · apply (Real.log_le_log_iff (by positivity) (Real.sqrt_pos.2 hSpos)).1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_sqrt hSpos.le]
    have hlogtwo : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
    have hlogL : Real.log (L : Real) ≤ (L : Real) :=
      (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
    norm_num
    nlinarith
  · apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).1
    rw [Real.log_exp, Real.log_inv, Real.log_pow]
    norm_num
    linarith

end CausalSmith.Stat.AnnotationRarearmFrontier

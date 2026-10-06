module
public import Causalean.Stat.Nonparametric.HistogramRegression.PatternMeans

/-!
# Clipping and empty-default comparisons

Clipping an empirical mean to the unit interval contracts squared distance
to every unit-interval center. An empty cell contributes at most one when
the default lies in the same interval. These deterministic comparisons do
not assume bounded responses; they separate estimator algebra from the iid
variance analysis. The clipped squared error is integrable under every iid
probability law with measurable inputs.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [A unit-interval default and center](hyp:ha,hc) give
[a pointwise bound on squared cell-estimation error by the squared totalized
centered empirical mean plus the empty-cell indicator](goal). -/
theorem cellEstimate_sq_error_le {m : ℕ}
    (label : A → κ) (X : Ω → A) (Y : Ω → ℝ) (a c : ℝ) (k : κ)
    (z : Fin m → Ω) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (cellEstimate label X Y a k z - c) ^ 2 ≤
      (centeredCellMean label X Y c k z) ^ 2 +
        (if cellCount label X k z = 0 then 1 else 0) := by
  -- Split on count zero. Then centeredCellMean=0 and |a-c|≤1.
  -- For positive count N, expand cellSum(Y-c)=cellSum(Y)-c*N
  -- using Finset.sum_sub_distrib and Finset.card_filter. Thus the centered
  -- mean equals cellSum(Y)/N-c. For any t and c∈[0,1],
  -- (clip t-c)^2≤(t-c)^2: split t≤0, 0≤t≤1, and 1≤t, and use
  -- sq_le_sq / nlinarith. No bounds on Y or probabilistic assumptions are needed.
  classical
  by_cases hn : cellCount label X k z = 0
  · simp only [cellEstimate, hn, if_pos, centeredCellMean, Nat.cast_zero,
      div_zero]
    simpa using (sq_le_sq' (by linarith [ha.1, hc.2])
      (by linarith [ha.2, hc.1]) : (a - c) ^ 2 ≤ (1 : ℝ) ^ 2)
  · have hsum : cellSum label X (fun ω => Y ω - c) k z =
        cellSum label X Y k z - c * (cellCount label X k z : ℝ) := by
      unfold cellSum cellCount
      rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_sub_distrib]
      simp [mul_comm]
    have hmean : centeredCellMean label X Y c k z =
        cellSum label X Y k z / (cellCount label X k z : ℝ) - c := by
      rw [centeredCellMean, hsum, sub_div, mul_div_cancel_right₀ c
        (Nat.cast_ne_zero.mpr hn)]
    simp only [cellEstimate, hn, if_false, hmean, add_zero]
    generalize cellSum label X Y k z / (cellCount label X k z : ℝ) = t
    by_cases ht0 : t ≤ 0
    · rw [clip, min_eq_right (by linarith : t ≤ 1), max_eq_left ht0]
      nlinarith [mul_nonneg (neg_nonneg.mpr ht0) hc.1, sq_nonneg t]
    · have ht0' : 0 ≤ t := le_of_not_ge ht0
      by_cases ht1 : t ≤ 1
      · simp [clip, min_eq_right ht1, max_eq_right ht0']
      · have ht1' : 1 ≤ t := le_of_not_ge ht1
        rw [clip, min_eq_left ht1', max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1') (sub_nonneg.mpr hc.2),
          sq_nonneg (t - 1)]

/-- [Measurable partition inputs and responses](hyp:hlabel,hX,hY) and
[a unit-interval default and center](hyp:ha,hc) imply
[the clipped cell-estimation squared error is integrable under iid sampling](goal). -/
theorem integrable_cellEstimate_sq_error {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (a c : ℝ) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun z : Fin m → Ω => (cellEstimate label X Y a k z - c) ^ 2)
      (Measure.pi (fun _ : Fin m => μ)) := by
  -- Measurability follows from measurable_cellEstimate, subtraction, and square.
  -- Every estimate is in [0,1] by the definition of clip and ha; no hbound
  -- or tuple-ae argument is needed. Dominate the loss by the constant 1
  -- using Integrable.mono' and sq_le_sq' with bounds -1≤estimate-c≤1.
  have hmeas : Measurable (fun z : Fin m → Ω =>
      (cellEstimate label X Y a k z - c) ^ 2) :=
    ((measurable_cellEstimate label X Y a k hlabel hX hY).sub
      measurable_const).pow_const 2
  refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro z
  have he : cellEstimate label X Y a k z ∈ Set.Icc (0 : ℝ) 1 := by
    unfold cellEstimate
    split_ifs
    · exact ha
    · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa using (sq_le_sq' (by linarith [he.1, hc.2])
    (by linarith [he.2, hc.1]) :
    (cellEstimate label X Y a k z - c) ^ 2 ≤ (1 : ℝ) ^ 2)

end

end Causalean.Stat.Nonparametric.HistogramRegression

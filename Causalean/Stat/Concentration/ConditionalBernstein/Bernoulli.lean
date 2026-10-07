module
public import Causalean.Stat.Concentration.ConditionalBernstein.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Centered measurable-bin indicators

These one-coordinate facts supply the Bernoulli means, second moments, and bounds used
on each conditional design fibre. No density or regularity of the outcome law is assumed.
-/

public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory

variable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {bin : Set Y}

/-- A bin has [probability between zero and one](goal) under a [probability law](hyp:μ). -/
theorem binProbability_mem_Icc : μ.real bin ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The indicator of a [measurable bin](hyp:hbin), centered by its probability under
the [law](hyp:μ), is [integrable](goal). -/
theorem integrable_centered_bin (hbin : MeasurableSet bin) :
    Integrable (fun y => binIndicator bin y - μ.real bin) μ := by
  exact ((integrable_const (1 : ℝ)).indicator hbin).sub
    (integrable_const (μ.real bin))

/-- The squared centered indicator of a [measurable bin](hyp:hbin) under the
[law](hyp:μ) is [integrable](goal). -/
theorem integrable_sq_centered_bin (hbin : MeasurableSet bin) :
    Integrable (fun y => (binIndicator bin y - μ.real bin) ^ 2) μ := by
  have hi : Integrable (binIndicator bin) μ :=
    (integrable_const (1 : ℝ)).indicator hbin
  refine ((hi.const_mul (1 - 2 * μ.real bin)).add
    (integrable_const (μ.real bin ^ 2))).congr ?_
  filter_upwards [] with y
  by_cases hy : y ∈ bin
  · simp [binIndicator, hy]
    ring
  · simp [binIndicator, hy]

/-- Centering the indicator of a [measurable bin](hyp:hbin) by its probability under
the [law](hyp:μ) gives [mean zero](goal). -/
theorem integral_centered_bin (hbin : MeasurableSet bin) :
    (∫ y, (binIndicator bin y - μ.real bin) ∂μ) = 0 := by
  have hi : Integrable (binIndicator bin) μ :=
    (integrable_const (1 : ℝ)).indicator hbin
  rw [integral_sub hi (integrable_const (μ.real bin))]
  simp [binIndicator, integral_indicator_const, hbin]

/-- For a [measurable bin](hyp:hbin) with probability p under a [probability law](hyp:μ),
[the expected square of the bin indicator minus p equals p (1 − p)](goal).

Expand the square using that the indicator squared is the indicator; integrate the
three terms, using the preceding integrability and mean lemmas. This is the variance
calculation that must be derived, rather than assumed in a histogram theorem. -/
theorem integral_sq_centered_bin (hbin : MeasurableSet bin) :
    (∫ y, (binIndicator bin y - μ.real bin) ^ 2 ∂μ) =
      μ.real bin * (1 - μ.real bin) := by
  have hi : Integrable (binIndicator bin) μ :=
    (integrable_const (1 : ℝ)).indicator hbin
  have hexpand : (fun y => (binIndicator bin y - μ.real bin) ^ 2) =
      (fun y => (1 - 2 * μ.real bin) * binIndicator bin y + μ.real bin ^ 2) := by
    funext y
    by_cases hy : y ∈ bin
    · simp [binIndicator, hy]
      ring
    · simp [binIndicator, hy]
  rw [hexpand, integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
  simp only [binIndicator, integral_indicator_const (1 : ℝ) hbin,
    smul_eq_mul, mul_one, integral_const, probReal_univ, one_mul]
  ring

/-- A bin indicator centered by its probability under the [law](hyp:μ) is
[pointwise bounded in absolute value by one](goal). -/
theorem abs_centered_bin_le_one (y : Y) :
    |binIndicator bin y - μ.real bin| ≤ 1 := by
  rcases binProbability_mem_Icc μ (bin := bin) with ⟨hp0, hp1⟩
  by_cases hy : y ∈ bin
  · simp only [binIndicator, Set.indicator_of_mem hy]
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  · simp only [binIndicator, Set.indicator_of_notMem hy, zero_sub, abs_neg]
    rwa [abs_of_nonneg hp0]

end Causalean.Stat.Concentration.ConditionalBernstein

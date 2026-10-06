module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Scalar bounded marks and centered moments

Bounded measurable marks are integrable to every natural power. A mark in [0,1] has a mean
in [0,1] and a centered value of absolute magnitude at most one. Consequently every centered
absolute moment of order at least two is bounded by the mark's variance.

The variance API is Mathlib's `ProbabilityTheory.variance`, with the bridge
`ProbabilityTheory.variance_eq_integral`; no additional integrability hypothesis is imposed
on consumers because it follows from boundedness.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A [measurable real mark](hyp:hg) whose [absolute value is at most one](hyp:hb) has
[integrable natural powers](goal) under a [probability law](hyp:μ). -/
@[fun_prop]
theorem integrable_pow_of_abs_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1) (n : ℕ) :
    Integrable (fun y => g y ^ n) μ := by
  -- Dominate |g|^n by the integrable constant 1.
  refine (integrable_const (1 : ℝ)).mono' (hg.pow_const n).aestronglyMeasurable ?_
  exact ae_of_all μ fun y => by
    simpa only [Real.norm_eq_abs, abs_pow] using
      (pow_le_one₀ (abs_nonneg (g y)) (hb y) : |g y| ^ n ≤ 1)

/-- For a [measurable real mark](hyp:hg) with [absolute value at most one](hyp:hb), the
absolute integral of a power [of order at least two](hyp:hn) is [at most its second
moment](goal) under a [probability law](hyp:μ). -/
theorem abs_integral_pow_le_secondMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    |∫ y, g y ^ n ∂μ| ≤ ∫ y, g y ^ 2 ∂μ := by
  -- |g|^n ≤ |g|^2 follows from |g|≤1. Integrate the pointwise inequality and use
  -- `abs_integral_le_integral_abs`, with the integrability lemma above.
  have hi := integrable_pow_of_abs_le_one μ g hg hb n
  have hi2 := integrable_pow_of_abs_le_one μ g hg hb 2
  refine abs_integral_le_integral_abs.trans (integral_mono hi.abs hi2 ?_)
  intro y
  change |g y ^ n| ≤ g y ^ 2
  rw [abs_pow, ← sq_abs]
  exact pow_le_pow_of_le_one (abs_nonneg (g y)) (hb y) hn

/-- A [measurable mark](hyp:hf) [valued in the unit interval](hyp:h0,h1) has its
[mean in the unit interval](goal) under a [probability law](hyp:μ). -/
theorem mean_mem_unitInterval (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1) :
    0 ≤ (∫ y, f y ∂μ) ∧ (∫ y, f y ∂μ) ≤ 1 := by
  -- Integrability follows from `integrable_pow_of_abs_le_one` with n=1.
  have hb : ∀ y, |f y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (h0 y)]
    exact h1 y
  have hi : Integrable f μ := by
    simpa only [pow_one] using integrable_pow_of_abs_le_one μ f hf hb 1
  refine ⟨integral_nonneg h0, ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) h1

/-- A [measurable mark](hyp:hf) [valued in the unit interval](hyp:h0,h1) differs from
its mean by [at most one in absolute value](goal) under a [probability law](hyp:μ). -/
theorem abs_centered_mark_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1)
    (y : Ω) : |f y - ∫ z, f z ∂μ| ≤ 1 := by
  obtain ⟨hm0, hm1⟩ := mean_mem_unitInterval μ f hf h0 h1
  rw [abs_le]
  constructor <;> linarith [h0 y, h1 y]

/-- Subtracting the mean from a [measurable mark](hyp:hf) [in the unit
interval](hyp:h0,h1) gives a [zero integral](goal) under a [probability law](hyp:μ). -/
theorem integral_centered_mark_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1) :
    (∫ y, (f y - ∫ z, f z ∂μ) ∂μ) = 0 := by
  have hb : ∀ y, |f y| ≤ 1 := fun y => by rw [abs_of_nonneg (h0 y)]; exact h1 y
  have hi : Integrable f μ := by
    simpa only [pow_one] using integrable_pow_of_abs_le_one μ f hf hb 1
  rw [integral_sub hi (integrable_const _)]
  simp

/-- Every centered power [of order at least two](hyp:hn) of a [measurable
mark](hyp:hf) [in the unit interval](hyp:h0,h1) has its [absolute integral bounded by
the variance](goal) under a [probability law](hyp:μ). -/
theorem abs_integral_centered_pow_le_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    |∫ y, (f y - ∫ z, f z ∂μ) ^ n ∂μ| ≤ variance f μ := by
  rw [variance_eq_integral hf.aemeasurable]
  exact abs_integral_pow_le_secondMoment μ _ (hf.sub measurable_const)
    (abs_centered_mark_le_one μ f hf h0 h1) n hn

end Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

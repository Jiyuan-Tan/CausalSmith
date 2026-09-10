import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw

/-!
# Self-normalized Poisson deviations: basic definitions

This module defines the deviation, random radius, deterministic local scale,
and bad event used by the quantitative Poisson moment bounds.  The Poisson
parameter is an `NNReal`, so nonnegativity is encoded in its type.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

/-- Given [a nonnegative mean](hyp:lambda) and [a natural-valued count](hyp:w), the
[absolute deviation of the count from its mean](goal) is their absolute difference. -/
noncomputable def deviation (lambda : ℝ≥0) (w : ℕ) : ℝ :=
  |(w : ℝ) - (lambda : ℝ)|

/-- Given [a logarithmic level](hyp:L) and [a natural-valued count](hyp:w), the
[self-normalizing random radius](goal) is the square root of count times level, plus the level. -/
noncomputable def radius (L : ℝ) (w : ℕ) : ℝ :=
  Real.sqrt ((w : ℝ) * L) + L

/-- Given [a nonnegative Poisson mean](hyp:lambda) and [a logarithmic level](hyp:L), the
[deterministic local scale](goal) is the square root of mean times level, plus the level. -/
noncomputable def localScale (lambda : ℝ≥0) (L : ℝ) : ℝ :=
  Real.sqrt ((lambda : ℝ) * L) + L

/-- Given [a multiplier and logarithmic level](hyp:H,L) and [a nonnegative Poisson mean](hyp:lambda),
the [self-normalized bad event](goal) contains counts whose absolute deviation exceeds one quarter
of the multiplier times their random radius. -/
def badEvent (H L : ℝ) (lambda : ℝ≥0) : Set ℕ :=
  {w | deviation lambda w > (H / 4) * radius L w}

/-- The [universal self-normalization multiplier](goal) is 1024. -/
def universalH : ℝ := 1024

/-- The [pre-aggregation exponential decay rate](goal) is 40. -/
def scalarDecay : ℝ := 40

/-- The [universal self-normalization multiplier is strictly positive](goal). -/
theorem universalH_pos : 0 < universalH := by
  norm_num [universalH]

/-- The [scalar exponential decay rate is at least forty](goal), and hence is positive. -/
theorem forty_le_scalarDecay : (40 : ℝ) ≤ scalarDecay := by
  norm_num [scalarDecay]

/-- The [absolute-deviation function for a nonnegative mean](hyp:lambda) is [measurable](goal). -/
@[fun_prop]
theorem measurable_deviation (lambda : ℝ≥0) : Measurable (deviation lambda) := by
  fun_prop

/-- The [self-normalizing radius at a fixed logarithmic level](hyp:L) is [measurable](goal). -/
@[fun_prop]
theorem measurable_radius (L : ℝ) : Measurable (radius L) := by
  fun_prop

/-- Given [a multiplier and logarithmic level](hyp:H,L) and [a nonnegative Poisson mean](hyp:lambda),
the [self-normalized bad event is measurable](goal). -/
theorem measurableSet_badEvent (H L : ℝ) (lambda : ℝ≥0) :
    MeasurableSet (badEvent H L lambda) := by
  exact measurableSet_lt (measurable_const.mul (measurable_radius L))
    (measurable_deviation lambda)

private theorem integrable_natCast_poisson (lambda : ℝ≥0) :
    Integrable (fun w : ℕ => (w : ℝ)) (poissonMeasure lambda) := by
  rw [integrable_poissonMeasure_iff]
  apply (summable_nat_add_iff 1).mp
  have h := (Real.summable_pow_div_factorial (lambda : ℝ)).mul_left
    (Real.exp (-(lambda : ℝ)) * (lambda : ℝ))
  refine h.congr ?_
  intro n
  simp only [Nat.cast_add, Nat.cast_one, norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
    Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp

/-- The [absolute deviation under the Poisson law with a nonnegative mean](hyp:lambda) is
[integrable](goal). -/
theorem integrable_deviation (lambda : ℝ≥0) :
    Integrable (deviation lambda) (poissonMeasure lambda) := by
  change Integrable (fun w : ℕ => |(w : ℝ) - (lambda : ℝ)|) _
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    ((integrable_natCast_poisson lambda).sub (integrable_const _)).norm

/-- Under [a Poisson law with a nonnegative mean](hyp:lambda), the [self-normalizing radius at a
nonnegative logarithmic level](hyp:L,hL) is [integrable](goal). -/
theorem integrable_radius (lambda : ℝ≥0) (L : ℝ) (hL : 0 ≤ L) :
    Integrable (radius L) (poissonMeasure lambda) := by
  have hlin : Integrable (fun w : ℕ => (w : ℝ) * L) (poissonMeasure lambda) :=
    (integrable_natCast_poisson lambda).mul_const L
  have hc : Integrable (fun _ : ℕ => (1 + L : ℝ)) (poissonMeasure lambda) :=
    integrable_const _
  have hg := hlin.add hc
  refine hg.mono' (measurable_radius L).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  have hx : 0 ≤ (w : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hsqrt : Real.sqrt ((w : ℝ) * L) ≤ (w : ℝ) * L + 1 := by
    have hs := Real.sq_sqrt hx
    have hsq := sq_nonneg (Real.sqrt ((w : ℝ) * L) - 1)
    nlinarith
  change ‖Real.sqrt ((w : ℝ) * L) + L‖ ≤ (w : ℝ) * L + (1 + L)
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · linarith
  · exact add_nonneg (Real.sqrt_nonneg _) hL

/-- Under a zero-mean Poisson law, [the count is almost surely zero](goal). -/
theorem poissonMeasure_zero_ae :
    (fun w : ℕ => w) =ᵐ[poissonMeasure 0] 0 := by
  rw [Filter.EventuallyEq, ae_iff]
  change poissonMeasure 0 {a : ℕ | a ≠ 0} = 0
  have hcomp : poissonMeasure 0 ({0}ᶜ) = 0 := by
    rw [measure_compl (MeasurableSet.singleton 0) (measure_ne_top _ _),
      poissonMeasure_singleton]
    norm_num
  rw [show {a : ℕ | a ≠ 0} = {0}ᶜ by ext; simp]
  exact hcomp

end Causalean.Stat.Concentration.PoissonSelfNormalized

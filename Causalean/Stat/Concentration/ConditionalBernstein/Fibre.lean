module
public import Causalean.Stat.Concentration.ConditionalBernstein.Bernoulli
public import Causalean.Stat.Concentration.ConditionalBernstein.TotalVariance
public import Mathlib.Probability.Independence.Integration

/-!
# Conditional Bernstein bounds on a complete design fibre

Fixing the complete design vector makes the outcome coordinates independent under the
finite product kernel. This module derives the centered Bernoulli summand data, bounds
the sum of second moments by `pMax * cellCount`, and proves the two-sided count tail.
No positive-count condition is imposed; zero-count cells have identically zero deviation.
-/

public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {D Y C : Type*} [MeasurableSpace D] [MeasurableSpace Y] {n : ℕ}
    (key : D → C) (K : Kernel D Y) [IsMarkovKernel K]
    {bin : Set Y} (c : C) (x : Fin n → D)

/-- The centered bin-count summands for a [fixed complete design vector](hyp:x),
[cell](hyp:key,c), and [measurable bin](hyp:hbin) under a [Markov outcome kernel](hyp:K)
are [independent on that design fibre](goal).

Rewrite `finProductKernel_apply` and apply Mathlib's `iIndepFun_pi` directly to
`fun i y => cellIndicator key c (x i) * (binIndicator bin y - binProbability K bin (x i))`.
Its coordinate measurability uses `measurable_binIndicator`, subtraction of a constant,
and multiplication by a constant. No additional independence infrastructure is needed.
-/
theorem iIndepFun_centeredSummand (hbin : MeasurableSet bin) :
    iIndepFun (centeredSummand key K bin c x) (Causalean.Stat.finProductKernel n K x) := by
  rw [Causalean.Stat.finProductKernel_apply]
  exact iIndepFun_pi (fun i =>
    (((measurable_binIndicator hbin).sub measurable_const).const_mul
      (cellIndicator key c (x i))).aemeasurable)

omit [IsMarkovKernel K] in
/-- Each centered count summand for the [design vector](hyp:x), [cell](hyp:key,c),
[kernel](hyp:K), and [measurable bin](hyp:hbin) is [measurable as a function of the
outcome vector](goal). -/
@[fun_prop] theorem measurable_centeredSummand (hbin : MeasurableSet bin) (i : Fin n) :
    Measurable (centeredSummand key K bin c x i) := by
  exact (((measurable_binIndicator hbin).comp (measurable_pi_apply i)).sub
    measurable_const).const_mul _

/-- Each centered bin-count summand for the [cell and design vector](hyp:key,c,x)
under a [Markov outcome kernel](hyp:K) is [bounded in absolute value by one](goal). -/
theorem abs_centeredSummand_le_one (i : Fin n) (y : Fin n → Y) :
    |centeredSummand key K bin c x i y| ≤ 1 := by
  classical
  by_cases hc : key (x i) = c
  · simpa [centeredSummand, cellIndicator, binProbability, hc] using
      abs_centered_bin_le_one (K (x i)) (bin := bin) (y i)
  · simp [centeredSummand, cellIndicator, hc]

/-- Each centered count summand for the [design vector](hyp:x), [cell](hyp:key,c),
[kernel](hyp:K), and [measurable bin](hyp:hbin) is [integrable on its design fibre](goal).

After `finProductKernel_apply`, `integrable_comp_eval` lifts the one-coordinate
`integrable_centered_bin` result; use `Integrable.const_mul` for the cell indicator.
-/
theorem integrable_centeredSummand (hbin : MeasurableSet bin) (i : Fin n) :
    Integrable (centeredSummand key K bin c x i) (Causalean.Stat.finProductKernel n K x) := by
  rw [Causalean.Stat.finProductKernel_apply]
  exact (integrable_comp_eval (μ := fun j : Fin n => K (x j))
    (integrable_centered_bin (K (x i)) hbin)).const_mul (cellIndicator key c (x i))

/-- Each squared centered count summand for the [design vector](hyp:x), [cell](hyp:key,c),
[kernel](hyp:K), and [measurable bin](hyp:hbin) is [integrable on its design fibre](goal).

Lift `integrable_sq_centered_bin` using `integrable_comp_eval` and rewrite `mul_pow`.
The cell factor is constant on the fibre, including when it is zero.
-/
theorem integrable_sq_centeredSummand (hbin : MeasurableSet bin) (i : Fin n) :
    Integrable (fun y => centeredSummand key K bin c x i y ^ 2)
      (Causalean.Stat.finProductKernel n K x) := by
  rw [Causalean.Stat.finProductKernel_apply]
  simpa only [centeredSummand, binProbability, mul_pow] using
    (integrable_comp_eval (μ := fun j : Fin n => K (x j))
      (integrable_sq_centered_bin (K (x i)) hbin)).const_mul
        (cellIndicator key c (x i) ^ 2)

/-- Each centered count summand for the [design vector](hyp:x), [cell](hyp:key,c),
[kernel](hyp:K), and [measurable bin](hyp:hbin) has [zero conditional mean](goal).

Use `integral_const_mul`, `integral_comp_eval`, and `integral_centered_bin` after
rewriting the fibre law. The one-coordinate integrability lemma supplies the
AEStronglyMeasurable hypothesis of `integral_comp_eval`.
-/
theorem integral_centeredSummand (hbin : MeasurableSet bin) (i : Fin n) :
    (∫ y, centeredSummand key K bin c x i y ∂Causalean.Stat.finProductKernel n K x) = 0 := by
  rw [Causalean.Stat.finProductKernel_apply]
  change (∫ y, cellIndicator key c (x i) *
    (binIndicator bin (y i) - (K (x i)).real bin)
    ∂Measure.pi (fun j : Fin n => K (x j))) = 0
  rw [integral_const_mul, integral_comp_eval (μ := fun j : Fin n => K (x j)) (i := i)
    (integrable_centered_bin (K (x i)) hbin).aestronglyMeasurable,
    integral_centered_bin (K (x i)) hbin, mul_zero]

/-- A centered count summand for the [design vector](hyp:x), [cell](hyp:key,c),
[kernel](hyp:K), and [measurable bin](hyp:hbin) has [the cell indicator times the
conditional Bernoulli variance as its second moment](goal).

Use `integral_comp_eval` and `integral_sq_centered_bin` on the product measure after
expanding `mul_pow` and pulling out the constant cell factor. Split on `key (x i) = c`
to reduce the squared cell indicator to the cell indicator; its values are zero and one.
-/
theorem integral_sq_centeredSummand (hbin : MeasurableSet bin) (i : Fin n) :
    (∫ y, centeredSummand key K bin c x i y ^ 2 ∂Causalean.Stat.finProductKernel n K x) =
      cellIndicator key c (x i) * binProbability K bin (x i) *
        (1 - binProbability K bin (x i)) := by
  classical
  rw [Causalean.Stat.finProductKernel_apply]
  simp only [centeredSummand, binProbability, mul_pow]
  rw [integral_const_mul, integral_comp_eval (μ := fun j : Fin n => K (x j)) (i := i)
    (integrable_sq_centered_bin (K (x i)) hbin).aestronglyMeasurable,
    integral_sq_centered_bin (K (x i)) hbin]
  by_cases hc : key (x i) = c <;> simp [cellIndicator, hc]

/-- If [conditional bin probabilities obey a cell envelope](hyp:hprob),
then the [centered summands](hyp:key,K,hbin,c,x) have
[total second moment at most the envelope times the realized cell count](goal).

Use `integral_sq_centeredSummand`, bound `p*(1-p) ≤ p ≤ pMax` on active coordinates,
and use `cellCount_cast`. Inactive coordinates have zero variance. This is the crucial
budget calculation; replacing the realized cell count by n would not meet the API.
-/
theorem sum_second_moments_le (hbin : MeasurableSet bin) {pMax : ℝ}
    (hprob : ∀ i, key (x i) = c → binProbability K bin (x i) ≤ pMax) :
    (∑ i, ∫ y, centeredSummand key K bin c x i y ^ 2
      ∂Causalean.Stat.finProductKernel n K x) ≤ pMax * (cellCount key c x : ℝ) := by
  classical
  simp_rw [integral_sq_centeredSummand key K c x hbin]
  rw [cellCount_cast, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : key (x i) = c
  · simp only [cellIndicator, if_pos hc, one_mul]
    have hp0 : 0 ≤ binProbability K bin (x i) := measureReal_nonneg
    have hp := hprob i hc
    nlinarith [sq_nonneg (binProbability K bin (x i))]
  · simp [cellIndicator, hc]

/-- Fix a [complete design vector](hyp:x), and draw the outcomes independently across
coordinates, each from a [Markov outcome kernel](hyp:K) at its design entry. For a
[design cell and measurable bin](hyp:key,c,hbin), suppose the [kernel probability of the bin
is at most a nonnegative number pMax at every design entry in the cell](hyp:hprob,hpMax) and
the [tail parameter u is nonnegative](hyp:hu). Then [the probability that the joint count
differs from its conditional mean by strictly more than √(2 · pMax · N · u) + u, where N is
the number of design entries in the cell, is at most 2 exp(−u)](goal).

Apply `bernstein_sum_totalVariance_abs_gt` to the preceding summand data and rewrite
with `jointCount_sub_conditionalMean`. Both n = 0 and cellCount = 0 are included.
-/
theorem fibre_pair_tail_le (hbin : MeasurableSet bin) {pMax u : ℝ} (hpMax : 0 ≤ pMax) (hu : 0 ≤ u)
    (hprob : ∀ i, key (x i) = c → binProbability K bin (x i) ≤ pMax) :
    (Causalean.Stat.finProductKernel n K x).real
      {y | bernsteinRadius (pMax * (cellCount key c x : ℝ)) u <
        |(jointCount key bin c x y : ℝ) - conditionalMean key K bin c x|} ≤
      2 * Real.exp (-u) := by
  have hv : 0 ≤ pMax * (cellCount key c x : ℝ) :=
    mul_nonneg hpMax (Nat.cast_nonneg _)
  simpa only [jointCount_sub_conditionalMean] using
    bernstein_sum_totalVariance_abs_gt hv hu
      (iIndepFun_centeredSummand key K c x hbin)
      (measurable_centeredSummand key K c x hbin)
      (integrable_centeredSummand key K c x hbin)
      (integrable_sq_centeredSummand key K c x hbin)
      (integral_centeredSummand key K c x hbin)
      (fun i => Filter.Eventually.of_forall (abs_centeredSummand_le_one key K c x i))
      (sum_second_moments_le key K c x hbin hprob)

end Causalean.Stat.Concentration.ConditionalBernstein

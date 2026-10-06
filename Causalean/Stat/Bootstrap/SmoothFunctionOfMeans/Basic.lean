module

public import Causalean.Stat.Bootstrap.EfronResampling.Basic
public import Causalean.Stat.CLT.SampleFnEstimator
public import Causalean.Stat.CLT.VectorWLLN

/-!
# Smooth functions of finite-dimensional sample means

This module defines estimators obtained by applying a scalar function to the canonical finite
mean, together with a reusable notion of almost-sure conditional bootstrap tightness and the
basic ratio-of-means specialization.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mu : Measure Omega} {P : Measure X}

/-- Given [a finite vector of observations](hyp:x), its [finite mean](goal) is the coordinate sum
scaled by the reciprocal of the vector length. -/
def finMean {n : ℕ} (x : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- Given [a moment function](hyp:g), [a scalar transform](hyp:h), [a sample size](hyp:n), and
[data of that size](hyp:x), the [smooth-function-of-means estimator](goal) applies the transform
to the finite average of the moment vectors. -/
def smoothMeanEstimator (g : X → E) (h : E → ℝ)
    (n : ℕ) (x : Fin n → X) : ℝ :=
  h (finMean (fun i ↦ g (x i)))

/-- If [the moment function](hyp:hg) and [the transform](hyp:hh) are measurable, then [the
smooth-function-of-means estimator is measurable at every sample size](goal). -/
@[fun_prop]
theorem measurable_smoothMeanEstimator {g : X → E} {h : E → ℝ}
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hg : Measurable g) (hh : Measurable h) (n : ℕ) :
    Measurable (smoothMeanEstimator g h n) := by
  unfold smoothMeanEstimator finMean
  apply hh.comp
  exact (Finset.measurable_sum _
    (fun i _ ↦ hg.comp (measurable_pi_apply i))).const_smul _

/-- For [an iid sample](hyp:S) and [a bootstrap statistic](hyp:T),
[almost-sure conditional bootstrap tightness](goal) means that, for almost every realized data
sequence, the conditional bootstrap norm tails are eventually uniformly small. -/
def ConditionallyBoundedInProbability
    (S : IIDSample Omega X mu P)
    (T : (n : ℕ) → (Fin n → X) → (Fin n → X) → E) : Prop :=
  ∀ᵐ omega ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      (bootstrapResample (S.sampleVector n omega)).real
        {xstar | M < ‖T n (S.sampleVector n omega) xstar‖} < epsilon

/-- For [a bivariate moment function](hyp:g), [a sample size](hyp:n), and [observed data](hyp:x),
the [ratio-of-means estimator](goal) divides the first finite sample moment by the second. -/
def ratioOfMeansEstimator
    (g : X → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (x : Fin n → X) : ℝ :=
  (finMean (fun i ↦ g (x i))) 0 / (finMean (fun i ↦ g (x i))) 1

/-- Given [a bivariate vector](hyp:z), its [coordinate ratio](goal) is its first coordinate divided
by its second coordinate. -/
def coordinateRatio (z : EuclideanSpace ℝ (Fin 2)) : ℝ := z 0 / z 1

/-- Given [a bivariate moment function](hyp:g), its [population mean](hyp:m), and [an
observation](hyp:x), the [ratio influence function](goal) is the quotient-rule linearization of
the first moment divided by the second. -/
def ratioInfluence (g : X → EuclideanSpace ℝ (Fin 2))
    (m : EuclideanSpace ℝ (Fin 2)) (x : X) : ℝ :=
  (g x 0 - m 0) / m 1 - m 0 * (g x 1 - m 1) / (m 1) ^ 2

/-- The ratio-of-means estimator [built from a moment function](hyp:g), [at a sample size](hyp:n)
and [data vector](hyp:x), [equals the smooth mean estimator using the coordinate ratio](goal). -/
theorem ratioOfMeansEstimator_eq_smoothMeanEstimator
    (g : X → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (x : Fin n → X) :
    ratioOfMeansEstimator g n x = smoothMeanEstimator g coordinateRatio n x := by
  rfl

end

end Causalean.Stat

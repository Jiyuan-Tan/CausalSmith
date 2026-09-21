/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer.Basic

/-!
# Failure bounds for a shared random scale

This module bounds the probability that either ordered Poisson pool is too short.  The
prior-predictive bound separates parameters whose shared scale lies below a deterministic
floor from the two conditional Poisson lower tails above that floor.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Minimax.MomentMatchedMixture

universe uTheta uX uY

variable {Theta : Type uTheta} {X : Type uX} {Y : Type uY}
  [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [a raw experiment kernel](hyp:K), [the first mark kernel](hyp:P), [the second mark
kernel](hyp:Q), [a shared scale](hyp:S), [the first intensity multiplier](hyp:u), [the second
intensity multiplier](hyp:v), [the raw-experiment law](hyp:hraw), [the first requested
length](hyp:n), [the second requested length](hyp:m), and [a parameter value](hyp:theta),
[conditional retention failure is bounded by the sum of the two Poisson lower tails](goal). -/
theorem conditional_retentionFailure_le_poissonLowerTails
    (K : Kernel Theta (RawTwoPool X Y))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (u v : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment K P Q S u v)
    (n m : ℕ) (theta : Theta) :
    K theta (retentionFailureSet (X := X) (Y := Y) n m) ≤
      (poissonMeasure (u * S theta)) (Set.Iio n) +
        (poissonMeasure (v * S theta)) (Set.Iio m) := by
  /-
  Rewrite the raw fibre with `hraw`; express failure as the union of the two marginal
  count events; apply the measure union bound and
  `finitePoissonSampleLaw_map_count` to identify both marginals.
  -/
  rw [hraw theta]
  let muX := finitePoissonSampleLaw (P theta) (u * S theta)
  let muY := finitePoissonSampleLaw (Q theta) (v * S theta)
  let AX : Set (FiniteSample X) := {s | s.count < n}
  let AY : Set (FiniteSample Y) := {s | s.count < m}
  have hfailure : retentionFailureSet (X := X) (Y := Y) n m =
      (AX ×ˢ Set.univ) ∪ (Set.univ ×ˢ AY) := by
    ext z
    simp [retentionFailureSet, AX, AY]
  have hcountX : muX AX = (poissonMeasure (u * S theta)) (Set.Iio n) := by
    rw [← finitePoissonSampleLaw_map_count (P theta) (u * S theta),
      Measure.map_apply measurable_finiteSample_count measurableSet_Iio]
    rfl
  have hcountY : muY AY = (poissonMeasure (v * S theta)) (Set.Iio m) := by
    rw [← finitePoissonSampleLaw_map_count (Q theta) (v * S theta),
      Measure.map_apply measurable_finiteSample_count measurableSet_Iio]
    rfl
  rw [hfailure]
  refine (measure_union_le _ _).trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
    mul_one, one_mul, hcountX, hcountY]

/-- Given [a parameter prior](hyp:pi), [a raw experiment kernel](hyp:K), [the first mark
kernel](hyp:P), [the second mark kernel](hyp:Q), [a measurable shared scale](hyp:S,hS), [the
two intensity multipliers](hyp:u,v), [a deterministic scale floor](hyp:s0), [the
raw-experiment law](hyp:hraw), [the first requested length](hyp:n), and [the second requested
length](hyp:m), [prior-predictive retention failure is bounded by low-scale mass plus the
integrated high-scale Poisson tails](goal). -/
theorem priorPredictive_retentionFailure_le_scaleFloor_add_integratedTails
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (K : Kernel Theta (RawTwoPool X Y))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (hS : Measurable S) (u v s0 : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment K P Q S u v)
    (n m : ℕ) :
    priorPredictive pi K (retentionFailureSet (X := X) (Y := Y) n m) ≤
      pi {theta | S theta < s0} +
        ∫⁻ theta in {theta | s0 ≤ S theta},
          ((poissonMeasure (u * S theta)) (Set.Iio n) +
            (poissonMeasure (v * S theta)) (Set.Iio m)) ∂pi := by
  /-
  Expand `priorPredictive_apply`, split the parameter integral over the measurable scale
  event and its complement, bound the low-scale integrand by one, and use
  `conditional_retentionFailure_le_poissonLowerTails` on the high-scale part.
  -/
  let A : Set Theta := {theta | S theta < s0}
  have hA : MeasurableSet A := measurableSet_lt hS measurable_const
  have hAc : Aᶜ = {theta | s0 ≤ S theta} := by
    ext theta
    simp [A]
  rw [priorPredictive_apply pi K (measurableSet_retentionFailureSet n m),
    ← lintegral_add_compl
      (fun theta => K theta (retentionFailureSet (X := X) (Y := Y) n m)) hA]
  apply add_le_add
  · calc
      (∫⁻ theta in A,
          K theta (retentionFailureSet (X := X) (Y := Y) n m) ∂pi) ≤
          ∫⁻ _theta in A, 1 ∂pi := by
            apply lintegral_mono
            intro theta
            change K theta (retentionFailureSet (X := X) (Y := Y) n m) ≤ 1
            rw [hraw theta]
            exact prob_le_one
      _ = pi A := by simp
  · rw [hAc]
    apply lintegral_mono
    intro theta
    exact conditional_retentionFailure_le_poissonLowerTails
      K P Q S u v hraw n m theta

/-- Given [a parameter prior](hyp:pi), [a raw experiment kernel](hyp:K), [the first mark
kernel](hyp:P), [the second mark kernel](hyp:Q), [a measurable shared scale](hyp:S,hS), [the
two intensity multipliers](hyp:u,v), [a deterministic scale floor](hyp:s0), [the
raw-experiment law](hyp:hraw), [the first requested length](hyp:n), [the second requested
length](hyp:m), [a scale-error budget](hyp:epsScale), [a first-tail budget](hyp:epsX), [a
second-tail budget](hyp:epsY), [the scale concentration bound](hyp:hscale), [the first
uniform tail bound](hyp:htailX), and [the second uniform tail bound](hyp:htailY),
[prior-predictive retention failure is at most the sum of the three error budgets](goal). -/
theorem priorPredictive_retentionFailure_le
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (K : Kernel Theta (RawTwoPool X Y))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (hS : Measurable S) (u v s0 : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment K P Q S u v)
    (n m : ℕ) (epsScale epsX epsY : ℝ≥0∞)
    (hscale : pi {theta | S theta < s0} ≤ epsScale)
    (htailX : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (u * S theta)) (Set.Iio n) ≤ epsX)
    (htailY : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (v * S theta)) (Set.Iio m) ≤ epsY) :
    priorPredictive pi K (retentionFailureSet (X := X) (Y := Y) n m) ≤
      epsScale + epsX + epsY := by
  /-
  Apply the scale-floor decomposition.  Monotonicity of the lower integral and the two
  supplied tail bounds control the high-scale integrand by `epsX + epsY`; the probability
  prior gives mass at most one to the restricted region.
  -/
  refine (priorPredictive_retentionFailure_le_scaleFloor_add_integratedTails
    pi K P Q S hS u v s0 hraw n m).trans ?_
  have htail :
      (∫⁻ theta in {theta | s0 ≤ S theta},
        ((poissonMeasure (u * S theta)) (Set.Iio n) +
          (poissonMeasure (v * S theta)) (Set.Iio m)) ∂pi) ≤ epsX + epsY := by
    calc
      (∫⁻ theta in {theta | s0 ≤ S theta},
          ((poissonMeasure (u * S theta)) (Set.Iio n) +
            (poissonMeasure (v * S theta)) (Set.Iio m)) ∂pi) ≤
          ∫⁻ _theta in {theta | s0 ≤ S theta}, epsX + epsY ∂pi := by
            apply setLIntegral_mono measurable_const
            intro theta htheta
            exact add_le_add (htailX theta htheta) (htailY theta htheta)
      _ = (epsX + epsY) * pi {theta | s0 ≤ S theta} :=
        setLIntegral_const _ _
      _ ≤ epsX + epsY := mul_le_of_le_one_right (by positivity) prob_le_one
  exact (add_le_add hscale htail).trans_eq (by simp [add_assoc])

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer.Risk

/-!
# Random-scale unequal two-pool minimax transfer

This module composes a raw two-fuzzy-prior Bayes lower bound, shared-scale concentration,
two Poisson lower-tail controls, and an independent small-signal fixed-sample floor.  The
result is a reusable minimax lower bound for two fixed pools of unequal sizes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

universe uTheta uX uY uA uZ

variable {Theta : Type uTheta} {X : Type uX} {Y : Type uY} {A : Type uA}
  [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A]

/-- Given [a fixed experiment kernel](hyp:Kfixed), [a loss](hyp:loss), [a raw Bayes lower
bound](hyp:rawLower), [a transfer penalty](hyp:penalty), [a small-signal fixed-sample
floor](hyp:smallFloor), [a rulewise raw-to-fixed transfer bound](hyp:htransfer), and [the
small-signal floor bound](hyp:hsmall), [the fixed experiment's minimax risk is at least the
larger of the penalized raw bound and the small-signal floor](goal). -/
theorem minimaxDecisionRisk_lower_of_rawBayesTransfer
    {Z : Type uZ} [MeasurableSpace Z]
    (Kfixed : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞)
    (rawLower penalty smallFloor : ℝ≥0∞)
    (htransfer : ∀ rule : {f : Z → A // Measurable f},
      rawLower ≤ worstCaseDecisionRisk Kfixed loss rule.1 + penalty)
    (hsmall : smallFloor ≤ minimaxDecisionRisk Kfixed loss) :
    max (rawLower - penalty) smallFloor ≤ minimaxDecisionRisk Kfixed loss := by
  /-
  For each measurable rule, residuation for truncated subtraction turns `htransfer` into
  `rawLower - penalty ≤ worstCaseRisk`.  Take the infimum over rules, then combine that bound
  with `hsmall` using `max_le`.
  -/
  apply max_le
  · unfold minimaxDecisionRisk
    apply le_iInf
    intro rule
    apply tsub_le_iff_left.mpr
    simpa [add_comm] using htransfer rule
  · exact hsmall

/-- Given [two fuzzy parameter priors](hyp:pi0,pi1), [a raw experiment](hyp:Kraw), [a fixed
two-pool experiment](hyp:Kfixed), [the first mark kernel](hyp:P), [the second mark kernel](hyp:Q),
[a measurable shared scale](hyp:S,hS), [two intensity multipliers](hyp:u,v), [a scale
floor](hyp:s0), [the raw experiment law](hyp:hraw), [the fixed experiment law](hyp:hfixed), [a
loss](hyp:loss), [a finite loss bound](hyp:B,hB,hbound), [joint measurability of the
loss](hyp:hloss), [fallback first and second arrays](hyp:fallbackX,fallbackY), [a fallback
action](hyp:fallbackA), [a raw lower bound](hyp:rawLower,hrawLower), [a small-signal
floor](hyp:smallFloor,hsmall), [a scale-error budget](hyp:epsScale,hscale0,hscale1),
[two Poisson-tail budgets](hyp:epsX,epsY,htailX,htailY),
[the fixed unequal-pool minimax risk is at least the larger of the penalized fuzzy-prior lower
bound and the small-signal floor](goal).

The intensity multipliers may in particular be chosen proportional to the unequal fixed sample
sizes. Exact ordered retention preserves the complete auxiliary iid law rather than merely
selected auxiliary summaries. -/
theorem randomScale_twoFuzzy_minimax_lower_transfer
    (pi0 pi1 : Measure Theta) [IsProbabilityMeasure pi0] [IsProbabilityMeasure pi1]
    (Kraw : Kernel Theta (RawTwoPool X Y))
    (Kfixed : Kernel Theta (FixedPools (X := X) (Y := Y) n m))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (hS : Measurable S) (u v s0 : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment Kraw P Q S u v)
    (hfixed : IsFixedTwoPoolExperiment n m Kfixed P Q)
    (loss : Theta → A → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hloss : Measurable (Function.uncurry loss))
    (hbound : ∀ theta a, loss theta a ≤ B)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A)
    (rawLower smallFloor epsScale epsX epsY : ℝ≥0∞)
    (hrawLower : ∀ rawRule : RawTwoPool X Y → A, Measurable rawRule →
      rawLower ≤ max (bayesDecisionRisk pi0 Kraw loss rawRule)
        (bayesDecisionRisk pi1 Kraw loss rawRule))
    (hscale0 : pi0 {theta | S theta < s0} ≤ epsScale)
    (hscale1 : pi1 {theta | S theta < s0} ≤ epsScale)
    (htailX : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (u * S theta)) (Set.Iio n) ≤ epsX)
    (htailY : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (v * S theta)) (Set.Iio m) ≤ epsY)
    (hsmall : smallFloor ≤ minimaxDecisionRisk Kfixed loss) :
    max (rawLower - B * (epsScale + epsX + epsY)) smallFloor ≤
      minimaxDecisionRisk Kfixed loss := by
  /-
  Apply `priorPredictive_retentionFailure_le` under each fuzzy prior.  For an arbitrary
  measurable fixed rule, form the single `transferredRawRule`; the raw fuzzy lower bound and
  the two Bayes-to-worst-case transfer inequalities show
  `rawLower ≤ fixedWorstCase + B * (epsScale + epsX + epsY)`.  Finish with
  `minimaxDecisionRisk_lower_of_rawBayesTransfer` and `hsmall`.
  -/
  refine minimaxDecisionRisk_lower_of_rawBayesTransfer Kfixed loss rawLower
    (B * (epsScale + epsX + epsY)) smallFloor ?_ hsmall
  intro rule
  let rawRule :=
    transferredRawRule n m rule.1 fallbackX fallbackY fallbackA
  have hrawRule : Measurable rawRule := by
    exact measurable_transferredRawRule n m rule.2 fallbackX fallbackY fallbackA
  have hfail0 := priorPredictive_retentionFailure_le pi0 Kraw P Q S hS u v s0
    hraw n m epsScale epsX epsY hscale0 htailX htailY
  have hfail1 := priorPredictive_retentionFailure_le pi1 Kraw P Q S hS u v s0
    hraw n m epsScale epsX epsY hscale1 htailX htailY
  have hrisk0 :=
    bayesDecisionRisk_transferredRawRule_le_worstCase_add
      pi0 Kraw Kfixed P Q S u v hraw hfixed loss B
      (epsScale + epsX + epsY) hB hloss hbound hfail0 rule.1 rule.2
      fallbackX fallbackY fallbackA
  have hrisk1 :=
    bayesDecisionRisk_transferredRawRule_le_worstCase_add
      pi1 Kraw Kfixed P Q S u v hraw hfixed loss B
      (epsScale + epsX + epsY) hB hloss hbound hfail1 rule.1 rule.2
      fallbackX fallbackY fallbackA
  exact (hrawLower rawRule hrawRule).trans (max_le hrisk0 hrisk1)

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

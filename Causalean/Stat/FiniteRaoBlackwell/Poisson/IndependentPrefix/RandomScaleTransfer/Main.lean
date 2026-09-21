/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Risk

/-!
# Random-scale unequal two-pool minimax transfer

This module combines a raw two-fuzzy-prior Bayes lower bound with shared-scale concentration
and two Poisson lower-tail controls.  The result transfers the raw bound, minus the resulting
bounded-loss penalty, to the minimax risk of two fixed pools of unequal sizes.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

universe uTheta uX uY uA uZ

variable {Theta : Type uTheta} {X : Type uX} {Y : Type uY} {A : Type uA}
  [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A]

/-- Given [a fixed experiment kernel](hyp:Kfixed), [a loss](hyp:loss), [a raw Bayes lower
bound](hyp:rawLower), [a transfer penalty](hyp:penalty), and [a rulewise raw-to-fixed transfer
bound](hyp:htransfer), [the fixed experiment's minimax risk is at least the raw bound reduced by
the penalty](goal).

A caller holding a separate lower bound on the same minimax risk may combine it with this one
using `max_le`; that combination is not part of this theorem. -/
theorem minimaxDecisionRisk_lower_of_rawBayesTransfer
    {Z : Type uZ} [MeasurableSpace Z]
    (Kfixed : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞)
    (rawLower penalty : ℝ≥0∞)
    (htransfer : ∀ rule : {f : Z → A // Measurable f},
      rawLower ≤ worstCaseDecisionRisk Kfixed loss rule.1 + penalty) :
    rawLower - penalty ≤ minimaxDecisionRisk Kfixed loss := by
  /-
  For each measurable rule, residuation for truncated subtraction turns `htransfer` into
  `rawLower - penalty ≤ worst-case risk`. Take the infimum over rules.
  -/
  unfold minimaxDecisionRisk
  apply le_iInf
  intro rule
  apply tsub_le_iff_left.mpr
  simpa [add_comm] using htransfer rule

/-- Given [two fuzzy parameter priors](hyp:pi0,pi1), [a raw experiment](hyp:Kraw), [a fixed
two-pool experiment](hyp:Kfixed), [the first mark kernel](hyp:P), [the second mark kernel](hyp:Q),
[a measurable shared scale](hyp:S,hS), [two intensity multipliers](hyp:u,v), [a scale
floor](hyp:s0), [the raw experiment law](hyp:hraw), [the fixed experiment law](hyp:hfixed), [a
loss](hyp:loss), [a finite loss bound](hyp:B,hB,hbound), [joint measurability of the
loss](hyp:hloss), [fallback first and second arrays](hyp:fallbackX,fallbackY), [a fallback
action](hyp:fallbackA), [a raw lower bound](hyp:rawLower,hrawLower), [a scale-error
budget](hyp:epsScale,hscale0,hscale1), [two Poisson-tail budgets](hyp:epsX,epsY,htailX,htailY),
[the fixed two-pool minimax risk is at least the fuzzy-prior lower bound reduced by the loss
bound times the total budget](goal).

The intensity multipliers may in particular be chosen proportional to the potentially unequal fixed sample
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
    (rawLower epsScale epsX epsY : ℝ≥0∞)
    (hrawLower : ∀ rawRule : RawTwoPool X Y → A, Measurable rawRule →
      rawLower ≤ max (bayesDecisionRisk pi0 Kraw loss rawRule)
        (bayesDecisionRisk pi1 Kraw loss rawRule))
    (hscale0 : pi0 {theta | S theta < s0} ≤ epsScale)
    (hscale1 : pi1 {theta | S theta < s0} ≤ epsScale)
    (htailX : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (u * S theta)) (Set.Iio n) ≤ epsX)
    (htailY : ∀ theta, s0 ≤ S theta →
      (poissonMeasure (v * S theta)) (Set.Iio m) ≤ epsY)
    :
    rawLower - B * (epsScale + epsX + epsY) ≤
      minimaxDecisionRisk Kfixed loss := by
  /-
  Apply `priorPredictive_retentionFailure_le` under each fuzzy prior.  For an arbitrary
  measurable fixed rule, form the single `transferredRawRule`; the raw fuzzy lower bound and
  the two Bayes-to-worst-case transfer inequalities show
  `rawLower ≤ fixedWorstCase + B * (epsScale + epsX + epsY)`.  Finish with
  `minimaxDecisionRisk_lower_of_rawBayesTransfer`.
  -/
  refine minimaxDecisionRisk_lower_of_rawBayesTransfer Kfixed loss rawLower
    (B * (epsScale + epsX + epsY)) ?_
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

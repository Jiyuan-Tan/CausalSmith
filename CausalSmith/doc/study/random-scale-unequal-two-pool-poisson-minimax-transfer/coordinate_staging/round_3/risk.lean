/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer.Failure

/-!
# Bounded-loss decision transfer

This module defines general nonnegative decision risks and transfers any measurable rule on
two fixed unequal pools to the raw random-scale Poisson experiment.  Exact ordered retention
handles the successful-count event; bounded loss pays only for count failure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

open Causalean.Stat.Minimax.MomentMatchedMixture

universe uTheta uX uY uA uZ

variable {Theta : Type uTheta} {X : Type uX} {Y : Type uY} {A : Type uA}
  [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A]

/-- Given [an experiment kernel](hyp:K), [a nonnegative loss](hyp:loss), [a decision
rule](hyp:rule), and [a parameter value](hyp:theta), [the decision risk](goal) is the expected
loss under that parameter's experiment law. [It is given by its lower integral](step:1). -/
noncomputable def decisionRisk {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞) (rule : Z → A)
    (theta : Theta) : ℝ≥0∞ :=
  ∫⁻ z, loss theta (rule z) ∂K theta

/-- Given [a parameter prior](hyp:pi), [an experiment kernel](hyp:K), [a nonnegative
loss](hyp:loss), and [a decision rule](hyp:rule), [the Bayes decision risk](goal) averages
the rule's parameterwise risks. [It is given by the prior lower integral](step:1). -/
noncomputable def bayesDecisionRisk {Z : Type uZ} [MeasurableSpace Z]
    (pi : Measure Theta) (K : Kernel Theta Z)
    (loss : Theta → A → ℝ≥0∞) (rule : Z → A) : ℝ≥0∞ :=
  ∫⁻ theta, decisionRisk K loss rule theta ∂pi

/-- Given [an experiment kernel](hyp:K), [a nonnegative loss](hyp:loss), and [a decision
rule](hyp:rule), [the worst-case decision risk](goal) is the largest parameterwise risk.
[It is given by the supremum over parameters](step:1). -/
noncomputable def worstCaseDecisionRisk {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞) (rule : Z → A) : ℝ≥0∞ :=
  ⨆ theta, decisionRisk K loss rule theta

/-- Given [an experiment kernel](hyp:K) and [a nonnegative loss](hyp:loss), [the minimax
decision risk](goal) is the smallest worst-case risk attainable by a measurable rule.
[It is given by the infimum over measurable rules](step:1). -/
noncomputable def minimaxDecisionRisk {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ rule : {f : Z → A // Measurable f}, worstCaseDecisionRisk K loss rule.1

/-- Given [the first requested length](hyp:n), [the second requested length](hyp:m), [a fixed
sample rule](hyp:rule), [a fallback first array](hyp:fallbackX), [a fallback second
array](hyp:fallbackY),
and [a fallback action](hyp:fallbackA), [the transferred raw rule](goal) uses retained prefixes
on count success and the fallback action otherwise. [It is given by the success test](step:1). -/
noncomputable def transferredRawRule (n m : ℕ)
    (rule : FixedPools (X := X) (Y := Y) n m → A)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A) :
    RawTwoPool X Y → A := fun z =>
  if n ≤ z.1.count ∧ m ≤ z.2.count then
    rule (twoPoolOrderedRetention fallbackX fallbackY z)
  else fallbackA

/-- Given [the first requested length](hyp:n), [the second requested length](hyp:m), [a
measurable fixed-sample rule](hyp:rule,hrule), [a fallback first array](hyp:fallbackX), [a
fallback second array](hyp:fallbackY), and [a fallback action](hyp:fallbackA), [the transferred
raw rule is measurable](goal). -/
theorem measurable_transferredRawRule (n m : ℕ)
    {rule : FixedPools (X := X) (Y := Y) n m → A} (hrule : Measurable rule)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A) :
    Measurable (transferredRawRule n m rule fallbackX fallbackY fallbackA) := by
  unfold transferredRawRule
  exact Measurable.ite (measurableSet_retentionSuccessSet n m)
    (hrule.comp (measurable_twoPoolOrderedRetention fallbackX fallbackY)) measurable_const

/-- Given [an s-finite experiment kernel](hyp:K), [a jointly measurable loss](hyp:loss,hloss),
and [a measurable rule](hyp:rule,hrule), [parameterwise decision risk is measurable as a
function of the parameter](goal). -/
theorem measurable_decisionRisk {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Theta Z) [IsSFiniteKernel K] {loss : Theta → A → ℝ≥0∞}
    (hloss : Measurable (Function.uncurry loss))
    {rule : Z → A} (hrule : Measurable rule) :
    Measurable (decisionRisk K loss rule) := by
  /-
  Apply `Measurable.lintegral_kernel_prod_right` to the jointly measurable integrand
  `(theta, z) ↦ loss theta (rule z)`.  The s-finiteness assumption is essential for the
  parameterized-integral theorem and is automatic for the probability kernels used below.
  -/
  unfold decisionRisk
  apply Measurable.lintegral_kernel_prod_right
    (κ := K) (f := fun theta z => loss theta (rule z))
  exact hloss.comp (measurable_fst.prodMk (hrule.comp measurable_snd))

/-- Given [a raw experiment](hyp:Kraw), [a fixed-pool experiment](hyp:Kfixed), [the first
mark kernel](hyp:P), [the second mark kernel](hyp:Q), [a shared scale](hyp:S), [two intensity
multipliers](hyp:u,v), [the raw experiment law](hyp:hraw), [the fixed experiment law](hyp:hfixed),
[a loss](hyp:loss), [a finite loss bound](hyp:B,hB,hbound), [joint measurability of the
loss](hyp:hloss), [a measurable fixed rule](hyp:rule,hrule), [a fallback first
array](hyp:fallbackX),
[a fallback second array](hyp:fallbackY), [a fallback action](hyp:fallbackA), and [a parameter
value](hyp:theta), [the transferred raw-rule risk is at most fixed risk plus bounded failure
probability](goal). -/
theorem decisionRisk_transferredRawRule_le
    (Kraw : Kernel Theta (RawTwoPool X Y))
    (Kfixed : Kernel Theta (FixedPools (X := X) (Y := Y) n m))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (u v : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment Kraw P Q S u v)
    (hfixed : IsFixedTwoPoolExperiment n m Kfixed P Q)
    (loss : Theta → A → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hloss : Measurable (Function.uncurry loss))
    (hbound : ∀ theta a, loss theta a ≤ B)
    (rule : FixedPools (X := X) (Y := Y) n m → A) (hrule : Measurable rule)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A)
    (theta : Theta) :
    decisionRisk Kraw loss
        (transferredRawRule n m rule fallbackX fallbackY fallbackA) theta ≤
      decisionRisk Kfixed loss rule theta +
        B * Kraw theta (retentionFailureSet (X := X) (Y := Y) n m) := by
  /-
  Split the raw measure over success and failure.  On success, rewrite the pushforward by
  `map_twoPoolOrderedRetention_restrict_success`; its scalar success mass is at most one,
  and `hfixed` identifies the fixed risk.  On failure, the transferred rule is constant and
  `hbound` bounds its integral by `B` times the failure mass.
  -/
  let E : Set (RawTwoPool X Y) := retentionSuccessSet n m
  have hE : MeasurableSet E := measurableSet_retentionSuccessSet n m
  have hlossTheta : Measurable (loss theta) :=
    hloss.comp (measurable_const.prodMk measurable_id)
  have hfixedIntegrand : Measurable (fun z => loss theta (rule z)) :=
    hlossTheta.comp hrule
  have hsuccess :
      (∫⁻ z in E,
          loss theta (transferredRawRule n m rule fallbackX fallbackY fallbackA z) ∂Kraw theta) ≤
        decisionRisk Kfixed loss rule theta := by
    have hsuccessEq :
        (∫⁻ z in E,
            loss theta (transferredRawRule n m rule fallbackX fallbackY fallbackA z) ∂Kraw theta) =
          ∫⁻ z in E, loss theta (rule
            (twoPoolOrderedRetention fallbackX fallbackY z)) ∂Kraw theta := by
      apply setLIntegral_congr_fun hE
      intro z hz
      simp only [transferredRawRule]
      rw [if_pos]
      simpa [E, retentionSuccessSet] using hz
    unfold decisionRisk
    rw [hsuccessEq, ← lintegral_map hfixedIntegrand
        (measurable_twoPoolOrderedRetention fallbackX fallbackY)]
    rw [hraw theta,
      map_twoPoolOrderedRetention_restrict_success
        (P theta) (Q theta) (u * S theta) (v * S theta)
        n m fallbackX fallbackY,
      lintegral_smul_measure, smul_eq_mul, hfixed theta]
    apply mul_le_of_le_one_left (by positivity)
    calc
      (poissonMeasure (u * S theta)) (Set.Ici n) *
          (poissonMeasure (v * S theta)) (Set.Ici m) ≤ 1 * 1 :=
        mul_le_mul prob_le_one prob_le_one (by positivity) (by positivity)
      _ = 1 := one_mul 1
  have hfailure :
      (∫⁻ z in Eᶜ,
          loss theta (transferredRawRule n m rule fallbackX fallbackY fallbackA z) ∂Kraw theta) ≤
        B * Kraw theta (retentionFailureSet (X := X) (Y := Y) n m) := by
    calc
      (∫⁻ z in Eᶜ,
          loss theta (transferredRawRule n m rule fallbackX fallbackY fallbackA z) ∂Kraw theta) ≤
          ∫⁻ _z in Eᶜ, B ∂Kraw theta := by
            apply lintegral_mono
            exact fun z => hbound theta _
      _ = B * Kraw theta Eᶜ := setLIntegral_const _ _
      _ = B * Kraw theta (retentionFailureSet (X := X) (Y := Y) n m) := by
        congr 2
        simpa [E] using congrArg compl
          (retentionSuccessSet_eq_compl_failureSet (X := X) (Y := Y) n m)
  unfold decisionRisk
  rw [← lintegral_add_compl
    (fun z => loss theta
      (transferredRawRule n m rule fallbackX fallbackY fallbackA z)) hE]
  exact add_le_add hsuccess hfailure

/-- Given [a parameter prior](hyp:pi), [a raw experiment](hyp:Kraw), [a fixed-pool
experiment](hyp:Kfixed), [the first mark kernel](hyp:P), [the second mark kernel](hyp:Q), [a
shared scale](hyp:S), [two intensity multipliers](hyp:u,v), [the raw experiment law](hyp:hraw),
[the fixed experiment law](hyp:hfixed), [a loss](hyp:loss), [a finite loss bound](hyp:B,hB,hbound),
[joint measurability of the loss](hyp:hloss), [a measurable fixed rule](hyp:rule,hrule), [a
fallback first array](hyp:fallbackX), [a fallback second array](hyp:fallbackY), and [a fallback
action](hyp:fallbackA), [the raw transferred-rule Bayes risk is bounded by fixed Bayes risk
plus prior-predictive failure cost](goal). -/
theorem bayesDecisionRisk_transferredRawRule_le
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (Kraw : Kernel Theta (RawTwoPool X Y))
    (Kfixed : Kernel Theta (FixedPools (X := X) (Y := Y) n m))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (u v : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment Kraw P Q S u v)
    (hfixed : IsFixedTwoPoolExperiment n m Kfixed P Q)
    (loss : Theta → A → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hloss : Measurable (Function.uncurry loss))
    (hbound : ∀ theta a, loss theta a ≤ B)
    (rule : FixedPools (X := X) (Y := Y) n m → A) (hrule : Measurable rule)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A) :
    bayesDecisionRisk pi Kraw loss
        (transferredRawRule n m rule fallbackX fallbackY fallbackA) ≤
      bayesDecisionRisk pi Kfixed loss rule +
        B * priorPredictive pi Kraw
          (retentionFailureSet (X := X) (Y := Y) n m) := by
  /-
  Integrate `decisionRisk_transferredRawRule_le` over the prior.  Use
  `lintegral_add_left`, `lintegral_const_mul`, and `priorPredictive_apply` to identify the
  integrated conditional failure probability.
  -/
  letI : IsMarkovKernel Kraw := ⟨fun theta => by
    rw [hraw theta]
    infer_instance⟩
  letI : IsMarkovKernel Kfixed := ⟨fun theta => by
    rw [hfixed theta]
    unfold fixedPoolsLaw
    infer_instance⟩
  have hfixedRisk : Measurable (decisionRisk Kfixed loss rule) := by
    unfold decisionRisk
    apply Measurable.lintegral_kernel_prod_right
      (κ := Kfixed) (f := fun theta z => loss theta (rule z))
    exact hloss.comp (measurable_fst.prodMk (hrule.comp measurable_snd))
  unfold bayesDecisionRisk
  calc
    (∫⁻ theta,
        decisionRisk Kraw loss
          (transferredRawRule n m rule fallbackX fallbackY fallbackA) theta ∂pi) ≤
        ∫⁻ theta, decisionRisk Kfixed loss rule theta +
          B * Kraw theta (retentionFailureSet (X := X) (Y := Y) n m) ∂pi := by
      apply lintegral_mono
      intro theta
      exact decisionRisk_transferredRawRule_le Kraw Kfixed P Q S u v hraw hfixed
        loss B hB hloss hbound rule hrule fallbackX fallbackY fallbackA theta
    _ = (∫⁻ theta, decisionRisk Kfixed loss rule theta ∂pi) +
        ∫⁻ theta, B * Kraw theta
          (retentionFailureSet (X := X) (Y := Y) n m) ∂pi := by
      rw [lintegral_add_left hfixedRisk]
    _ = (∫⁻ theta, decisionRisk Kfixed loss rule theta ∂pi) +
        B * ∫⁻ theta, Kraw theta
          (retentionFailureSet (X := X) (Y := Y) n m) ∂pi := by
      rw [lintegral_const_mul]
      exact Kraw.measurable_coe (measurableSet_retentionFailureSet n m)
    _ = (∫⁻ theta, decisionRisk Kfixed loss rule theta ∂pi) +
        B * priorPredictive pi Kraw
          (retentionFailureSet (X := X) (Y := Y) n m) := by
      rw [priorPredictive_apply pi Kraw (measurableSet_retentionFailureSet n m)]

/-- Given [a probability prior](hyp:pi), [an experiment kernel](hyp:K), [a nonnegative
loss](hyp:loss), and [a decision rule](hyp:rule), [Bayes decision risk is no larger than
worst-case decision risk](goal). -/
theorem bayesDecisionRisk_le_worstCase
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Theta Z) (loss : Theta → A → ℝ≥0∞) (rule : Z → A) :
    bayesDecisionRisk pi K loss rule ≤ worstCaseDecisionRisk K loss rule := by
  unfold bayesDecisionRisk worstCaseDecisionRisk
  apply lintegral_le_const
  filter_upwards with theta
  exact le_iSup (fun theta => decisionRisk K loss rule theta) theta

/-- Given [a parameter prior](hyp:pi), [a raw experiment](hyp:Kraw), [a fixed-pool
experiment](hyp:Kfixed), [the first mark kernel](hyp:P), [the second mark kernel](hyp:Q), [a
shared scale](hyp:S), [two intensity multipliers](hyp:u,v), [the raw experiment law](hyp:hraw),
[the fixed experiment law](hyp:hfixed), [a loss](hyp:loss), [a finite loss bound](hyp:B,hB,hbound),
[a failure-probability budget](hyp:eps,hfail), [joint measurability of the loss](hyp:hloss), [a
measurable fixed rule](hyp:rule,hrule), [a fallback first array](hyp:fallbackX), [a fallback
second array](hyp:fallbackY), and [a fallback action](hyp:fallbackA), [the transferred raw Bayes
risk is at most fixed worst-case risk plus bounded failure cost](goal). -/
theorem bayesDecisionRisk_transferredRawRule_le_worstCase_add
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (Kraw : Kernel Theta (RawTwoPool X Y))
    (Kfixed : Kernel Theta (FixedPools (X := X) (Y := Y) n m))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (u v : ℝ≥0)
    (hraw : IsRandomScaleTwoPoolExperiment Kraw P Q S u v)
    (hfixed : IsFixedTwoPoolExperiment n m Kfixed P Q)
    (loss : Theta → A → ℝ≥0∞) (B eps : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hloss : Measurable (Function.uncurry loss))
    (hbound : ∀ theta a, loss theta a ≤ B)
    (hfail : priorPredictive pi Kraw
      (retentionFailureSet (X := X) (Y := Y) n m) ≤ eps)
    (rule : FixedPools (X := X) (Y := Y) n m → A) (hrule : Measurable rule)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) (fallbackA : A) :
    bayesDecisionRisk pi Kraw loss
        (transferredRawRule n m rule fallbackX fallbackY fallbackA) ≤
      worstCaseDecisionRisk Kfixed loss rule + B * eps := by
  /-
  Chain `bayesDecisionRisk_transferredRawRule_le`,
  `bayesDecisionRisk_le_worstCase`, and multiplication monotonicity applied to `hfail`.
  -/
  exact (bayesDecisionRisk_transferredRawRule_le pi Kraw Kfixed P Q S u v
    hraw hfixed loss B hB hloss hbound rule hrule fallbackX fallbackY fallbackA).trans
      (add_le_add
        (bayesDecisionRisk_le_worstCase pi Kfixed loss rule)
        (mul_le_mul (le_refl B) hfail (by positivity) (by positivity)))

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

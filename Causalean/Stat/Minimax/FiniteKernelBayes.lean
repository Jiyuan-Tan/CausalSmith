/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteDesign.FiniteDesignMeasure
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Finite-state Bayes risks through probability kernels

This module supplies a real-valued Bayes-to-minimax bridge for a finite state space. A possibly
continuous prior is mixed through a Markov kernel, and the resulting average loss is bounded by
the finite worst-case loss. It also gives deterministic-map and `FiniteDesign` specializations,
including the finite-sum and measure-integral representations of the mixed risk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat

variable {Θ S A : Type*} [MeasurableSpace Θ]
variable [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- [A real-valued function on a finite state space has a bounded range](goal). -/
theorem finite_range_bddAbove (f : S → ℝ) : BddAbove (Set.range f) := by
  exact Finite.bddAbove_range f

/-- [A real-valued function on a finite state space has a range bounded below](goal). -/
theorem finite_range_bddBelow (f : S → ℝ) : BddBelow (Set.range f) := by
  exact Finite.bddBelow_range f

/-- [A real-valued statistic on a finite state space is integrable under every finite measure](goal). -/
theorem finite_integrable (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) :
    Integrable f μ := by
  refine Integrable.of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ s, ‖f s‖) (ae_of_all μ fun s ↦ ?_)
  exact Finset.single_le_sum (fun t _ ↦ norm_nonneg (f t)) (Finset.mem_univ s)

/-- [The loss from one action is integrable under every probability distribution emitted by a
Markov kernel into a finite state space](goal). -/
theorem loss_integrable_kernel (K : Kernel Θ S) [IsMarkovKernel K]
    (loss : A → S → ℝ) (a : A) (θ : Θ) : Integrable (loss a) (K θ) := by
  exact finite_integrable (K θ) (loss a)

/-- Given [a measurable parameter space](hyp:Θ), [a finite measurable state space](hyp:S), [an action space](hyp:A), [a probability kernel from parameters to states](hyp:K), [a real-valued loss for each action and state](hyp:loss), [an action](hyp:a), and [a parameter value](hyp:θ), [the kernel-average loss](goal) is the expected loss of that action under the state distribution selected by the kernel at that parameter value.

`kernelAverageLoss` is the expected loss of an action under the state distribution selected
by a kernel at a parameter value. -/
noncomputable def kernelAverageLoss (K : Kernel Θ S) (loss : A → S → ℝ)
    (a : A) (θ : Θ) : ℝ :=
  ∫ s, loss a s ∂K θ

/-- [The kernel-averaged loss of a finite-state action is measurable as a function of the
parameter](goal). -/
theorem stronglyMeasurable_kernelAverageLoss (K : Kernel Θ S) (loss : A → S → ℝ) (a : A) :
    StronglyMeasurable (kernelAverageLoss K loss a) := by
  exact (measurable_of_finite (loss a)).stronglyMeasurable.integral_kernel

/-- [Under a probability prior, the kernel-averaged loss of a finite-state action is integrable](goal). -/
theorem integrable_kernelAverageLoss (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ) (a : A) :
    Integrable (kernelAverageLoss K loss a) π := by
  refine Integrable.of_bound (stronglyMeasurable_kernelAverageLoss K loss a).aestronglyMeasurable
    (∑ s, ‖loss a s‖) (ae_of_all π fun θ ↦ ?_)
  calc
    ‖kernelAverageLoss K loss a θ‖
        ≤ (∑ s, ‖loss a s‖) * (K θ).real Set.univ := by
          apply norm_integral_le_of_norm_le_const
          exact ae_of_all (K θ) fun s ↦
            Finset.single_le_sum (fun t _ ↦ norm_nonneg (loss a t)) (Finset.mem_univ s)
    _ = ∑ s, ‖loss a s‖ := by simp

/-- [Kernel averaging on a finite state space equals the sum of statewise losses weighted by the
kernel's singleton probabilities](goal). -/
theorem kernelAverageLoss_eq_sum (K : Kernel Θ S) [IsMarkovKernel K]
    (loss : A → S → ℝ) (a : A) (θ : Θ) :
    kernelAverageLoss K loss a θ = ∑ s, (K θ).real {s} * loss a s := by
  simpa [kernelAverageLoss] using integral_fintype (loss_integrable_kernel K loss a θ)

/-- [A finite-state Markov kernel's probability of a fixed state is measurable in its source
parameter](goal). -/
theorem measurable_kernel_singletonReal (K : Kernel Θ S) [IsMarkovKernel K] (s : S) :
    Measurable (fun θ ↦ (K θ).real {s}) := by
  exact (K.measurable_coe (MeasurableSet.singleton s)).ennreal_toReal

/-- [A finite-state Markov kernel's probability of a fixed state is integrable under every
probability prior](goal). -/
theorem integrable_kernel_singletonReal (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (s : S) :
    Integrable (fun θ ↦ (K θ).real {s}) π := by
  refine Integrable.of_bound (measurable_kernel_singletonReal K s).aestronglyMeasurable 1
    (ae_of_all π fun θ ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, Measure.real_def]
  have htop : ((K θ) Set.univ) ≠ ⊤ := by simp
  simpa using ENNReal.toReal_mono htop (measure_mono (Set.subset_univ {s}))

/-- Given [a measurable parameter space](hyp:Θ), [a finite measurable state space](hyp:S), [an action space](hyp:A), [a prior measure on the parameter space](hyp:π), [a probability kernel from parameters to states](hyp:K), [a real-valued loss for each action and state](hyp:loss), and [an action](hyp:a), [the mixed kernel loss](goal) is that action's kernel-average loss integrated with respect to the prior.

`mixedKernelLoss` is the prior average of an action's kernel-averaged state loss. -/
noncomputable def mixedKernelLoss (π : Measure Θ) (K : Kernel Θ S)
    (loss : A → S → ℝ) (a : A) : ℝ :=
  ∫ θ, kernelAverageLoss K loss a θ ∂π

/-- [A continuous-prior mixture through a finite-state kernel equals the sum of statewise losses
weighted by the prior-averaged singleton probabilities](goal). -/
theorem mixedKernelLoss_eq_sum_integral (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ) (a : A) :
    mixedKernelLoss π K loss a
      = ∑ s, (∫ θ, (K θ).real {s} ∂π) * loss a s := by
  simp_rw [mixedKernelLoss, kernelAverageLoss_eq_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_mul_const]
  · intro s _
    exact (integrable_kernel_singletonReal π K s).mul_const (loss a s)

/-- If [statewise loss is nonnegative](hyp:hloss), then [its prior-and-kernel mixture is
nonnegative](goal). -/
theorem mixedKernelLoss_nonneg (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) (a : A) :
    0 ≤ mixedKernelLoss π K loss a := by
  exact integral_nonneg fun θ ↦ integral_nonneg (hloss a)

/-- [The continuous-prior average of each action's finite-state kernel loss is no greater than
that action's finite worst-case risk](goal). -/
theorem mixedKernelLoss_le_worstCaseRiskReal (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (a : A) :
    (∫ θ, ∫ s, loss a s ∂K θ ∂π) ≤ worstCaseRiskReal loss a := by
  calc
    (∫ θ, ∫ s, loss a s ∂K θ ∂π)
        ≤ ∫ _θ, worstCaseRiskReal loss a ∂π := by
          apply integral_mono (integrable_kernelAverageLoss π K loss a)
            (integrable_const (worstCaseRiskReal loss a))
          intro θ
          change kernelAverageLoss K loss a θ ≤ worstCaseRiskReal loss a
          unfold kernelAverageLoss
          calc
            (∫ s, loss a s ∂K θ)
                ≤ ∫ _s, worstCaseRiskReal loss a ∂K θ := by
                  apply integral_mono (loss_integrable_kernel K loss a θ)
                    (integrable_const (worstCaseRiskReal loss a))
                  intro s
                  exact le_worstCaseRisk (finite_range_bddAbove (loss a)) s
            _ = worstCaseRiskReal loss a := by simp
    _ = worstCaseRiskReal loss a := by simp

/-- If [loss is nonnegative](hyp:hloss), the [nonnegative extension of an action's mixed
kernel loss is at most its standard extended worst-case risk](goal). -/
theorem mixedKernelLoss_le_worstCaseRiskENNReal (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) (a : A) :
    ENNReal.ofReal (mixedKernelLoss π K loss a) ≤ worstCaseRiskOfReal loss a := by
  rw [ENNReal.ofReal_le_iff_le_toReal
    (worstCaseRiskOfReal_ne_top_of_bddAbove (finite_range_bddAbove (loss a))),
    worstCaseRiskENNReal_ofReal_toReal (hloss a)
      (worstCaseRiskOfReal_ne_top_of_bddAbove (finite_range_bddAbove (loss a)))]
  exact mixedKernelLoss_le_worstCaseRiskReal π K loss a

/-- Given [a measurable parameter space](hyp:Θ), [a finite measurable state space](hyp:S), [an action space](hyp:A), [a prior measure on the parameter space](hyp:π), [a probability kernel from parameters to states](hyp:K), and [a real-valued loss for each action and state](hyp:loss), [the real Bayes risk](goal) is the infimum, over all actions, of their mixed kernel losses.

`realBayesRisk` is the smallest prior-and-kernel average loss achievable by an action in a
finite-state decision problem. -/
noncomputable def realBayesRisk (π : Measure Θ) (K : Kernel Θ S)
    (loss : A → S → ℝ) : ℝ :=
  ⨅ a, mixedKernelLoss π K loss a

/-- If [statewise loss is nonnegative](hyp:hloss), then [the real Bayes risk is
nonnegative](goal). -/
theorem realBayesRisk_nonneg (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) :
    0 ≤ realBayesRisk π K loss := by
  exact Real.iInf_nonneg fun a ↦ mixedKernelLoss_nonneg π K loss hloss a

/-- With at least one available action and [nonnegative statewise loss](hyp:hloss),
[the real Bayes risk under a continuous prior and finite-state Markov kernel is at most the
finite-state minimax value](goal). -/
theorem realBayesRisk_le_minimaxValueReal [Nonempty A]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) :
    realBayesRisk π K loss ≤ minimaxValueReal loss := by
  apply le_minimaxValue
  intro a
  refine (ciInf_le ?_ a).trans (mixedKernelLoss_le_worstCaseRiskReal π K loss a)
  refine ⟨0, ?_⟩
  rintro _ ⟨a', rfl⟩
  exact mixedKernelLoss_nonneg π K loss hloss a'

/-- With [at least one action](hyp:A) and [nonnegative loss](hyp:hloss), the
[nonnegative extension of the Bayes risk is at most the standard minimax value](goal). -/
theorem realBayesRisk_le_minimaxValueENNReal [Nonempty A]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) :
    ENNReal.ofReal (realBayesRisk π K loss) ≤ minimaxValueENNRealOfReal loss := by
  apply le_minimaxValueENNReal
  intro a
  refine (ENNReal.ofReal_le_ofReal ?_).trans
    (mixedKernelLoss_le_worstCaseRiskENNReal π K loss hloss a)
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨a', rfl⟩
  exact mixedKernelLoss_nonneg π K loss hloss a'

/-- A finite-state loss composed with [a measurable deterministic state map](hyp:hf) is
[integrable under every probability prior](goal). -/
theorem integrable_loss_comp (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ) (a : A) :
    Integrable (fun θ ↦ loss a (f θ)) π := by
  refine Integrable.of_bound
    ((measurable_of_finite (loss a)).comp hf).aestronglyMeasurable
    (∑ s, ‖loss a s‖) (ae_of_all π fun θ ↦ ?_)
  exact Finset.single_le_sum (fun s _ ↦ norm_nonneg (loss a s)) (Finset.mem_univ (f θ))

/-- A [measurable deterministic state map](hyp:hf) has the same mixed kernel loss as the
[ordinary prior integral of its composed loss](goal). -/
theorem mixedKernelLoss_deterministic (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ) (a : A) :
    mixedKernelLoss π (Kernel.deterministic f hf) loss a
      = ∫ θ, loss a (f θ) ∂π := by
  unfold mixedKernelLoss kernelAverageLoss
  apply integral_congr_ae
  refine ae_of_all π fun θ ↦ ?_
  change (∫ s, loss a s ∂(Kernel.deterministic f hf) θ) = loss a (f θ)
  rw [Kernel.deterministic_apply, integral_dirac]

/-- If [the state map is measurable](hyp:hf), then [the prior average of the composed loss is no
greater than its finite worst-case risk](goal). -/
theorem integral_loss_comp_le_worstCaseRiskReal (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ)
    (a : A) :
    (∫ θ, loss a (f θ) ∂π) ≤ worstCaseRiskReal loss a := by
  rw [← mixedKernelLoss_deterministic π f hf loss a]
  exact mixedKernelLoss_le_worstCaseRiskReal π (Kernel.deterministic f hf) loss a

/-- If [the state map is measurable](hyp:hf) and [loss is nonnegative](hyp:hloss), the
[extended prior-average loss is at most the standard extended worst-case risk](goal). -/
theorem integral_loss_comp_le_worstCaseRiskENNReal
    (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) (a : A) :
    ENNReal.ofReal (∫ θ, loss a (f θ) ∂π) ≤ worstCaseRiskOfReal loss a := by
  rw [← mixedKernelLoss_deterministic π f hf loss a]
  exact mixedKernelLoss_le_worstCaseRiskENNReal π (Kernel.deterministic f hf) loss hloss a

/-- Given [a measurable parameter space](hyp:Θ), [a finite measurable state space](hyp:S), [an action space](hyp:A), [a prior measure on the parameter space](hyp:π), [a map assigning each parameter a state](hyp:f), and [a real-valued loss for each action and state](hyp:loss), [the deterministic Bayes risk](goal) is the infimum, over all actions, of the prior-integrated loss evaluated at the state assigned to each parameter.

`deterministicBayesRisk` is the smallest prior-integrated loss achieved after a measurable
parameter is deterministically assigned to a finite state. -/
noncomputable def deterministicBayesRisk (π : Measure Θ) (f : Θ → S)
    (loss : A → S → ℝ) : ℝ :=
  ⨅ a, ∫ θ, loss a (f θ) ∂π

/-- A [measurable deterministic state map](hyp:hf) gives the same Bayes risk whether viewed
[directly or as its deterministic Markov kernel](goal). -/
theorem deterministicBayesRisk_eq_realBayesRisk (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ) :
    deterministicBayesRisk π f loss
      = realBayesRisk π (Kernel.deterministic f hf) loss := by
  simp [deterministicBayesRisk, realBayesRisk, mixedKernelLoss_deterministic]

/-- With at least one available action,
[a measurable deterministic state map](hyp:hf), and [nonnegative statewise loss](hyp:hloss), [the deterministic Bayes risk is at most
the finite-state minimax value](goal). -/
theorem deterministicBayesRisk_le_minimaxValueReal [Nonempty A]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) :
    deterministicBayesRisk π f loss ≤ minimaxValueReal loss := by
  rw [deterministicBayesRisk_eq_realBayesRisk π f hf loss]
  exact realBayesRisk_le_minimaxValueReal π (Kernel.deterministic f hf) loss hloss

/-- With [at least one action](hyp:A), a [measurable state map](hyp:hf), and
[nonnegative loss](hyp:hloss), the [extended deterministic Bayes risk is at most the
standard minimax value](goal). -/
theorem deterministicBayesRisk_le_minimaxValueENNReal [Nonempty A]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → S) (hf : Measurable f) (loss : A → S → ℝ)
    (hloss : ∀ a s, 0 ≤ loss a s) :
    ENNReal.ofReal (deterministicBayesRisk π f loss) ≤ minimaxValueENNRealOfReal loss := by
  rw [deterministicBayesRisk_eq_realBayesRisk π f hf loss]
  exact realBayesRisk_le_minimaxValueENNReal π (Kernel.deterministic f hf) loss hloss

/-- [A real-valued statistic on a finite design space is integrable under the design's induced
probability measure](goal). -/
theorem finiteDesign_integrable
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S) (g : S → ℝ) :
    Integrable g D.toMeasure := by
  exact finite_integrable D.toMeasure g

/-- [A finite design's expected action loss equals both its finite weighted sum and its induced
probability-measure integral](goal). -/
theorem finiteDesign_expectedLoss_eq_sum_eq_integral
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (a : A) :
    D.E (loss a) = ∑ s, D.p s * loss a s ∧
      D.E (loss a) = ∫ s, loss a s ∂D.toMeasure := by
  exact ⟨rfl, (D.integral_toMeasure (loss a)).symm⟩

/-- [A finite design's expected loss for each action is no greater than that action's finite
worst-case risk](goal). -/
theorem finiteDesign_expectedLoss_le_worstCaseRiskReal
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (a : A) :
    D.E (loss a) ≤ worstCaseRiskReal loss a := by
  rw [← D.integral_toMeasure]
  calc
    (∫ s, loss a s ∂D.toMeasure)
        ≤ ∫ _s, worstCaseRiskReal loss a ∂D.toMeasure := by
          apply integral_mono (finiteDesign_integrable D (loss a))
            (integrable_const (worstCaseRiskReal loss a))
          intro s
          exact le_worstCaseRisk (finite_range_bddAbove (loss a)) s
    _ = worstCaseRiskReal loss a := by simp

/-- If [loss is nonnegative](hyp:hloss), a [finite design's extended expected loss is at
most the action's standard extended worst-case risk](goal). -/
theorem finiteDesign_expectedLoss_le_worstCaseRiskENNReal
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (hloss : ∀ a s, 0 ≤ loss a s) (a : A) :
    ENNReal.ofReal (D.E (loss a)) ≤ worstCaseRiskOfReal loss a := by
  rw [ENNReal.ofReal_le_iff_le_toReal
    (worstCaseRiskOfReal_ne_top_of_bddAbove (finite_range_bddAbove (loss a))),
    worstCaseRiskENNReal_ofReal_toReal (hloss a)
      (worstCaseRiskOfReal_ne_top_of_bddAbove (finite_range_bddAbove (loss a)))]
  exact finiteDesign_expectedLoss_le_worstCaseRiskReal D loss a

/-- If [the loss is nonnegative for every action and state](hyp:hloss), then [the expected loss
of any fixed action under a finite design is at most that action's worst-case risk](goal).

Deprecated real-valued form of `finiteDesign_expectedLoss_le_worstCaseRiskENNReal`. -/
@[deprecated finiteDesign_expectedLoss_le_worstCaseRiskReal (since := "2026-09-17")]
theorem finiteDesign_expectedLoss_le_worstCaseRisk
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (hloss : ∀ a s, 0 ≤ loss a s) (a : A) :
    D.E (loss a) ≤ worstCaseRiskReal loss a := by
  simpa [worstCaseRiskReal] using
    finiteDesign_expectedLoss_le_worstCaseRiskReal D loss a

/-- Given [a finite state space](hyp:S), [an action space](hyp:A), [a finite randomization design on the state space](hyp:D), and [a real-valued loss for each action and state](hyp:loss), [the finite-design Bayes risk](goal) is the infimum, over all actions, of their expected losses under that design.

`finiteDesignBayesRisk` is the smallest expected loss attainable under a fixed finite
randomization design. -/
noncomputable def finiteDesignBayesRisk
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) : ℝ :=
  ⨅ a, D.E (loss a)

/-- With at least one available action and [nonnegative statewise loss](hyp:hloss),
[a finite design's Bayes risk is at most the finite-state minimax value](goal). -/
theorem finiteDesignBayesRisk_le_minimaxValueReal [Nonempty A]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (hloss : ∀ a s, 0 ≤ loss a s) :
    finiteDesignBayesRisk D loss ≤ minimaxValueReal loss := by
  apply le_minimaxValue
  intro a
  refine (ciInf_le ?_ a).trans
    (finiteDesign_expectedLoss_le_worstCaseRiskReal D loss a)
  refine ⟨0, ?_⟩
  rintro _ ⟨a', rfl⟩
  exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (D.p_nonneg s) (hloss a' s)

/-- With [at least one action](hyp:A) and [nonnegative loss](hyp:hloss), the [extended
finite-design Bayes risk is at most the standard minimax value](goal). -/
theorem finiteDesignBayesRisk_le_minimaxValueENNReal [Nonempty A]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign S)
    (loss : A → S → ℝ) (hloss : ∀ a s, 0 ≤ loss a s) :
    ENNReal.ofReal (finiteDesignBayesRisk D loss) ≤ minimaxValueENNRealOfReal loss := by
  apply le_minimaxValueENNReal
  intro a
  refine (ENNReal.ofReal_le_ofReal ?_).trans
    (finiteDesign_expectedLoss_le_worstCaseRiskENNReal D loss hloss a)
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨a', rfl⟩
  exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (D.p_nonneg s) (hloss a' s)

/-- Given [a measurable parameter space](hyp:Θ), [a nonempty finite measurable state space with measurable singletons](hyp:S), [a probability prior on the parameter space](hyp:π), and [a Markov kernel from parameters to states](hyp:K), [the induced finite design](goal) is the design whose [probability assigned to each state is the prior average of the kernel's probability of that state](step:1), these probabilities are nonnegative, and their sum over all states is one.

`inducedFiniteDesign` assigns each finite state the average, under the prior, of the Markov
kernel's probability of that state. -/
noncomputable def inducedFiniteDesign (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] :
    Causalean.Experimentation.DesignBased.FiniteDesign S where
  p s := ∫ θ, (K θ).real {s} ∂π
  p_nonneg := by
    intro s
    exact integral_nonneg fun θ ↦ measureReal_nonneg
  p_sum := by
    rw [← integral_finsetSum]
    · simp_rw [sum_measureReal_singleton]
      simp
    · intro s _
      exact integrable_kernel_singletonReal π K s

/-- [The induced finite design's mass at each state is the prior integral of the kernel's
singleton probability](goal). -/
theorem inducedFiniteDesign_p (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (s : S) :
    (inducedFiniteDesign π K).p s = ∫ θ, (K θ).real {s} ∂π :=
  rfl

/-- [Expected loss under the induced finite design equals the continuous-prior, kernel-averaged
loss integral](goal). -/
theorem inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ) (a : A) :
    (inducedFiniteDesign π K).E (loss a) = mixedKernelLoss π K loss a := by
  exact (mixedKernelLoss_eq_sum_integral π K loss a).symm

/-- [A continuous prior mixed through a finite-state Markov kernel has the same real Bayes risk
as its induced finite design](goal). -/
theorem realBayesRisk_eq_inducedFiniteDesignBayesRisk
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (loss : A → S → ℝ) :
    realBayesRisk π K loss = finiteDesignBayesRisk (inducedFiniteDesign π K) loss := by
  unfold realBayesRisk finiteDesignBayesRisk
  congr 1
  funext a
  exact (inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss π K loss a).symm

end Causalean.Stat

import Causalean.Stat.FiniteRaoBlackwell.RaoBlackwell
import Causalean.Stat.FiniteRaoBlackwell.Posterior
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Stat.Minimax.FiniteKernelBayes
import Mathlib.Probability.Kernel.Basic

/-!
# Markov-kernel and finite-Bayes bridges

This module realizes the algebraic finite designs from `Core` as genuine Markov kernels on
finite labeled measurable spaces.  It exposes the full-data law, statistic law, and guarded
conditional laws in the kernel API, including the factorization-derived common conditional law
and a finite-prior posterior law of the latent state given the statistic.  Singleton
probabilities are identified with real finite masses, so the kernels can be passed directly to
`Causalean.Stat.Minimax.FiniteKernelBayes` without an `ENNReal` loss conversion.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

open Causalean.Experimentation.DesignBased

variable {Latent Allocation Observation Statistic : Type*}
variable [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic]
variable [DecidableEq Allocation] [DecidableEq Observation] [DecidableEq Statistic]
variable [MeasurableSpace Latent] [MeasurableSingletonClass Latent]
variable [MeasurableSpace Allocation] [MeasurableSingletonClass Allocation]
variable [MeasurableSpace Observation] [MeasurableSingletonClass Observation]
variable [MeasurableSpace Statistic] [MeasurableSingletonClass Statistic]

namespace FiniteUniformExperiment

variable (E : FiniteUniformExperiment Latent Allocation Observation Statistic)

/-- Given [a finite uniform experiment on finite latent, allocation, observation, and statistic spaces](hyp:E), with σ-algebras on the latent, allocation, and observation spaces and measurable singleton latent states, the [full-data Markov kernel](goal) assigns to each latent state the experiment's finite joint probability law of the allocation and observation at that state.

The full-data Markov kernel sends each latent state to the finite joint allocation-observation
law at that state. -/
noncomputable def fullKernel : Kernel Latent (Allocation × Observation) :=
  Kernel.ofFunOfCountable fun θ ↦
    ({
      p := E.jointMass θ
      p_nonneg := E.jointMass_nonneg θ
      p_sum := E.jointMass_sum θ
    } : FiniteDesign (Allocation × Observation)).toMeasure

/-- For [a finite uniform experiment on finite latent, allocation, observation, and statistic
spaces, with distinguishable allocation, observation, and statistic values, σ-algebras on the
latent, allocation, and observation spaces, and measurable singleton latent states](hyp:E), the
[full-data kernel is a Markov kernel](goal): [at every latent state, its output law is a probability
measure](step:1). -/
instance fullKernel_isMarkovKernel : IsMarkovKernel E.fullKernel where
  isProbabilityMeasure θ := by
    change IsProbabilityMeasure
      (({
        p := E.jointMass θ
        p_nonneg := E.jointMass_nonneg θ
        p_sum := E.jointMass_sum θ
      } : FiniteDesign (Allocation × Observation)).toMeasure)
    infer_instance

/-- Given [a finite uniform experiment on finite latent, allocation, observation, and statistic spaces](hyp:E), with σ-algebras on the latent and statistic spaces and measurable singleton latent states, the [statistic Markov kernel](goal) assigns to each latent state the experiment's finite marginal probability law of the statistic.

The statistic Markov kernel sends each latent state to the finite statistic marginal law. -/
noncomputable def statisticKernel : Kernel Latent Statistic :=
  Kernel.ofFunOfCountable fun θ ↦ (E.statisticDesign θ).toMeasure

/-- For [a finite uniform experiment on finite latent, allocation, observation, and statistic
spaces, with distinguishable allocation, observation, and statistic values, σ-algebras on the
latent and statistic spaces, and measurable singleton latent states](hyp:E), the [statistic
kernel is a Markov kernel](goal): [at every latent state, its output law is a probability measure](step:1). -/
instance statisticKernel_isMarkovKernel : IsMarkovKernel E.statisticKernel where
  isProbabilityMeasure θ := by
    change IsProbabilityMeasure (E.statisticDesign θ).toMeasure
    infer_instance

/-- Given [a finite uniform experiment on finite latent, allocation, observation, and statistic spaces](hyp:E), with σ-algebras on the allocation, observation, and statistic spaces and measurable singleton statistic values, and [a latent state](hyp:θ), the [guarded conditional Markov kernel](goal) assigns to each statistic value the experiment's conditional probability law of the allocation--observation pair at that state, using the fallback law when the statistic fiber has zero probability.

At a fixed latent state, the guarded conditional Markov kernel sends each statistic value to
the corresponding full-data conditional law, using the fallback law on null fibers. -/
noncomputable def conditionalKernel (θ : Latent) :
    Kernel Statistic (Allocation × Observation) :=
  Kernel.ofFunOfCountable fun s ↦ (E.conditionalDesign θ s).toMeasure

/-- For [a finite uniform experiment on finite latent, allocation, observation, and statistic
spaces, with distinguishable allocation, observation, and statistic values, σ-algebras on the
allocation, observation, and statistic spaces, and measurable singleton statistic values](hyp:E)
and [a latent state](hyp:θ), the [guarded conditional kernel is a Markov kernel](goal): [at every
statistic value, including a zero-probability fibre, its output law is a probability measure](step:1). -/
instance conditionalKernel_isMarkovKernel (θ : Latent) :
    IsMarkovKernel (E.conditionalKernel θ) where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure (E.conditionalDesign θ s).toMeasure
    infer_instance

/-- Given [a finite uniform experiment on finite latent, allocation, observation, and statistic spaces](hyp:E), with σ-algebras on the allocation, observation, and statistic spaces and measurable singleton statistic values, and [a sufficient factorization of its full-data masses](hyp:F), the [common conditional Markov kernel](goal) assigns to each statistic value the factorization-induced state-independent conditional probability law of the allocation--observation pair.

A sufficient factorization gives a state-independent Markov kernel from the statistic to
the full data by converting its derived common finite conditional law to measures. -/
noncomputable def commonConditionalMarkovKernel (F : E.SufficientFactorization) :
    Kernel Statistic (Allocation × Observation) :=
  Kernel.ofFunOfCountable fun s ↦
    ({
      p := F.toCommonConditionalKernel.weight s
      p_nonneg := F.toCommonConditionalKernel.weight_nonneg s
      p_sum := F.toCommonConditionalKernel.weight_sum s
    } : FiniteDesign (Allocation × Observation)).toMeasure

/-- For [a finite uniform experiment on finite latent, allocation, observation, and statistic
spaces, with distinguishable allocation, observation, and statistic values, σ-algebras on the
allocation, observation, and statistic spaces, and measurable singleton statistic values](hyp:E)
and [a sufficient factorization of its full-data probability masses](hyp:F), the
[factorization-derived common conditional kernel is a Markov kernel](goal): [at every statistic
value, including a zero-probability fibre, its output law is a probability measure](step:1). -/
instance commonConditionalMarkovKernel_isMarkovKernel (F : E.SufficientFactorization) :
    IsMarkovKernel (E.commonConditionalMarkovKernel F) where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure
      (({
        p := F.toCommonConditionalKernel.weight s
        p_nonneg := F.toCommonConditionalKernel.weight_nonneg s
        p_sum := F.toCommonConditionalKernel.weight_sum s
      } : FiniteDesign (Allocation × Observation)).toMeasure)
    infer_instance

/-- Given [a finite uniform experiment on finite latent, allocation, observation, and statistic spaces](hyp:E), with σ-algebras on the latent and statistic spaces and measurable singleton statistic values, and [a finite prior probability distribution on latent states](hyp:prior), the [posterior Markov kernel](goal) assigns to each statistic value the guarded posterior probability law of the latent state, using the designated fallback law on prior-predictive statistic fibers of zero probability.

Under a finite prior, the posterior Markov kernel sends each statistic value to the guarded
conditional law of the latent state. -/
noncomputable def posteriorKernel (prior : FiniteDesign Latent) : Kernel Statistic Latent :=
  Kernel.ofFunOfCountable fun s ↦ (E.posteriorDesign prior s).toMeasure

/-- For [a finite uniform experiment on finite latent, allocation, observation, and statistic
spaces, with distinguishable allocation, observation, and statistic values, σ-algebras on the
latent and statistic spaces, and measurable singleton statistic values](hyp:E) and [a finite
prior probability distribution on latent states](hyp:prior), the [guarded posterior kernel is a
Markov kernel](goal): [at every statistic value, including a prior-predictive zero-probability
fibre, its output law is a probability measure](step:1). -/
instance posteriorKernel_isMarkovKernel (prior : FiniteDesign Latent) :
    IsMarkovKernel (E.posteriorKernel prior) where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure (E.posteriorDesign prior s).toMeasure
    infer_instance

/-- The real singleton probability of the full-data kernel equals the finite joint mass. -/
theorem fullKernel_singletonReal (θ : Latent) (z : Allocation × Observation) :
    (E.fullKernel θ).real {z} = E.jointMass θ z := by
  change
    (({
      p := E.jointMass θ
      p_nonneg := E.jointMass_nonneg θ
      p_sum := E.jointMass_sum θ
    } : FiniteDesign (Allocation × Observation)).toMeasure).real {z} = E.jointMass θ z
  rw [show ({z} : Set (Allocation × Observation)) = {x | x = z} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  change (∑ x, E.jointMass θ x * if x = z then 1 else 0) = E.jointMass θ z
  simp

/-- The real singleton probability of the statistic kernel equals the finite statistic mass. -/
theorem statisticKernel_singletonReal (θ : Latent) (s : Statistic) :
    (E.statisticKernel θ).real {s} = E.statisticMass θ s := by
  change (E.statisticDesign θ).toMeasure.real {s} = E.statisticMass θ s
  rw [show ({s} : Set Statistic) = {x | x = s} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  change (∑ x, E.statisticMass θ x * if x = s then 1 else 0) = E.statisticMass θ s
  simp

/-- The real singleton probability of the guarded conditional kernel equals its finite
conditional weight. -/
theorem conditionalKernel_singletonReal (θ : Latent) (s : Statistic)
    (z : Allocation × Observation) :
    (E.conditionalKernel θ s).real {z} = E.conditionalWeight θ s z := by
  change (E.conditionalDesign θ s).toMeasure.real {z} = E.conditionalWeight θ s z
  rw [show ({z} : Set (Allocation × Observation)) = {x | x = z} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  change (∑ x, E.conditionalWeight θ s x * if x = z then 1 else 0) =
    E.conditionalWeight θ s z
  simp

/-- The real singleton probability of the factorization-derived common conditional Markov
kernel equals its finite common conditional weight. -/
theorem commonConditionalMarkovKernel_singletonReal
    (F : E.SufficientFactorization) (s : Statistic)
    (z : Allocation × Observation) :
    (E.commonConditionalMarkovKernel F s).real {z} =
      F.toCommonConditionalKernel.weight s z := by
  change
    (({
      p := F.toCommonConditionalKernel.weight s
      p_nonneg := F.toCommonConditionalKernel.weight_nonneg s
      p_sum := F.toCommonConditionalKernel.weight_sum s
    } : FiniteDesign (Allocation × Observation)).toMeasure).real {z} =
      F.toCommonConditionalKernel.weight s z
  rw [show ({z} : Set (Allocation × Observation)) = {x | x = z} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  change (∑ x, F.toCommonConditionalKernel.weight s x * if x = z then 1 else 0) =
    F.toCommonConditionalKernel.weight s z
  simp

/-- The real singleton probability of the finite-prior posterior kernel equals the guarded
posterior weight of that latent state. -/
theorem posteriorKernel_singletonReal (prior : FiniteDesign Latent)
    (s : Statistic) (θ : Latent) :
    (E.posteriorKernel prior s).real {θ} = E.posteriorWeight prior s θ := by
  classical
  change (E.posteriorDesign prior s).toMeasure.real {θ} = E.posteriorWeight prior s θ
  rw [show ({θ} : Set Latent) = {x | x = θ} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  change (∑ x, E.posteriorWeight prior s x * if x = θ then 1 else 0) =
    E.posteriorWeight prior s θ
  simp

/-- Kernel averaging through the statistic kernel is exactly the real finite sum of statistic
losses weighted by their statistic masses, matching `FiniteKernelBayes`. -/
theorem kernelAverageLoss_statisticKernel_eq_sum {Action : Type*}
    (loss : Action → Statistic → ℝ) (a : Action) (θ : Latent) :
    Causalean.Stat.kernelAverageLoss E.statisticKernel loss a θ =
      ∑ s, E.statisticMass θ s * loss a s := by
  /- Rewrite with Causalean.Stat.kernelAverageLoss_eq_sum and the singleton bridge. -/
  letI : Nonempty Statistic := ⟨E.sampleStatistic E.fallbackSample⟩
  rw [Causalean.Stat.kernelAverageLoss_eq_sum]
  simp_rw [E.statisticKernel_singletonReal]

/-- Kernel averaging a real latent-state loss through the finite-prior posterior kernel is
exactly the finite posterior-weighted sum, matching the real `FiniteKernelBayes` interface. -/
theorem kernelAverageLoss_posteriorKernel_eq_sum {Action : Type*}
    (prior : FiniteDesign Latent) (loss : Action → Latent → ℝ)
    (a : Action) (s : Statistic) :
    Causalean.Stat.kernelAverageLoss (E.posteriorKernel prior) loss a s =
      ∑ θ, E.posteriorWeight prior s θ * loss a θ := by
  change (∫ θ, loss a θ ∂(E.posteriorDesign prior s).toMeasure) =
    ∑ θ, E.posteriorWeight prior s θ * loss a θ
  rw [FiniteDesign.integral_toMeasure]
  rfl

/-- The measure-theoretic conditional-kernel mean of a full-data estimator [equals the finite
conditional mean](goal), so no `ENNReal` conversion appears in Rao--Blackwell calculations. -/
theorem kernelMean_conditionalKernel_eq_conditionalMean
    (est : Allocation × Observation → ℝ) (θ : Latent) (s : Statistic) :
    (∫ z, est z ∂(E.conditionalKernel θ) s) = E.conditionalMean est θ s := by
  /- Evaluate the finite-design integral and unfold the two finite expectations. -/
  change (∫ z, est z ∂(E.conditionalDesign θ s).toMeasure) = E.conditionalMean est θ s
  rw [FiniteDesign.integral_toMeasure]
  rfl

end FiniteUniformExperiment

end Causalean.Stat.FiniteRaoBlackwell

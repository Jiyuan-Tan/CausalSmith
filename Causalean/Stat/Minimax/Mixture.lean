/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite mixtures of measures

A finite mixture `mixture w P = ∑ i, w i • P i` of measures `P : ι → Measure Ω`
(over any finite index `ι`) with `ℝ≥0∞`-weights `w`.  When the weights sum to `1`
and each part is a probability measure, the mixture is a probability measure
(`mixture_isProbabilityMeasure`).  The key reusable fact for minimax lower bounds
is the **domination** lemma `mixtureReal_le`: a uniform `.real`-mass bound `B` on
every part transfers to the mixture.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Mathlib.Probability.Kernel.Composition.Comp


/-! # Finite Mixtures of Measures

This file defines finite mixtures of measures with nonnegative extended-real
weights. It proves evaluation, probability-measure, and domination facts used to
transfer componentwise bounds to mixtures in minimax arguments. -/

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal BigOperators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- Given a [sample space equipped with a σ-algebra](hyp:Ω,mΩ), a [finite index set](hyp:ι),
[nonnegative extended-real weights indexed by that set](hyp:w), and [a measure for each
index](hyp:P), the [finite mixture measure](goal) is the sum of the component measures, each
scaled by its corresponding weight. -/
noncomputable def mixture (w : ι → ℝ≥0∞) (P : ι → Measure Ω) : Measure Ω :=
  ∑ i, w i • P i

/-- Evaluation: the mixture's mass on a set is the weighted sum of the parts' masses. -/
theorem mixture_apply (w : ι → ℝ≥0∞) (P : ι → Measure Ω) (A : Set Ω) :
    mixture w P A = ∑ i, w i * P i A := by
  simp only [mixture, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]

/-- If the weights sum to 1 and each part is a probability measure, the mixture is one. -/
theorem mixture_isProbabilityMeasure (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] :
    IsProbabilityMeasure (mixture w P) := by
  refine ⟨?_⟩
  rw [mixture_apply]
  simp only [measure_univ, mul_one]
  exact hw

/-- **Domination.** If [the mixture weights `w` sum to `1`](hyp:w,hw), each component
measure `P i` is a probability measure, and [every component assigns `.real`-mass at most
`B` to the set `A`](hyp:hB), then [the mixture measure also assigns `.real`-mass at most
`B` to `A`](goal). -/
theorem mixtureReal_le (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (A : Set Ω) (B : ℝ) (hB : ∀ i, (P i).real A ≤ B) :
    (mixture w P).real A ≤ B := by
  have hwfin : ∀ i, w i ≠ ⊤ := by
    intro i
    have hle : w i ≤ 1 := le_of_le_of_eq (Finset.single_le_sum
      (f := w) (fun j _ => zero_le) (Finset.mem_univ i)) hw
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hterm : ∀ i, w i * P i A ≠ ⊤ := by
    intro i
    exact ENNReal.mul_ne_top (hwfin i) (measure_ne_top _ _)
  rw [Measure.real, mixture_apply, ENNReal.toReal_sum (fun i _ => hterm i)]
  have hsum : (∑ i, (w i * P i A).toReal) ≤ ∑ i, (w i).toReal * B := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [ENNReal.toReal_mul]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have : (P i).real A = (P i A).toReal := rfl
    rw [← this]
    exact hB i
  refine hsum.trans ?_
  rw [← Finset.sum_mul]
  have hwsum : (∑ i, (w i).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => hwfin i), hw, ENNReal.toReal_one]
  rw [hwsum, one_mul]

/-- **Witness extraction.**  Some component carries at least the mixture's `.real`-mass:
since the mixture is a weighted average (weights summing to `1`), its mass on `A` is at
most the maximal component mass, attained over the finite index. -/
theorem exists_real_ge_mixture [Nonempty ι] (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] (A : Set Ω) :
    ∃ i, (mixture w P).real A ≤ (P i).real A := by
  obtain ⟨i, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => (P i).real A) Finset.univ_nonempty
  exact ⟨i, mixtureReal_le w hw P A ((P i).real A) (fun j => hmax j (Finset.mem_univ j))⟩

end Causalean.Stat


/-! ## Continuous prior-predictive mixtures

This section complements finite weighted mixtures with mixtures obtained by integrating a
measurable experiment kernel against an arbitrary prior.  It records probability and integration
interfaces used by moment-matching and fuzzy-hypothesis lower bounds.
-/

namespace Causalean.Stat.Minimax.MomentMatchedMixture

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- Given [a prior measure](hyp:π) and [a measurable experiment kernel](hyp:K), the
[prior-predictive law](goal) first draws a parameter from the prior and then draws an observation
from the experiment at that parameter. -/
noncomputable def priorPredictive (π : Measure Θ) (K : Kernel Θ X) : Measure X :=
  π.bind fun θ => K θ

/-- Mixing [probability experiment laws](hyp:hK) from [a measurable kernel](hyp:K) against
[a probability prior](hyp:π) [produces a probability law on observations](goal). -/
theorem priorPredictive_isProbability (π : Measure Θ) (K : Kernel Θ X)
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ)) :
    IsProbabilityMeasure (priorPredictive π K) := by
  rw [priorPredictive]
  apply isProbabilityMeasure_iff.mpr
  rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
  simp_rw [isProbabilityMeasure_iff.mp (hK _)]
  simp

/-- The mass that [a prior](hyp:π) and [experiment kernel](hyp:K) assign to
[a measurable observation event](hyp:hA) [equals the prior average of its conditional event
probabilities](goal). -/
theorem priorPredictive_apply (π : Measure Θ) (K : Kernel Θ X) {A : Set X}
    (hA : MeasurableSet A) :
    priorPredictive π K A = ∫⁻ θ, K θ A ∂π := by
  exact Measure.bind_apply hA K.aemeasurable

/-- The lower integral of [a nonnegative measurable statistic](hyp:f,hf) under the mixture from
[a prior](hyp:π) and [experiment kernel](hyp:K) [equals the iterated prior-then-experiment lower
integral](goal). -/
theorem lintegral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂priorPredictive π K = ∫⁻ θ, ∫⁻ x, f x ∂K θ ∂π := by
  exact Measure.lintegral_bind K.aemeasurable hf.aemeasurable

/-- The expectation of [an integrable real-valued statistic](hyp:f,hf) under the mixture from
[a prior](hyp:π) and [experiment kernel](hyp:K) [equals the prior average of its conditional
expectations](goal). -/
theorem integral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ)
    (hf : Integrable f (priorPredictive π K)) :
    ∫ x, f x ∂priorPredictive π K = ∫ θ, ∫ x, f x ∂K θ ∂π := by
  exact Causalean.Mathlib.MeasureTheory.integral_bind K.measurable hf

end Causalean.Stat.Minimax.MomentMatchedMixture

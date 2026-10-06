module
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Mixture
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.Reconstruction

/-!
# Count reconstruction for random-scale transfer

Histogram reconstruction transfers random-scale Poisson count mixtures to ordered samples and contracts total variation.
-/

public section

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open scoped ENNReal NNReal

/-- For a [mixing law](hyp:π), [conditional sampling kernel](hyp:P), [random
scale](hyp:S), and [scale multiplier](hyp:u), applying histogram reconstruction
to the mixture of independent Poisson counts gives the corresponding mixture
of ordered finite Poisson samples. The result is [the reconstruction identity from count mixtures to ordered-sample mixtures](goal). -/
lemma randomScale_count_mixture_reconstruction
    {Θ X : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    (π : Measure Θ) (P : Kernel Θ X) [∀ θ, IsProbabilityMeasure (P θ)]
    (S : Θ → ℝ≥0) (u : ℝ≥0) :
    histogramReconstructionKernel X ∘ₘ
        π.bind (fun θ => independentPoissonCountLaw (P θ) (u * S θ)) =
      rawMixture π P S u := by
  change (π.bind (fun θ => independentPoissonCountLaw (P θ) (u * S θ))).bind
    (histogramReconstructionKernel X) = _
  rw [Measure.bind_bind (measurable_of_finite _).aemeasurable
    (histogramReconstructionKernel X).aemeasurable]
  simp_rw [show ∀ θ, (independentPoissonCountLaw (P θ) (u * S θ)).bind
      (histogramReconstructionKernel X) =
        finitePoissonSampleLaw (P θ) (u * S θ) from
    fun θ => independentPoissonCountLaw_comp_reconstruction (P θ) (u * S θ)]
  rfl


/-- For a [probability mixing law](hyp:π), [two conditional sampling
kernels](hyp:P₀,P₁), a [random scale](hyp:S), and a [scale multiplier](hyp:u),
histogram reconstruction bounds the ordered-sample mixture total variation by
the count-mixture total variation. The result is [the contraction bound from count-mixture to ordered-mixture total variation](goal). -/
lemma randomScale_ordered_tv_le_count_tv
    {Θ X : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (P₀ P₁ : Kernel Θ X) [∀ θ, IsProbabilityMeasure (P₀ θ)]
    [∀ θ, IsProbabilityMeasure (P₁ θ)] (S : Θ → ℝ≥0) (u : ℝ≥0) :
    Causalean.Stat.tvDist (rawMixture π P₀ S u) (rawMixture π P₁ S u) ≤
      Causalean.Stat.tvDist
        (π.bind (fun θ => independentPoissonCountLaw (P₀ θ) (u * S θ)))
        (π.bind (fun θ => independentPoissonCountLaw (P₁ θ) (u * S θ))) := by
  letI : IsProbabilityMeasure
      (π.bind (fun θ => independentPoissonCountLaw (P₀ θ) (u * S θ))) :=
    isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  letI : IsProbabilityMeasure
      (π.bind (fun θ => independentPoissonCountLaw (P₁ θ) (u * S θ))) :=
    isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  rw [← randomScale_count_mixture_reconstruction π P₀ S u,
    ← randomScale_count_mixture_reconstruction π P₁ S u]
  exact Causalean.Stat.tvDist_bind_le _ _ (histogramReconstructionKernel X)


/-- For a [probability mixing law](hyp:π), [two conditional sampling
kernels](hyp:P₀,P₁), a [random scale and multiplier](hyp:S,u), and a [fixed
sample size with fallback](hyp:n,fallback), the fixed-sample mixture distance
is bounded by the count-mixture distance plus twice the averaged short-count
probability. The result is [the fixed-sample total-variation bound with averaged short-count loss](goal). -/
lemma randomScale_fixed_tv_le_count_tv_add_tail
    {Θ X : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (P₀ P₁ : Kernel Θ X) [∀ θ, IsProbabilityMeasure (P₀ θ)]
    [∀ θ, IsProbabilityMeasure (P₁ θ)] (S : Θ → ℝ≥0) (u : ℝ≥0)
    (n : ℕ) (fallback : Fin n → X) :
    Causalean.Stat.tvDist (fixedMixture π P₀ n) (fixedMixture π P₁ n) ≤
      Causalean.Stat.tvDist
        (π.bind (fun θ => independentPoissonCountLaw (P₀ θ) (u * S θ)))
        (π.bind (fun θ => independentPoissonCountLaw (P₁ θ) (u * S θ))) +
      2 * ∫ θ, (poissonMeasure (u * S θ) (Set.Iio n)).toReal ∂π := by
  have ht := fixedMixture_tv_le_randomScalePoisson π P₀ P₁ S
    (measurable_of_finite _) u n fallback
    (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
  exact ht.trans (add_le_add
    (randomScale_ordered_tv_le_count_tv π P₀ P₁ S u) le_rfl)


/-- For a [probability mixing law](hyp:π), [two conditional sampling
kernels](hyp:P₀,P₁), a [random scale and multiplier](hyp:S,u), a [positive fixed
sample size with fallback](hyp:n,hn,fallback), and [conditional Poisson means at
least twice that size](hyp:hmean), the fixed-sample mixture distance is bounded
by the count-mixture distance plus `16 / n`. The result is [the fixed-sample total-variation bound with the `16 / n` correction](goal). -/
lemma randomScale_fixed_tv_le_count_tv_add_inverse
    {Θ X : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (P₀ P₁ : Kernel Θ X) [∀ θ, IsProbabilityMeasure (P₀ θ)]
    [∀ θ, IsProbabilityMeasure (P₁ θ)] (S : Θ → ℝ≥0) (u : ℝ≥0)
    (n : ℕ) (hn : 1 ≤ n) (fallback : Fin n → X)
    (hmean : ∀ θ, (2 : ℝ) * n ≤ (u * S θ : ℝ≥0)) :
    Causalean.Stat.tvDist (fixedMixture π P₀ n) (fixedMixture π P₁ n) ≤
      Causalean.Stat.tvDist
        (π.bind (fun θ => independentPoissonCountLaw (P₀ θ) (u * S θ)))
        (π.bind (fun θ => independentPoissonCountLaw (P₁ θ) (u * S θ))) +
      16 / (n : ℝ) := by
  have itail : Integrable
      (fun θ => (poissonMeasure (u * S θ) (Set.Iio n)).toReal) π := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_of_finite _).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
  have htail : (∫ θ, (poissonMeasure (u * S θ) (Set.Iio n)).toReal ∂π) ≤
      8 / (n : ℝ) := by
    calc
      _ ≤ ∫ _ : Θ, 8 / (n : ℝ) ∂π :=
        integral_mono itail (integrable_const _) (fun θ =>
          poisson_lower_tail_of_two_mul_le n (u * S θ) hn (hmean θ))
      _ = _ := by simp
  have htransfer := randomScale_fixed_tv_le_count_tv_add_tail π P₀ P₁ S u n fallback
  have heq : (16 : ℝ) / n = 2 * (8 / (n : ℝ)) := by ring
  rw [heq]
  exact htransfer.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left htail (by norm_num)))

end Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer

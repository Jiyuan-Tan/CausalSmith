module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Mixture
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.Reconstruction
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.CountReconstruction

/-! # Random-scale prefix comparison through independent Poisson counts

Histogram reconstruction retains the ordered experiment. The shared latent
scale need not be constant: only its uniform lower bound enters the short-count
loss. These lemmas implement the transfer in equations (15)--(16) of the
normalized-converse roadmap.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open scoped ENNReal NNReal





-- @node: pmf_bind_eq_finite_mixture
/-- Integrating a measure-valued map against a finite PMF is its finite weighted mixture. Given [the specified input `X`](hyp:X), [the specified input `f`](hyp:f), [the stated mathematical conclusion holds](goal). Given [the specified input `Θ`](hyp:Θ), [the specified input `π`](hyp:π). -/
lemma pmf_bind_eq_finite_mixture {Θ X : Type*} [Fintype Θ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace X]
    (π : PMF Θ) (f : Θ → Measure X) :
    π.toMeasure.bind f = ∑ θ : Θ, π θ • f θ := by
  rw [pmf_toMeasure_finset_decomposition, ← Measure.sum_fintype,
    Measure.bind_sum _ _ (measurable_of_finite _).aemeasurable, Measure.sum_fintype]
  simp only [Measure.bind_smul, Measure.dirac_bind (measurable_of_finite _)]

end CausalSmith.Stat.MarNearcompleteFrontier

import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The uniform histogram-fibre kernel

This module constructs the parameter-free Markov kernel which reconstructs a
finite ordered sample uniformly from the orderings compatible with a supplied
finite count vector, and records its singleton mass and support identities.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Given [a finite count vector](hyp:c), the [histogram reconstruction
distribution](goal) is uniform over all ordered samples having exactly those
counts.  Its definition depends only on the count vector, not on a sampling
law or intensity. -/
noncomputable def histogramReconstructionPMF
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (c : X → ℕ) : PMF (FiniteSample X) := by
  classical
  letI : Nonempty (HistogramFiber c) := histogramFiber_nonempty c
  exact (PMF.uniformOfFintype (HistogramFiber c)).map
    (fun x ↦ fixedSizeEmbed (histogramTotal c) x.1)

/-- On [a finite measurable alphabet](hyp:X), the [histogram reconstruction
kernel](goal) sends every count vector to the uniform distribution on its
ordered histogram fibre. -/
noncomputable def histogramReconstructionKernel
    (X : Type*) [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] :
    Kernel (X → ℕ) (FiniteSample X) :=
  Kernel.ofFunOfCountable fun c ↦ (histogramReconstructionPMF c).toMeasure

/-- On [a finite measurable alphabet](hyp:X), [the histogram reconstruction
channel is a Markov kernel](goal). -/
instance histogramReconstructionKernel_isMarkovKernel
    (X : Type*) [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] :
    IsMarkovKernel (histogramReconstructionKernel X) where
  isProbabilityMeasure c := by
    change IsProbabilityMeasure (histogramReconstructionPMF c).toMeasure
    infer_instance

/-- Given [a count vector](hyp:c) and [one compatible ordering](hyp:x), the
reconstruction kernel assigns [that ordered sample the reciprocal of the
histogram-fibre cardinality](goal). -/
theorem histogramReconstructionKernel_singleton
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (c : X → ℕ) (x : HistogramFiber c) :
    histogramReconstructionKernel X c
        {fixedSizeEmbed (histogramTotal c) x.1} =
      (Fintype.card (HistogramFiber c) : ℝ≥0∞)⁻¹ := by
  -- Unfold to `PMF.toMeasure`; the embedding of the subtype fibre into the
  -- dependent finite-sample type is injective, so its mapped singleton has
  -- the uniform source singleton mass.
  classical
  change (histogramReconstructionPMF c).toMeasure
    {fixedSizeEmbed (histogramTotal c) x.1} = _
  have hs : MeasurableSet
      ({fixedSizeEmbed (histogramTotal c) x.1} : Set (FiniteSample X)) := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change @MeasurableSet (Fin n → X) inferInstance
      ((Sigma.mk (β := fun k => Fin k → X) n) ⁻¹'
        ({fixedSizeEmbed (histogramTotal c) x.1} : Set (FiniteSample X)))
    by_cases hn : n = histogramTotal c
    · subst n
      convert (measurableSet_singleton x.1)
      ext y
      simp [fixedSizeEmbed]
    · convert MeasurableSet.empty
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro h
      exact hn (Sigma.mk.inj_iff.mp h).1
  rw [PMF.toMeasure_apply_singleton _ _ hs]
  unfold histogramReconstructionPMF
  rw [PMF.map_apply, tsum_eq_single x]
  · simp [fixedSizeEmbed]
  · intro a hax
    simp only [PMF.uniformOfFintype_apply, ite_eq_right_iff]
    intro h
    exact (hax (Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm)).elim

/-- Given [a count vector](hyp:c), reconstruction is [supported entirely on
finite ordered samples whose histogram is exactly that vector](goal). -/
theorem histogramReconstructionKernel_histogram_eq
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (c : X → ℕ) :
    histogramReconstructionKernel X c
        {s : FiniteSample X | finiteSampleHistogram s.points = c} = 1 := by
  -- Rewrite the PMF map on this event.  Every fibre element lands in it by
  -- its subtype certificate, so the preimage is `Set.univ`.
  classical
  change (histogramReconstructionPMF c).toMeasure
    {s : FiniteSample X | finiteSampleHistogram s.points = c} = 1
  have hs : MeasurableSet
      {s : FiniteSample X | finiteSampleHistogram s.points = c} := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change @MeasurableSet (Fin n → X) inferInstance
      ((Sigma.mk (β := fun k => Fin k → X) n) ⁻¹'
        {s : FiniteSample X | finiteSampleHistogram s.points = c})
    exact Set.Finite.measurableSet (Set.toFinite _)
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hs]
  unfold histogramReconstructionPMF
  rw [PMF.toOuterMeasure_map_apply]
  have hpre :
      (fun x : HistogramFiber c => fixedSizeEmbed (histogramTotal c) x.1) ⁻¹'
          {s : FiniteSample X | finiteSampleHistogram s.points = c} = Set.univ := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true]
    exact x.2
  rw [hpre]
  letI : MeasurableSpace (HistogramFiber c) := ⊤
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.univ]
  exact measure_univ

/-- Given [a count vector](hyp:c), pushing its reconstruction through the
histogram map [returns the point mass at the original count vector](goal). -/
theorem map_histogram_histogramReconstructionKernel
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (c : X → ℕ) :
    Measure.map (fun s : FiniteSample X ↦ finiteSampleHistogram s.points)
        (histogramReconstructionKernel X c) = Measure.dirac c := by
  -- Both sides are probability measures on a countable space.  Extensionality
  -- on singletons reduces the claim to the preceding support identity, or
  -- directly simplify the composition of the PMF map with the constant
  -- histogram map on `HistogramFiber c`.
  classical
  let hist := fun s : FiniteSample X => finiteSampleHistogram s.points
  have hhist : Measurable hist := by
    apply measurable_to_countable'
    intro d
    change MeasurableSet {s : FiniteSample X | finiteSampleHistogram s.points = d}
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change @MeasurableSet (Fin n → X) inferInstance
      ((Sigma.mk (β := fun k => Fin k → X) n) ⁻¹'
        {s : FiniteSample X | finiteSampleHistogram s.points = d})
    exact Set.Finite.measurableSet (Set.toFinite _)
  change Measure.map hist (histogramReconstructionPMF c).toMeasure = Measure.dirac c
  rw [PMF.toMeasure_map hist (histogramReconstructionPMF c) hhist]
  unfold histogramReconstructionPMF
  rw [PMF.map_comp]
  have hcomp :
      hist ∘ (fun x : HistogramFiber c =>
        fixedSizeEmbed (histogramTotal c) x.1) = Function.const _ c := by
    funext x
    exact x.2
  rw [hcomp, PMF.map_const, PMF.toMeasure_pure]

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction

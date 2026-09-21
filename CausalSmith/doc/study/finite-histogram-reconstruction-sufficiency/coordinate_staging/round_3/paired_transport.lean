/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction.Reconstruction
import Causalean.Stat.Minimax.TotalVariation
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Paired histogram reconstruction transport

This module forms the independent product of two histogram reconstruction
channels and transfers total variation from paired count experiments to paired
ordered finite Poisson samples over possibly unequal finite alphabets.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- On [two finite measurable alphabets](hyp:X,Y), the [paired histogram
reconstruction kernel](goal) independently reconstructs the two ordered
samples from their two count vectors. -/
noncomputable def pairedHistogramReconstructionKernel
    (X Y : Type*)
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y] :
    Kernel ((X → ℕ) × (Y → ℕ)) (FiniteSample X × FiniteSample Y) :=
  (histogramReconstructionKernel X).parallelComp
    (histogramReconstructionKernel Y)

/-- On [two finite measurable alphabets](hyp:X,Y), [the independent paired
histogram reconstruction channel is a Markov kernel](goal). -/
instance pairedHistogramReconstructionKernel_isMarkovKernel
    (X Y : Type*)
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y] :
    IsMarkovKernel (pairedHistogramReconstructionKernel X Y) := by
  unfold pairedHistogramReconstructionKernel
  infer_instance

/-- Given [two finite-alphabet probability laws](hyp:P,Q) and [possibly
different Poisson intensities](hyp:lambdaX,lambdaY), independently
reconstructing their product count law [recovers the product of their ordered
finite Poisson sample laws exactly](goal). -/
theorem pairedIndependentPoissonCountLaw_comp_reconstruction
    {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) :
    pairedHistogramReconstructionKernel X Y ∘ₘ
        ((independentPoissonCountLaw P lambdaX).prod
          (independentPoissonCountLaw Q lambdaY)) =
      (finitePoissonSampleLaw P lambdaX).prod
        (finitePoissonSampleLaw Q lambdaY) := by
  unfold pairedHistogramReconstructionKernel
  calc
    ((histogramReconstructionKernel X) ∥ₖ
          (histogramReconstructionKernel Y)) ∘ₘ
        ((independentPoissonCountLaw P lambdaX).prod
          (independentPoissonCountLaw Q lambdaY)) =
      ((histogramReconstructionKernel X) ∥ₖ Kernel.id) ∘ₘ
        ((Kernel.id ∥ₖ (histogramReconstructionKernel Y)) ∘ₘ
          ((independentPoissonCountLaw P lambdaX).prod
            (independentPoissonCountLaw Q lambdaY))) := by
      rw [Measure.comp_assoc, Kernel.parallelComp_comp_parallelComp,
        Kernel.comp_id, Kernel.id_comp]
    _ = ((histogramReconstructionKernel X) ∥ₖ Kernel.id) ∘ₘ
        ((independentPoissonCountLaw P lambdaX).prod
          ((histogramReconstructionKernel Y) ∘ₘ
            independentPoissonCountLaw Q lambdaY)) := by
      rw [← Measure.prod_comp_right]
    _ = ((histogramReconstructionKernel X) ∘ₘ
          independentPoissonCountLaw P lambdaX).prod
        ((histogramReconstructionKernel Y) ∘ₘ
          independentPoissonCountLaw Q lambdaY) := by
      rw [Measure.prod_comp_left]
    _ = (finitePoissonSampleLaw P lambdaX).prod
        (finitePoissonSampleLaw Q lambdaY) := by
      rw [independentPoissonCountLaw_comp_reconstruction,
        independentPoissonCountLaw_comp_reconstruction]

/-- Given [two pairs of probability laws on possibly different finite
alphabets](hyp:PX0,PX1,PY0,PY1) and [arbitrary, potentially unequal Poisson
intensities](hyp:lambdaX0,lambdaX1,lambdaY0,lambdaY1), the total variation
distance between the paired ordered Poisson experiments [is no larger than the
distance between their paired independent count experiments](goal). -/
theorem tvDist_paired_finitePoissonSampleLaw_le_counts
    {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (PX0 PX1 : Measure X) [IsProbabilityMeasure PX0] [IsProbabilityMeasure PX1]
    (PY0 PY1 : Measure Y) [IsProbabilityMeasure PY0] [IsProbabilityMeasure PY1]
    (lambdaX0 lambdaX1 lambdaY0 lambdaY1 : ℝ≥0) :
    Causalean.Stat.tvDist
        ((finitePoissonSampleLaw PX0 lambdaX0).prod
          (finitePoissonSampleLaw PY0 lambdaY0))
        ((finitePoissonSampleLaw PX1 lambdaX1).prod
          (finitePoissonSampleLaw PY1 lambdaY1)) ≤
      Causalean.Stat.tvDist
        ((independentPoissonCountLaw PX0 lambdaX0).prod
          (independentPoissonCountLaw PY0 lambdaY0))
        ((independentPoissonCountLaw PX1 lambdaX1).prod
          (independentPoissonCountLaw PY1 lambdaY1)) := by
  rw [← pairedIndependentPoissonCountLaw_comp_reconstruction,
    ← pairedIndependentPoissonCountLaw_comp_reconstruction]
  exact tvDist_bind_le _ _ (pairedHistogramReconstructionKernel X Y)

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

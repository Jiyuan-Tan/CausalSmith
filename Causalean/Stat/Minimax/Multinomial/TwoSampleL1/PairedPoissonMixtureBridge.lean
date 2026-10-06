module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.Reconstruction
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonCountBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonPredictive

/-!
# Ordered Poisson mixtures and paired count vectors

The ordered finite Poisson sample can be reconstructed from its cell counts by
a parameter-free uniform ordering kernel. This module isolates that
sufficiency step for the balanced product priors.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

/-- The predictive law of an ordered finite Poisson sample from one of the
balanced product priors. -/
noncomputable def pairedFinitePoissonPredictive {L : ℕ}
    (P : ScalarMomentPriors L) (b n : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (side : Bool) :
    Measure (FiniteSample (Fin (b * 2))) :=
  Causalean.Stat.mixture (pairedProductWeight P b side)
    (fun u => finitePoissonSampleLaw
      (simplexPMF (pairedTiltVector b hb t ht ht1
        (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u))).toMeasure
      (Real.toNNReal (2 * (n : ℝ))))

/-- Given [a scalar moment prior](hyp:P), [a positive balanced pair count and sample size](hyp:b,n,hb), and [a bounded nonnegative tilt](hyp:t,ht,ht1), [the finite-Poisson predictive distance is bounded by the paired count-law predictive distance](goal). -/
theorem pairedFinitePoissonPredictive_tv_le_counts {L : ℕ}
    (P : ScalarMomentPriors L) (b n : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Causalean.Stat.tvDist
      (pairedFinitePoissonPredictive P b n hb t ht ht1 false)
      (pairedFinitePoissonPredictive P b n hb t ht ht1 true) ≤
    Causalean.Stat.tvDist
      (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false)
      (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true) := by
  classical
  let R : (Fin b → ℕ × ℕ) → (Fin (b * 2) → ℕ) := fun z i =>
    if (finProdFinEquiv.symm i).2 = 0 then (z (finProdFinEquiv.symm i).1).1
    else (z (finProdFinEquiv.symm i).1).2
  let H : FiniteSample (Fin (b * 2)) → (Fin (b * 2) → ℕ) := fun s =>
    Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram s.points
  let K := Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramReconstructionKernel
    (Fin (b * 2))
  have hR : Measurable R := measurable_of_countable _
  have hH : Measurable H := by
    apply measurable_to_countable'
    intro c
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((Sigma.mk m) ⁻¹'
      {s : FiniteSample (Fin (b * 2)) | H s = c})
    exact (Set.to_countable _).measurableSet
  have hC : Measurable (pairedCountVector b) := by
    apply measurable_to_countable'
    intro c
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((Sigma.mk m) ⁻¹'
      {s : FiniteSample (Fin (b * 2)) | pairedCountVector b s = c})
    exact (Set.to_countable _).measurableSet
  have hfactor : H = R ∘ pairedCountVector b := by
    funext s i
    have he := finProdFinEquiv.apply_symm_apply i
    have hfin : (finProdFinEquiv.symm i).2 = 0 ∨
        (finProdFinEquiv.symm i).2 = 1 := by omega
    rcases hfin with h0 | h1
    · have hi : finProdFinEquiv ((finProdFinEquiv.symm i).1, 0) = i := by
        rw [← h0]
        exact he
      change i.modNat = 0 at h0
      simp [H, R, pairedCountVector,
        Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram,
        Fintype.card_subtype, h0]
      change finProdFinEquiv (i.divNat, 0) = i at hi
      rw [hi]
    · have hi : finProdFinEquiv ((finProdFinEquiv.symm i).1, 1) = i := by
        rw [← h1]
        exact he
      change i.modNat = 1 at h1
      simp [H, R, pairedCountVector,
        Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram,
        Fintype.card_subtype, h1]
      change finProdFinEquiv (i.divNat, 1) = i at hi
      rw [hi]
  have hcomponent (u : Fin b → Fin P.m) :
      K ∘ₘ Measure.map R
        (Measure.pi (fun j : Fin b =>
          scalarPoissonPairLaw ((n : ℝ) / (b : ℝ)) t (P.node (u j)))) =
        finitePoissonSampleLaw
          (simplexPMF (pairedTiltVector b hb t ht ht1
            (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u))).toMeasure
          (Real.toNNReal (2 * (n : ℝ))) := by
    let Q := (simplexPMF (pairedTiltVector b hb t ht ht1
      (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u))).toMeasure
    have hcount := pairedCountVector_map_finitePoissonSampleLaw b n hb t ht ht1
      (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u)
    change Measure.map (pairedCountVector b) (finitePoissonSampleLaw Q _) = _ at hcount
    change K ∘ₘ Measure.map R
      (Measure.pi (fun j : Fin b =>
        scalarPoissonPairLaw ((n : ℝ) / (b : ℝ)) t (pairedNodeVector P u j))) = _
    rw [← hcount, Measure.map_map hR hC]
    rw [← hfactor]
    rw [Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finitePoissonSampleLaw_map_histogram Q]
    exact Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw_comp_reconstruction Q _
  have hmixture (side : Bool) :
      K ∘ₘ Measure.map R
        (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t side) =
        pairedFinitePoissonPredictive P b n hb t ht ht1 side := by
    unfold pairedPoissonPredictive pairedFinitePoissonPredictive Causalean.Stat.mixture
    rw [Measure.map_finset_sum' hR.aemeasurable]
    simp_rw [Measure.map_smul]
    rw [← Measure.sum_fintype]
    rw [Measure.bind_sum _ _ K.aemeasurable]
    rw [Measure.sum_fintype]
    simp_rw [Measure.bind_smul]
    apply Finset.sum_congr rfl
    intro u _
    rw [hcomponent u]
  have hprob (side : Bool) :
      IsProbabilityMeasure (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t side) := by
    haveI (u : Fin b → Fin P.m) : IsProbabilityMeasure
        (Measure.pi (fun j : Fin b =>
          scalarPoissonPairLaw ((n : ℝ) / (b : ℝ)) t (P.node (u j)))) := by
      unfold scalarPoissonPairLaw
      infer_instance
    exact Causalean.Stat.mixture_isProbabilityMeasure
      (pairedProductWeight P b side) (pairedProductWeight_sum P b side) _
  letI : IsProbabilityMeasure
      (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false) := hprob false
  letI : IsProbabilityMeasure
      (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true) := hprob true
  letI : IsProbabilityMeasure
      (Measure.map R (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false)) :=
    Measure.isProbabilityMeasure_map hR.aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map R (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true)) :=
    Measure.isProbabilityMeasure_map hR.aemeasurable
  let D := Kernel.deterministic R hR
  calc
    Causalean.Stat.tvDist
        (pairedFinitePoissonPredictive P b n hb t ht ht1 false)
        (pairedFinitePoissonPredictive P b n hb t ht ht1 true) =
      Causalean.Stat.tvDist
        (K ∘ₘ Measure.map R
          (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false))
        (K ∘ₘ Measure.map R
          (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true)) := by
            rw [hmixture false, hmixture true]
    _ ≤ Causalean.Stat.tvDist
        (Measure.map R (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false))
        (Measure.map R (pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true)) :=
      Causalean.Stat.tvDist_bind_le _ _ K
    _ = Causalean.Stat.tvDist
        (D ∘ₘ pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t false)
        (D ∘ₘ pairedPoissonPredictive P b ((n : ℝ) / (b : ℝ)) t true) := by
          rw [Measure.deterministic_comp_eq_map hR,
            Measure.deterministic_comp_eq_map hR]
    _ ≤ _ := Causalean.Stat.tvDist_bind_le _ _ D

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FixedPoissonBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonMixtureBridge

/-!
# Fixed two-sample predictive comparison for balanced priors

The first multinomial sample has a common uniform law under both hypotheses.
The second sample carries the balanced perturbation. Finite Poisson samples
and their paired count vectors control the fixed predictive distance.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The fixed two-sample predictive law under one side of the balanced product prior: the mixture, with that side's product-prior weights, of the two-sample laws whose first sample is drawn from the uniform base vector and whose second sample is drawn from the vector tilted by t in the selected node directions. -/
noncomputable def pairedFixedPredictive {L : ℕ}
    (P : ScalarMomentPriors L) (b n : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (side : Bool) :
    Measure ((Fin n → Fin (b * 2)) × (Fin n → Fin (b * 2))) :=
  Causalean.Stat.mixture (pairedProductWeight P b side)
    (fun u => twoSampleLaw n
      (pairedBaseVector b hb,
        pairedTiltVector b hb t ht ht1
          (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u)))

/-- Given [a moment-matched prior](hyp:P), [a balanced pair count and sample size](hyp:b,n,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), and [the scale budget 100·(n/b)·t² ≤ L](hyp:hscale), [the total variation distance between the fixed two-sample predictive laws of the two prior sides is at most b · 2^(−L/4) plus twice the probability that a Poisson count with mean 2n falls below n](goal). -/
theorem pairedFixedPredictive_tv_le {L : ℕ}
    (P : ScalarMomentPriors L)
    (b n : ℕ) (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hscale : 100 * ((n : ℝ) / (b : ℝ)) * t ^ 2 ≤ (L : ℝ)) :
    Causalean.Stat.tvDist
      (pairedFixedPredictive P b n hb t ht ht1 false)
      (pairedFixedPredictive P b n hb t ht ht1 true) ≤
    (b : ℝ) * (2 : ℝ) ^ (-(L : ℝ) / 4) +
      2 * (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal := by
  classical
  let μ := simplexSampleLaw (pairedBaseVector b hb) n
  let R (u : Fin b → Fin P.m) :=
    pairedTiltVector b hb t ht ht1
      (pairedNodeVector P u) (pairedNodeVector_abs_le_one P u)
  let ν (side : Bool) := Causalean.Stat.mixture (pairedProductWeight P b side)
    (fun u => simplexSampleLaw (R u) n)
  have hfactor (side : Bool) :
      pairedFixedPredictive P b n hb t ht ht1 side = μ.prod (ν side) := by
    unfold pairedFixedPredictive Causalean.Stat.mixture
    change (∑ u, pairedProductWeight P b side u •
      (μ.prod (simplexSampleLaw (R u) n))) =
      μ.prod (∑ u, pairedProductWeight P b side u • simplexSampleLaw (R u) n)
    rw [← Measure.sum_fintype]
    rw [← Measure.sum_fintype]
    rw [Measure.prod_sum_right]
    simp_rw [Measure.prod_smul_right]
  have hνprob (side : Bool) : IsProbabilityMeasure (ν side) := by
    change IsProbabilityMeasure (Causalean.Stat.mixture
      (pairedProductWeight P b side) (fun u => simplexSampleLaw (R u) n))
    exact Causalean.Stat.mixture_isProbabilityMeasure
      (pairedProductWeight P b side) (pairedProductWeight_sum P b side) _
  haveI : IsProbabilityMeasure (ν false) := hνprob false
  haveI : IsProbabilityMeasure (ν true) := hνprob true
  have hfixed : Causalean.Stat.tvDist (ν false) (ν true) ≤
      Causalean.Stat.tvDist
        (pairedFinitePoissonPredictive P b n hb t ht ht1 false)
        (pairedFinitePoissonPredictive P b n hb t ht ht1 true) +
        2 * (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal := by
    let e : Fin (Fintype.card (Fin b → Fin P.m)) ≃ (Fin b → Fin P.m) :=
      (Fintype.equivFin _).symm
    let w (side : Bool) (i : Fin (Fintype.card (Fin b → Fin P.m))) :=
      pairedProductWeight P b side (e i)
    let S (i : Fin (Fintype.card (Fin b → Fin P.m))) := R (e i)
    have hw (side : Bool) : ∑ i, w side i = 1 := by
      exact (e.sum_comp (pairedProductWeight P b side)).trans
        (pairedProductWeight_sum P b side)
    have h := fixedSampleMixture_tv_le_finitePoisson n (b * 2)
      (Fintype.card (Fin b → Fin P.m)) (by omega)
      (Real.toNNReal (2 * (n : ℝ)))
      (w false) (w true) (hw false) (hw true) S S
    let F (side : Bool) (u : Fin b → Fin P.m) :
        Measure (Fin n → Fin (b * 2)) :=
      pairedProductWeight P b side u • simplexSampleLaw (R u) n
    let G (side : Bool) (u : Fin b → Fin P.m) :
        Measure (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample
          (Fin (b * 2))) :=
      pairedProductWeight P b side u •
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (simplexPMF (R u)).toMeasure (Real.toNNReal (2 * (n : ℝ)))
    change Causalean.Stat.tvDist (∑ i, F false (e i)) (∑ i, F true (e i)) ≤
      Causalean.Stat.tvDist (∑ i, G false (e i)) (∑ i, G true (e i)) +
        2 * (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal at h
    rw [e.sum_comp, e.sum_comp, e.sum_comp, e.sum_comp] at h
    simpa only [ν, pairedFinitePoissonPredictive, Causalean.Stat.mixture,
      F, G, R] using h
  have hcount := pairedFinitePoissonPredictive_tv_le_counts P b n hb t ht ht1
  have hpoisson := pairedPoissonPredictive_tv_le P b
    ((n : ℝ) / (b : ℝ)) t (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ht ht1 hscale
  calc
    Causalean.Stat.tvDist
        (pairedFixedPredictive P b n hb t ht ht1 false)
        (pairedFixedPredictive P b n hb t ht ht1 true) =
        Causalean.Stat.tvDist (μ.prod (ν false)) (μ.prod (ν true)) := by
          rw [hfactor false, hfactor true]
    _ ≤ Causalean.Stat.tvDist (ν false) (ν true) := by
      have h := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add
        μ μ (ν false) (ν true)
      simpa [Causalean.Stat.tvDist] using h
    _ ≤ _ := by linarith

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

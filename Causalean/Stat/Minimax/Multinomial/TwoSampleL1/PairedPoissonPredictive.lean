module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedProductPrior
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonComparison

/-!
# Product-prior Poisson predictive laws for balanced cell pairs

Independent scalar priors across balanced alphabet pairs give independent
Poisson count-pair predictive laws. Their total variation tensorizes.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory
open scoped BigOperators ENNReal

/-- The predictive count-vector law under one finite product prior, with one
independent balanced Poisson count pair for each alphabet pair. -/
noncomputable def pairedPoissonPredictive {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (lambda t : ℝ) (side : Bool) :
    Measure (Fin b → ℕ × ℕ) :=
  Causalean.Stat.mixture (pairedProductWeight P b side)
    (fun u => Measure.pi fun j : Fin b =>
      scalarPoissonPairLaw lambda t (P.node (u j)))

/-- Given [a moment prior](hyp:P), [a pair count](hyp:b), [a nonnegative Poisson intensity and bounded nonnegative tilt](hyp:lambda,t,hlambda,ht,ht1), and [the scale budget 100·λ·t² ≤ L](hyp:hscale), [the total variation distance between the paired Poisson predictive laws of the two prior sides is at most b · 2^(−L/4)](goal). -/
theorem pairedPoissonPredictive_tv_le {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (lambda t : ℝ) (hlambda : 0 ≤ lambda)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hscale : 100 * lambda * t ^ 2 ≤ (L : ℝ)) :
    Causalean.Stat.tvDist
      (pairedPoissonPredictive P b lambda t false)
      (pairedPoissonPredictive P b lambda t true) ≤
        (b : ℝ) * (2 : ℝ) ^ (-(L : ℝ) / 4) := by
  classical
  have hpair (u : ℝ) : IsProbabilityMeasure (scalarPoissonPairLaw lambda t u) := by
    unfold scalarPoissonPairLaw
    infer_instance
  have hscalar (side : Bool) :
      IsProbabilityMeasure (scalarPoissonPredictive P lambda t side) := by
    haveI (i : Fin P.m) : IsProbabilityMeasure
        (scalarPoissonPairLaw lambda t (P.node i)) := hpair _
    unfold scalarPoissonPredictive
    apply Causalean.Stat.mixture_isProbabilityMeasure
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.w₀_nonneg i), P.w₀_sum]
      simp
    · simp only [↓reduceIte]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.w₁_nonneg i), P.w₁_sum]
      simp
  have hfactor (side : Bool) :
      pairedPoissonPredictive P b lambda t side =
        Measure.pi (fun _ : Fin b => scalarPoissonPredictive P lambda t side) := by
    apply Measure.ext_of_singleton
    intro x
    haveI (u : ℝ) : IsProbabilityMeasure (scalarPoissonPairLaw lambda t u) := hpair u
    haveI : IsProbabilityMeasure (scalarPoissonPredictive P lambda t side) := hscalar side
    rw [Measure.pi_singleton]
    simp only [pairedPoissonPredictive, Causalean.Stat.mixture_apply,
      Measure.pi_singleton, pairedProductWeight, scalarPoissonPredictive,
      scalarPriorWeight]
    rw [Fintype.prod_sum]
    congr 1
    funext u
    rw [← Finset.prod_mul_distrib]
  haveI : IsProbabilityMeasure (scalarPoissonPredictive P lambda t false) :=
    hscalar false
  haveI : IsProbabilityMeasure (scalarPoissonPredictive P lambda t true) :=
    hscalar true
  rw [hfactor false, hfactor true]
  exact (Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le b _ _).trans
    (mul_le_mul_of_nonneg_left
      (scalarPoissonPredictive_tv_le P lambda t hlambda ht ht1 hscale)
      (Nat.cast_nonneg b))

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

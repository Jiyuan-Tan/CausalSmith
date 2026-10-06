module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.IdealRiskTransfer
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PoissonThinning
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RiskGeometry
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Expansion
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Risk

/-! Transfer from the finite prefix estimator to the independent ideal streams. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

attribute [local instance] Classical.propDecidable
attribute [local instance] map_obs_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,k,q,sample,hk,assign), [the stated mathematical conclusion holds](goal). -/
lemma streamAuxiliaryMixedValue_labeledPrefix {n d k : ℕ}
    (q : ℝ) (sample : Fin n → ObsRecord d) (hk : k ≤ n)
    (assign : Fin k → Fin 3) :
    streamAuxiliaryMixedValue n d q (labeledPrefix sample k hk assign) =
      auxiliaryMixedValue n q (fun i ↦ sample (Fin.castLE hk i)) assign := by
  unfold labeledPrefix
  rw [streamAuxiliaryMixedValue_unshuffle]
  rw [auxiliaryMixedValue_eq_poissonAuxiliaryMixedValue]
  congr 1

/-- Given [the specified inputs and assumptions](hyp:n,d,q,sample), [the stated mathematical conclusion holds](goal). -/
lemma mixedCountEstimator_eq_fixedStatistic (n d : ℕ) (q : ℝ)
    (sample : Fin n → ObsRecord d) :
    mixedCountEstimator n d q sample =
      fixedStatistic uniformPoolMass uniformPoolMass_sum ((n : ℝ≥0) / 2)
        sample (streamAuxiliaryMixedValue n d q) 0 := by
  rw [fixedStatistic_eq_finite_sum]
  simp only [mul_zero, add_zero]
  unfold mixedCountEstimator
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro k
  have hkn : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  simp only [dif_pos hkn]
  congr 1
  simp only [uniformPoolMass, streamAuxiliaryMixedValue_labeledPrefix]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro assign ha
  simp [uniformPoolMass, div_eq_mul_inv]
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P), [the stated mathematical conclusion holds](goal). -/
lemma deterministicRisk_mixedCountEstimator_le_streamRisk_add_tail
    (n d : ℕ) (q : ℝ) (P : FullLaw d) :
    deterministicRisk (mixedCountEstimator n d q) P ≤
      (∫ s, (streamAuxiliaryMixedValue n d q s - ate P) ^ 2
        ∂Measure.pi (fun _ : Fin 3 ↦
          finitePoissonSampleLaw (P.1.map obs)
            (((n : ℝ≥0) / 2) * (1 / 3)))) +
      4 * Real.exp (-(n : ℝ) * (Real.log 2 - 1 / 2)) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) := map_obs_isProbabilityMeasure P
  have htransfer := fixedRisk_le_independentRisk_add_tail
    (P.1.map obs) uniformPoolMass uniformPoolMass_sum ((n : ℝ≥0) / 2) n
    (measurable_streamAuxiliaryMixedValue n d q)
    (a := (-1 : ℝ)) (b := 1) (theta := ate P) (zOver := 0)
    (by norm_num) (streamAuxiliaryMixedValue_mem_Icc n d q)
    (ate_mem_Icc_of_fullLaw P) (by norm_num)
  have hfun : (fun sample : Fin n → ObsRecord d ↦
      fixedStatistic uniformPoolMass uniformPoolMass_sum ((n : ℝ≥0) / 2)
        sample (streamAuxiliaryMixedValue n d q) 0) =
      mixedCountEstimator n d q := by
    funext sample
    exact (mixedCountEstimator_eq_fixedStatistic n d q sample).symm
  rw [hfun] at htransfer
  have htransfer' : deterministicRisk (mixedCountEstimator n d q) P ≤
      (∫ s, (streamAuxiliaryMixedValue n d q s - ate P) ^ 2
        ∂Measure.pi (fun _ : Fin 3 ↦
          finitePoissonSampleLaw (P.1.map obs)
            (((n : ℝ≥0) / 2) * (1 / 3)))) +
      4 * (poissonMeasure ((n : ℝ≥0) / 2)).real (Set.Ioi n) := by
    norm_num at htransfer
    simpa [deterministicRisk, sqRisk, fixedPoolLaw, sampleLaw, uniformPoolMass]
      using htransfer
  refine htransfer'.trans ?_
  gcongr
  exact poisson_half_prefix_tail n

end CausalSmith.Stat.MarRareqLogfrontier

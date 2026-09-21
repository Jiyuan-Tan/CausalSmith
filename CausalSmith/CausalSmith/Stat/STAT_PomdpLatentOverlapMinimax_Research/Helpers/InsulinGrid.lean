module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinGridCore
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkAssembly

public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

set_option maxRecDepth 10000 in
/-- Interval arithmetic certifies the displayed strict bias enclosure. [the stated conclusion](goal). -/
lemma insulinGrid_bias_certificate (T : Nat) :
    -(6 / 1000 : ℝ) < immediateWeightBias T ∧
      immediateWeightBias T < -(58 / 10000 : ℝ) := by
  have hcb : ContractsL1
      (finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).b)
      (((1 / 2 : ℚ) : ℝ)) := by
    convert insulinFinitePolicyKernel_contractsL1 (T := T) false using 1 <;> norm_num
  have hce : ContractsL1
      (finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).e)
      (((1 / 2 : ℚ) : ℝ)) := by
    convert insulinFinitePolicyKernel_contractsL1 (T := T) true using 1 <;> norm_num
  have hb := stationaryRewardInterval_sound_of_chunked
    (insulinCertifiedKernel (T := T) false) (insulinChunkedIterateCertificate false)
    insulinRewardCertificate (1 / 2) insulinRho_nonneg insulinRho_lt_one
    hcb (insulinFiniteStationary (T := T) false)
  have he := stationaryRewardInterval_sound_of_chunked
    (insulinCertifiedKernel (T := T) true) (insulinChunkedIterateCertificate true)
    insulinRewardCertificate (1 / 2) insulinRho_nonneg insulinRho_lt_one
    hce (insulinFiniteStationary (T := T) true)
  have hb' : (insulinChunkedStationaryRewardInterval false).Contains
      (rewardExpectation
        (stationaryLaw (finitePolicyKernel (insulinGridFinite T)
          (insulinGridFinite T).b)) insulinStateReward) := by
    rw [← insulinChunkedStationaryRewardInterval_eq false]
    simp only [Bool.false_eq_true, if_false] at hb
    convert hb using 1 <;> rfl
  have he' : (insulinChunkedStationaryRewardInterval true).Contains
      (rewardExpectation
        (stationaryLaw (finitePolicyKernel (insulinGridFinite T)
          (insulinGridFinite T).e)) insulinStateReward) := by
    rw [← insulinChunkedStationaryRewardInterval_eq true]
    simp only [if_true] at he
    convert he using 1 <;> rfl
  have hd := RatInterval.sub_sound hb' he'
  rw [insulinImmediateWeightBias_eq]
  have hlo : (-(6 / 1000 : ℚ) : ℝ) < (insulinBiasInterval.lo : ℝ) := by
    exact_mod_cast insulinBiasInterval_bounds.1
  have hhi : (insulinBiasInterval.hi : ℝ) < (-(58 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast insulinBiasInterval_bounds.2
  unfold insulinBiasInterval at hlo hhi
  norm_num at hlo hhi
  constructor
  · nlinarith [hd.1]
  · nlinarith [hd.2]

end CausalSmith.Stat.PomdpLatentOverlapMinimax

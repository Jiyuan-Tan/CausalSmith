module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamMoments
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Capping and averaging the ideal four-stream estimator

The actual nonfallback estimator is the finite-partition conditional average.
Conditional Jensen and the Poisson cap coupling transfer its squared risk from
the projected ideal experiment, with a universal inverse-sample-size penalty.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- Singleton finite samples are measurable, by checking each fixed-size slice. Given [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_finiteSample_measurableSingletonClass
lemma upper_finiteSample_measurableSingletonClass (d : ℕ) :
    MeasurableSingletonClass (FiniteSample (Obs d)) := by
  constructor
  intro z
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((Sigma.mk m) ⁻¹' {z})
  exact Set.toFinite _ |>.measurableSet

/-- For [a sample size](hyp:n) and [a covariate dimension](hyp:d), [the ideal four-stream estimate is measurable](goal). -/
-- @node: upper_measurable_fourStreamEstimate
@[fun_prop] lemma upper_measurable_fourStreamEstimate (n d : ℕ) :
    Measurable (fourStreamEstimate n d) := by
  first | fun_prop |
    let := upper_finiteSample_measurableSingletonClass d
    exact measurable_of_countable _

/-- Projection confines every ideal estimate to the feasible target interval. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_fourStreamEstimate_range
lemma upper_fourStreamEstimate_range {n d : ℕ}
    (streams : Fin 4 → FiniteSample (Obs d)) :
    fourStreamEstimate n d streams ∈ Set.Icc (-1) 1 := by
  simp only [fourStreamEstimate, clipUnit, Set.mem_Icc]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Exponential Markov at tilt log two bounds the count-cap overflow for
an auxiliary Poisson count of mean half the sample size. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_half_mean_cap_tail_exp
lemma upper_half_mean_cap_tail_exp (n : ℕ) :
    (poissonMeasure ((n : NNReal) / 2)).real (Set.Ioi n) ≤
      Real.exp (-(Real.log 2 - 1 / 2) * (n : ℝ)) := by
  have hc := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    ((n : NNReal) / 2) n (r := 1) (by norm_num)
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-(n : ℝ) / 2))
  calc
    _ ≤ Real.exp (-Real.log 2 * (n : ℝ)) := by
      simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat,
        one_mul, neg_one_mul, neg_div, show (1 + 1 : ℝ) = 2 by norm_num, Set.Ioi] using hc
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The exponential cap penalty is bounded by eight inverse observations. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_half_mean_cap_tail_rate
lemma upper_half_mean_cap_tail_rate {n : ℕ} (hn : 0 < n) :
    (poissonMeasure ((n : NNReal) / 2)).real (Set.Ioi n) ≤ 8 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : (1 / 8 : ℝ) ≤ Real.log 2 - 1 / 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hx : 0 < (n : ℝ) / 8 := by positivity
  have hxe : (n : ℝ) / 8 ≤ Real.exp ((n : ℝ) / 8) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    _ ≤ Real.exp (-(Real.log 2 - 1 / 2) * (n : ℝ)) :=
      upper_half_mean_cap_tail_exp n
    _ ≤ Real.exp (-((n : ℝ) / 8)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ ((n : ℝ) / 8)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hx hxe
    _ = _ := by field_simp

/-- Conditional averaging and cap coupling bound the actual nonfallback
risk by projected independent-stream risk plus four times the overflow tail. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `hq`](hyp:hq), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hreg`](hyp:hreg). -/
-- @node: upper_nonfallback_risk_le_ideal_add_tail
lemma upper_nonfallback_risk_le_ideal_add_tail {n d : ℕ} (q : ℝ) (P : FullLaw d)
    (hq : q ≠ 1)
    (hreg : ¬(ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n)) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      (∫ streams, (fourStreamEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) +
        4 * (poissonMeasure ((n : NNReal) / 2)).real (Set.Ioi n) := by
  have ht := fixedRisk_le_independentRisk_add_tail (observedLaw P).toMeasure
    uniformFourMass uniformFourMass_sum ((n : NNReal) / 2) n
    (upper_measurable_fourStreamEstimate n d)
    (a := -1) (b := 1) (theta := tau P) (zOver := 0)
    (fun streams => upper_fourStreamEstimate_range streams)
    (tau_range P) (by norm_num)
  have hlaw : fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        (((n : NNReal) / 2) * uniformFourMass i)) := by
    unfold fourStreamLaw
    exact labeledStreamLaw_eq_independent _ _ _ _
  simp_rw [tauhatMM_nonfallback_eq_fixedStatistic q _ hq hreg]
  simpa only [Causalean.Stat.sqRisk, fixedPoolLaw, samplePi, hlaw,
    show ((1 : ℝ) - -1) ^ 2 = 4 by norm_num] using ht

/-- The fully implemented nonfallback estimator pays at most a universal
inverse-sample-size cost for its cap and auxiliary averaging. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `hq`](hyp:hq), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hreg`](hyp:hreg). -/
-- @node: upper_nonfallback_risk_le_ideal_add_rate
lemma upper_nonfallback_risk_le_ideal_add_rate {n d : ℕ} (hn : 0 < n)
    (q : ℝ) (P : FullLaw d) (hq : q ≠ 1)
    (hreg : ¬(ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n)) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      (∫ streams, (fourStreamEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) +
        32 / (n : ℝ) := by
  calc
    _ ≤ _ := upper_nonfallback_risk_le_ideal_add_tail q P hq hreg
    _ ≤ (∫ streams, (fourStreamEstimate n d streams - tau P) ^ 2 ∂fourStreamLaw n P) +
        4 * (8 / (n : ℝ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left
        (upper_half_mean_cap_tail_rate hn) (by norm_num : (0 : ℝ) ≤ 4)) _
    _ = _ := by ring

end CausalSmith.Stat.MarNearcompleteFrontier

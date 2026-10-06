module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.FullVarianceBudget
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.MembershipRatio
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotCorrection
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotTailBounds
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PrefixIdealTransfer
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioAggregate
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RawRiskAssembly
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RiskGeometry
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.SignedVariance

/-! The bounded auxiliary risk from marked moments and pilot selection. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hsmall,sample), [the stated mathematical conclusion holds](goal). -/
-- @node: mixedCountEstimator_eq_zero_of_effectiveSize_le_one
lemma mixedCountEstimator_eq_zero_of_effectiveSize_le_one
    (n d : ℕ) (q : ℝ) (hsmall : effectiveSize n q ≤ 1)
    (sample : Fin n → ObsRecord d) :
    mixedCountEstimator n d q sample = 0 := by
  simp [mixedCountEstimator, auxiliaryMixedValue, hsmall]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: riskEnvelope_eq_one_of_effectiveSize_le_one
lemma riskEnvelope_eq_one_of_effectiveSize_le_one
    (n d : ℕ) (q : ℝ) (hsmall : effectiveSize n q ≤ 1) :
    riskEnvelope n d q = 1 := by
  simp [riskEnvelope, hsmall]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: mixedCountEstimator_risk_eq_sq_of_effectiveSize_le_one
lemma mixedCountEstimator_risk_eq_sq_of_effectiveSize_le_one
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hsmall : effectiveSize n q ≤ 1) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂(sampleLaw n P)) = (cellFunctional P) ^ 2 := by
  let : IsProbabilityMeasure P.1 := P.2
  have : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
  have : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  simp only [mixedCountEstimator_eq_zero_of_effectiveSize_le_one n d q hsmall,
    zero_sub, neg_sq]
  simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_auxiliary_risk_envelope_small
lemma unrestricted_auxiliary_risk_envelope_small (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P)
    (hsmall : effectiveSize n q ≤ 1) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂(sampleLaw n P)) ≤ riskEnvelope n d q := by
  rw [mixedCountEstimator_risk_eq_sq_of_effectiveSize_le_one n d q P hsmall,
    riskEnvelope_eq_one_of_effectiveSize_le_one n d q hsmall]
  have htarget := cellFunctional_mem_Icc P hP
  nlinarith [htarget.1, htarget.2]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_mixedCountEstimator_risk_le_four
lemma unrestricted_mixedCountEstimator_risk_le_four (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂(sampleLaw n P)) ≤ 4 := by
  let : IsProbabilityMeasure P.1 := P.2
  have : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
  have : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  calc
    _ ≤ ∫ _sample : Fin n → ObsRecord d, (4 : ℝ) ∂sampleLaw n P := by
      apply integral_mono (Integrable.of_finite) (integrable_const _)
      intro sample
      exact sq_sub_le_four_of_mem_Icc
        ((mixed_count_estimator_regular n d q).2 sample)
        (cellFunctional_mem_Icc P hP)
    _ = 4 := by simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_auxiliary_risk_envelope_active
lemma unrestricted_auxiliary_risk_envelope_active (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P)
    (hb : needleBranch n d q) (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂sampleLaw n P) ≤ riskEnvelope n d q := by
  have ht := deterministicRisk_mixedCountEstimator_le_streamRisk_add_tail n d q P
  rw [unrestricted_cell_identification P hP] at ht
  rw [← integral_sq_poissonAuxiliaryMixedValue_eq_streams] at ht
  have hi := integral_sq_poissonAuxiliaryMixedValue_le_active_budget n d q P hP hb hlarge
  simp only [riskEnvelope, if_neg hlarge, not_true_eq_false, hb, if_false]
  apply le_min (unrestricted_mixedCountEstimator_risk_le_four n d q P hP)
  simp only [deterministicRisk, unrestricted_cell_identification P hP] at ht
  exact ht.trans (add_le_add hi le_rfl)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_integral_poissonRawMixedValue_bias_le_ratio
lemma abs_integral_poissonRawMixedValue_bias_le_ratio
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : ¬ needleBranch n d q) :
    |(∫ s, poissonRawMixedValue n d q s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellFunctional P| ≤
      8 * d / (Real.exp 1 * streamEffectiveSize n q) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hP.n_pos
  have hj (j : Cell d) : Integrable (fun s ↦ armSign j.1 * poissonMemberWeight n j s *
      poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
    simpa only [mul_assoc] using
      ((memLp_poissonMemberWeight_mul_selectedCellEstimate n d q P j).integrable
        (by norm_num)).const_mul (armSign j.1)
  have hc (j : Cell d) : cellContribution P j = cellProb P j * cellMean P j := by
    by_cases ha : 0 < arrivedCell P j
    · simp [cellContribution, ha]
    · simp [cellContribution, cellMean, ha]
  change |(∫ s, 2 * ∑ j : Cell d, armSign j.1 * poissonMemberWeight n j s *
    poissonSelectedCellEstimate n d q j s
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellFunctional P| ≤ _
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hj j)]
  simp_rw [mul_assoc (armSign _) (poissonMemberWeight _ _ _) _, integral_const_mul,
    integral_poissonMemberWeight_mul_selectedCellEstimate n d q P _ hn]
  rw [cellFunctional]
  simp_rw [hc, ← mul_assoc]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have heq : (∑ j : Cell d, (
      armSign j.1 * cellProb P j *
        (∫ s, poissonSelectedCellEstimate n d q j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
        armSign j.1 * cellProb P j * cellMean P j)) =
      ∑ j : Cell d, armSign j.1 * cellProb P j *
        ((∫ s, poissonSelectedCellEstimate n d q j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  simpa only [poissonSelectedCellEstimate, hb, false_and, if_false] using
    abs_ratioBranch_aggregate_bias_le n d q P hP


/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_poissonRawMixedValue_le_ratio_budget
lemma variance_poissonRawMixedValue_le_ratio_budget
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : ¬ needleBranch n d q) :
    variance (poissonRawMixedValue n d q)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 * (4 / streamEffectiveSize n q + 1 / streamSize n) := by
  rw [variance_poissonRawMixedValue_eq_four_sum]
  simp only [poissonSelectedCellEstimate, hb, false_and, if_false]
  exact mul_le_mul_of_nonneg_left
    (sum_variance_poissonMemberWeight_mul_ratioBranch_le n d q P hP) (by norm_num)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonAuxiliaryMixedValue_le_ratio_budget
lemma integral_sq_poissonAuxiliaryMixedValue_le_ratio_budget
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : ¬ needleBranch n d q)
    (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ s, (poissonAuxiliaryMixedValue n d q s - cellFunctional P) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      (8 * d / (Real.exp 1 * streamEffectiveSize n q)) ^ 2 +
        4 * (4 / streamEffectiveSize n q + 1 / streamSize n) := by
  have hbias := abs_integral_poissonRawMixedValue_bias_le_ratio n d q P hP hb
  have hs := mul_self_le_mul_self (abs_nonneg _) hbias
  have hs' : ((∫ s, poissonRawMixedValue n d q s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
      cellFunctional P) ^ 2 ≤ (8 * d / (Real.exp 1 * streamEffectiveSize n q)) ^ 2 := by
    simpa only [← sq, sq_abs] using hs
  have hv := variance_poissonRawMixedValue_le_ratio_budget n d q P hP hb
  refine (integral_sq_poissonAuxiliaryMixedValue_le_raw n d q P hP hlarge).trans ?_
  rw [integral_sq_poissonRawMixedValue_error_eq]
  exact (add_le_add hv hs').trans_eq (add_comm _ _)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_auxiliary_risk_envelope_ratio
lemma unrestricted_auxiliary_risk_envelope_ratio (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P)
    (hb : ¬ needleBranch n d q) (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂sampleLaw n P) ≤ riskEnvelope n d q := by
  have ht := deterministicRisk_mixedCountEstimator_le_streamRisk_add_tail n d q P
  rw [unrestricted_cell_identification P hP] at ht
  rw [← integral_sq_poissonAuxiliaryMixedValue_eq_streams] at ht
  have hi := integral_sq_poissonAuxiliaryMixedValue_le_ratio_budget n d q P hP hb hlarge
  simp only [riskEnvelope, if_neg hlarge, hb, not_false_eq_true, if_true]
  apply le_min (unrestricted_mixedCountEstimator_risk_le_four n d q P hP)
  simp only [deterministicRisk, unrestricted_cell_identification P hP] at ht
  exact ht.trans (add_le_add hi le_rfl)

-- @node: unrestricted_auxiliary_risk_envelope
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_auxiliary_risk_envelope (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P) :
    (∫ sample, (mixedCountEstimator n d q sample - cellFunctional P) ^ 2
      ∂(sampleLaw n P)) ≤ riskEnvelope n d q := by
  by_cases hsmall : effectiveSize n q ≤ 1
  · exact unrestricted_auxiliary_risk_envelope_small n d q P hP hsmall
  · by_cases hcap : riskEnvelope n d q = 4
    · rw [hcap]
      exact unrestricted_mixedCountEstimator_risk_le_four n d q P hP
    · by_cases hb : needleBranch n d q
      · exact unrestricted_auxiliary_risk_envelope_active n d q P hP hb hsmall
      · exact unrestricted_auxiliary_risk_envelope_ratio n d q P hP hb hsmall

end CausalSmith.Stat.MarRareqLogfrontier

module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TLocalCovarianceBias
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncatedExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperNumeratorExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperBiasLedger

/-! Finite-moment point-CATE frontier: Helpers/UpperBias. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- On the unit interval the original propensity regularity implies the effective exponent
used by the public tuning, with exactly the same Holder radius. -/
-- @node: upper_effective_propensity_holder
lemma upper_effective_propensity_holder (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) : holderBall (effectiveA κ) law.e := by
  refine ⟨hm.propensityHolder.1, hm.propensityHolder.2.1, ?_⟩
  intro x z
  have hd : |(x : ℝ) - z| ≤ 1 := abs_le.mpr
    ⟨by linarith [x.2.1, z.2.2], by linarith [x.2.2, z.2.1]⟩
  have ha : effectiveA κ ≤ κ.α := min_le_left _ _
  have hp : |(x : ℝ) - z|^κ.α ≤ |(x : ℝ) - z|^effectiveA κ := by
    by_cases hz : |(x : ℝ) - z| = 0
    · rw [hz, Real.zero_rpow hκ.2.1.1.ne',
        Real.zero_rpow (phase_algebra κ hκ).2.2.1.ne']
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)) hd ha
  exact (hm.propensityHolder.2.2 x z).trans (mul_le_mul_of_nonneg_left hp (by norm_num))

/-- The genuine localized covariance bound and public floor rounding control the untruncated
bias at the effective exponents, without changing the model class. -/
-- @node: upper_covariance_bias_tuned
lemma upper_covariance_bias_tuned (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law) :
    |localNumerator law (upperH κ n) (upperJ κ n) -
      law.theta * localDenominator law (upperH κ n) (upperJ κ n)| ≤ 1615 * rate κ n := by
  have ht := upper_tuning κ hκ n hn
  have ha : 0 < effectiveA κ ∧ effectiveA κ ≤ 1 :=
    ⟨(phase_algebra κ hκ).2.2.1, (min_le_left _ _).trans hκ.2.1.2⟩
  have hb := (local_covariance_bias_of_holder κ hκ law hm (effectiveA κ) ha
    (upper_effective_propensity_holder κ hκ law hm) (upperH κ n) ht.1 (upperJ κ n)).2
  change _ ≤ 400 * cellLen (upperH κ n) (upperJ κ n)^effectiveS κ +
    15 * (upperH κ n)^κ.γ at hb
  rw [ht.2.2.2.1] at hb
  have hround := ht.2.2.2.2.1
  nlinarith

/-- Independence and uniform design give the raw expectation identities and the public bias ledger. -/
-- @node: upper_bias
lemma upper_bias (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law) :
  (∫ o, denominatorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) =
    localDenominator law (upperH κ n) (upperJ κ n) ∧
  |(∫ o, numeratorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) -
    localNumerator law (upperH κ n) (upperJ κ n)| ≤
    20 * upperT κ n 0 ^ (1-κ.p) +
    400 * (∑ j : Fin (upperJ κ n), cellLen (upperH κ n) (j.val+1)^effectiveA κ * upperT κ n j.succ ^ (1-κ.p)) ∧
  |(∫ o, numeratorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) -
    localNumerator law (upperH κ n) (upperJ κ n)| +
    |localNumerator law (upperH κ n) (upperJ κ n)-law.theta*localDenominator law (upperH κ n) (upperJ κ n)| ≤
      cBias κ*rate κ n := by
  have htrunc : |(∫ o, numeratorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) -
      localNumerator law (upperH κ n) (upperJ κ n)| ≤
      20 * upperT κ n 0 ^ (1-κ.p) +
      400 * (∑ j : Fin (upperJ κ n), cellLen (upperH κ n) (j.val+1)^effectiveA κ *
        upperT κ n j.succ ^ (1-κ.p)) := by
    have hh := (upper_bandwidth_certificate κ hκ n hn).1
    have hT := upper_threshold_positive κ hκ n hn
    have ha : 0 < effectiveA κ ∧ effectiveA κ ≤ 1 :=
      ⟨(phase_algebra κ hκ).2.2.1, (min_le_left _ _).trans hκ.2.1.2⟩
    rw [upper_numerator_expectation κ n hn law hm.uniform,
      upper_conditional_error_identity κ hκ law hm (upperH κ n) hh
        (upperJ κ n) (upperT κ n) hT]
    exact upper_conditional_truncation_bias κ hκ law hm (upperH κ n) hh
      (effectiveA κ) ha (upper_effective_propensity_holder κ hκ law hm)
      (upperJ κ n) (upperT κ n) hT
  refine ⟨upper_denominator_expectation κ hκ n hn law hm, htrunc, ?_⟩
  have ht := upper_truncation_bias_ledger κ hκ n hn
  have hc := upper_covariance_bias_tuned κ hκ n hn law hm
  calc
    _ ≤ (20+400/constantA κ+1600/constantE κ)*rate κ n + 1615*rate κ n :=
      add_le_add (htrunc.trans ht) hc
    _ = cBias κ*rate κ n := by unfold cBias; ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

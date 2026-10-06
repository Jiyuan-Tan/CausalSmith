module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxUpperRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestIntervalGeometry
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestIntervalLower
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxCore
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Honest interval frontier

The explicit finite envelope in `honestConstant` calibrates the conservative
interval. The converse ranges over all measurable interval procedures. The shared
contrast-risk assembly is provided by `MinimaxUpperRisk`.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An explicit expected-length coefficient for the computable envelope
calibration. -/
noncomputable def honestLengthConstant (c : ClassConstants) (alpha : ℝ) : ℝ :=
  2 * Real.sqrt (honestConstant c alpha)

/-- The expected-length coefficient is strictly positive at positive
miscoverage levels. -/
-- @node: honestLengthConstant_pos
lemma honestLengthConstant_pos (c : ClassConstants) {alpha : ℝ} (ha : 0 < alpha) :
    0 < honestLengthConstant c alpha := by
  unfold honestLengthConstant
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (honestConstant_pos c ha))

/-- The declared length constant bounds expected length at every allowed
sample size, independently of the unfinished coverage calibration. -/
-- @node: honestInterval_expected_length_le
lemma honestInterval_expected_length_le (c : ClassConstants) (P : SubjectLaw)
    {alpha : ℝ} (ha : 0 < alpha) (n : ℕ) :
    (∫ s, volume.real (conservativeInterval c (honestConstant c alpha) s)
      ∂sampleLaw P n) ≤
      honestLengthConstant c alpha * Real.sqrt (riskScale c n) := by
  have h := conservativeInterval_expected_length_le c P (honestConstant c alpha) n
  rw [Real.sqrt_mul (honestConstant_pos c ha).le] at h
  simpa only [honestLengthConstant, mul_assoc] using h

/-- The explicit envelope construction used by the public calibration. -/
-- @node: honest_constant_construction
lemma honest_constant_construction (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlphaHalf : alpha < 1 / 2) :
    0 < honestConstant c alpha ∧ 0 < honestLengthConstant c alpha ∧
    ∀ n : ℕ, 3 ≤ n → ∀ P : SubjectLaw, ModelClass c P →
      1 - alpha ≤ (sampleLaw P n).real
        {s | causalTarget P ∈ conservativeInterval c (honestConstant c alpha) s} ∧
      (∫ s, volume.real
        (conservativeInterval c (honestConstant c alpha) s)
        ∂sampleLaw P n) ≤
        honestLengthConstant c alpha * Real.sqrt (riskScale c n) := by
  refine ⟨honestConstant_pos c hAlpha, honestLengthConstant_pos c hAlpha, ?_⟩
  intro n hn P hP
  refine ⟨?_, honestInterval_expected_length_le c P hAlpha n⟩
  exact conservativeInterval_coverage_of_sqRisk c P hP n hn
    (honestConstant c alpha) alpha (honestConstant_pos c hAlpha)
    (observableEstimator_sqRisk_le_honestConstant c P hP n hn alpha hAlpha)

-- @node: thm:honest-interval-frontier
theorem honest_interval_frontier (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    ∀ alpha : ℝ, 0 < alpha → alpha < 1 / 2 → -- @realizes alpha(miscoverage range)
      (∃ KAlpha CAlpha : ℝ,
      KAlpha = honestConstant c alpha ∧
      CAlpha = honestLengthConstant c alpha ∧
      0 < KAlpha ∧ 0 < CAlpha ∧
      (∀ n : ℕ, 3 ≤ n → ∀ P : SubjectLaw, ModelClass c P →
        1 - alpha ≤ (sampleLaw P n).real
          {s | causalTarget P ∈ conservativeInterval c KAlpha s} ∧
        (∫ s, volume.real
          (conservativeInterval c KAlpha s)
          ∂sampleLaw P n) ≤
          CAlpha * Real.sqrt (riskScale c n))) ∧
      (∃ cAlpha : ℝ, 0 < cAlpha ∧ ∀ n : ℕ, 3 ≤ n →
        ∀ lo hi : (Fin n → ObsHistory) → ℝ,
          Measurable lo → Measurable hi →
          (∀ P : SubjectLaw, ModelClass c P →
            1 - alpha ≤ (sampleLaw P n).real
              {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s}) →
          ∃ P : SubjectLaw, ModelClass c P ∧
            ENNReal.ofReal (cAlpha * Real.sqrt (riskScale c n)) ≤
              ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n) := by
  intro alpha hAlpha hAlphaHalf
  constructor
  · obtain ⟨hK, hC, hCoverage⟩ :=
      honest_constant_construction c hNonempty alpha hAlpha hAlphaHalf
    exact ⟨honestConstant c alpha, honestLengthConstant c alpha,
      rfl, rfl, hK, hC, hCoverage⟩
  · by_cases hk : c.kappa < 1
    · obtain ⟨a, ha, hparam⟩ :=
        honestInterval_parametric_lower c hNonempty alpha hAlphaHalf
      refine ⟨a, ha, ?_⟩
      intro n hn lo hi hlo hhi hcoverage
      simpa only [riskScale, if_pos hk] using hparam n hn lo hi hlo hhi hcoverage
    · apply honestInterval_lower_rate_of_eventual c hNonempty alpha hAlphaHalf
      exact honestInterval_eventual_lower_of_one_le_kappa c hNonempty
        (le_of_not_gt hk) alpha hAlphaHalf

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

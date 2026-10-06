module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.BoundedRisk

/-! Quantitative reciprocal moment certificate required by the Zeng lower bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:ε,c₁,c₂,c₄,n,d,K), [the mathematical structure](goal) records the components specified by this declaration. -/
structure ZengMomentPriorPair (ε c₁ c₂ c₄ : ℝ) (n d K : ℕ) where
  prior0 : Measure (ℝ × ℝ × ℝ)
  prior1 : Measure (ℝ × ℝ × ℝ)
  probability0 : IsProbabilityMeasure prior0
  probability1 : IsProbabilityMeasure prior1
  degree_pos : 1 ≤ K
  degree_calibration :
    (K : ℝ) ≤ c₂ * Real.log n ∧ c₂ * Real.log n < (K : ℝ) + 1
  finite_support :
    ∃ s0 s1 : Finset (ℝ × ℝ × ℝ),
      prior0 (s0 : Set (ℝ × ℝ × ℝ)) = 1 ∧
      prior1 (s1 : Set (ℝ × ℝ × ℝ)) = 1 ∧
      (∀ z ∈ s0,
        0 ≤ z.1 ∧ z.1 ≤ c₁ * Real.log n / n ∧
        ε ≤ z.2.1 ∧ z.2.1 ≤ 1 - ε ∧
        0 ≤ z.2.2 ∧ z.2.2 ≤ 1) ∧
      (∀ z ∈ s1,
        0 ≤ z.1 ∧ z.1 ≤ c₁ * Real.log n / n ∧
        ε ≤ z.2.1 ∧ z.2.1 ≤ 1 - ε ∧
        0 ≤ z.2.2 ∧ z.2.2 ≤ 1)
  matched_moments :
    ∀ i j k : ℕ, i + j + k ≤ 3 * K →
      (∫ z, z.1 ^ i * (z.1 * z.2.1) ^ j *
        (z.1 * z.2.1 * z.2.2) ^ k ∂prior0) =
      ∫ z, z.1 ^ i * (z.1 * z.2.1) ^ j *
        (z.1 * z.2.1 * z.2.2) ^ k ∂prior1
  mean_p_eq : (∫ z, z.1 ∂prior0) = ∫ z, z.1 ∂prior1
  mean_p_le : (∫ z, z.1 ∂prior0) ≤ ((d : ℝ))⁻¹
  separated_pmu :
    c₄ / ((n : ℝ) * Real.log n) ≤
      |(∫ z, z.1 * z.2.2 ∂prior1) - (∫ z, z.1 * z.2.2 ∂prior0)|

end CausalSmith.Stat.MarRareqLogfrontier

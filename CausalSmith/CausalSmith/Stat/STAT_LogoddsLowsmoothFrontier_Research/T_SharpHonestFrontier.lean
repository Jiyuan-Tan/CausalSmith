module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.FrontierSpecifications
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FrontierAssembly
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FrontierElbows
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FrontierMixtureRates
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FiniteHonestUpper
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ParametricNullFloor
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_OriginalRecordMixtures

/-! # T SharpHonestFrontier

The upper comparisons, operational guarantees, parametric numerator branch,
and combination of the lower rates use supporting lemmas. The mixture lower
rates follow from calibrated supports, original-record Hellinger bounds,
finite-prior testing, and uniform ceiling-rank estimates. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: thm:sharp-honest-frontier
/-- Positive absolute constants certify the entire domain and every radius, including randomized competitors. [the stated conclusion](goal) holds. -/
theorem sharp_honest_frontier : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  UniversalFrontier c C ∧ CompactUniform c C ∧
  (∀ α β : ℝ, ExponentDomain α β → ElbowIdentities α β) ∧
  (∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
    ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
      c*rate n α β r ≤ worstLength n α β r I) := by
  obtain ⟨cMix, cRadius, hcMix, hcRadius, hRough, hRadiusPositive⟩ :=
    frontier_mixture_lower_rates
  obtain ⟨C, hC, hUpper⟩ := frontier_upper_comparisons
  let cA : ℝ := min cMix (3/16)
  let c : ℝ := min cA cRadius / 2
  have hcA : 0 < cA := lt_min hcMix (by norm_num)
  have hc : 0 < c := div_pos (lt_min hcA hcRadius) (by norm_num)
  have hNumerator := frontier_numerator_lower_of_rough cMix hRough
  have hRadius := frontier_radius_lower_of_positive cRadius hRadiusPositive
  have hLower : ∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
      ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
        c*rate n α β r ≤ worstLength n α β r I := by
    intro α β r hD hr n hn I hI
    exact frontier_rate_lower_of_two n α β r cA cRadius hr.1 I
      (hNumerator α β r hD hr n hn I hI) (hRadius α β r hD hr n hn I hI)
  have hFrontier := universalFrontier_of_procedure_lower c C hUpper hLower
  exact ⟨c, C, hc, hC, hFrontier, frontier_compact_uniform c C hc,
    frontier_elbow_identities, hLower⟩
end CausalSmith.Stat.LogoddsLowsmoothFrontier

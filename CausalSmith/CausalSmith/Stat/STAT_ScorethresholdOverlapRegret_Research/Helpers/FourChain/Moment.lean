module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.MomentBuild

/-! # Score-threshold overlap regret — fourth-moment bound

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- The universal fourth-moment calculation after finite-chain reduction. -/
-- @node: localizedProcess_fourth_moment
lemma localizedProcess_fourth_moment :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ),
        0 < α → 0 < γ → 0 < θ → 0 < n → LawClass α γ θ n P e →
        ∀ (a z : ℝ), 0 < a → a ≤ 1/4 → 0 < z →
          (∫ d, (localizedProcess P a z d)^4 ∂sampleLaw P n)
            ≤ C*(z^2/((n:ℝ)^2*a^2) + z/((n:ℝ)^3*a^3)) := by
  obtain ⟨_, _, hbound⟩ := localizedProcess_fourth_moment_of_adapter
    buildLocalizedProcessL4Adapter
  exact ⟨81920 / 3, by norm_num, hbound⟩

end CausalSmith.Stat.ScorethresholdOverlapRegret

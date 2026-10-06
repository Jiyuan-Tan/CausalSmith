module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ParametricExperiment

/-! # T ParametricNullFloor

The constant-logit Bernoulli comparison and total-variation transfer give the
finite-sample root-n minimax length floor, including the radius-zero slice. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: lem:parametric-null-floor
/-- [A root-n length floor, including the radius-zero evaluation slice.](goal) Under [the stated assumptions](hyp:hD,hn). Under [the stated assumptions](hyp:hn,hr). -/
lemma parametric_null_floor (α β r : ℝ) (n : ℕ)
    (hD : ExponentDomain α β) (hn : 1 ≤ n) (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (3/16 : ℝ)*(n : ℝ)^(-(1/2 : ℝ)) ≤ lengthObjective n α β r := by
  -- The concrete comparison uses the fair null and a treated-outcome logistic shift.
  obtain ⟨P₀, P₁, hP₀, hP₁, hθ₀, hθ₁, htv⟩ :
      ∃ P₀ P₁ : ObservedLaw,
        RadiusModel α β r P₀ ∧ Model α β P₁ ∧ effect P₀ = 0 ∧
        effect P₁ = (1/4 : ℝ)*(n : ℝ)^(-(1/2 : ℝ)) ∧
        Causalean.Stat.tvDist (experimentLaw P₀ n) (experimentLaw P₁ n) ≤ 1/20 := by
    exact parametric_comparison α β r n hn hr.1
  have horder : effect P₀ ≤ effect P₁ := by
    rw [hθ₀, hθ₁]
    positivity
  have hbound := twoPoint_lengthObjective_lower P₀ P₁ n α β r (1/20)
    hP₀ hP₁ horder htv
  rw [hθ₀, hθ₁] at hbound
  convert hbound using 1 <;> ring
end CausalSmith.Stat.LogoddsLowsmoothFrontier

module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.Moment

/-! # Score-threshold overlap regret — four-chain fourth moment

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

-- @node: lem:four-chain-l4
/-- Universal fourth-moment maximal inequality for the atom-safe threshold process. -/
lemma four_chain_l4 :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ),
        0 < α → 0 < γ → 0 < θ → 0 < n → LawClass α γ θ n P e →
        ∀ (a z : ℝ), 0 < a → a ≤ 1/4 → 0 < z → -- @realizes a(0<a≤1/4); @realizes z(z>0)
          Measurable (fun d : Fin n → {o : Observation //
              o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
            localizedProcess (n := n) P a z (fun i => (d i).1)) ∧
          (∫ d, (localizedProcess P a z d)^4 ∂sampleLaw P n)
            ≤ C*(z^2/((n:ℝ)^2*a^2) + z/((n:ℝ)^3*a^3)) := by
  obtain ⟨C, hC, hmoment⟩ := localizedProcess_fourth_moment
  refine ⟨C, hC, ?_⟩
  intro α γ θ n P e hα hγ hθ hn hClass a z ha ha4 hz
  constructor
  · exact localizedProcess_measurable P a z hClass.wf ha hz
  · exact hmoment α γ θ n P e hα hγ hθ hn hClass a z ha ha4 hz

end CausalSmith.Stat.ScorethresholdOverlapRegret

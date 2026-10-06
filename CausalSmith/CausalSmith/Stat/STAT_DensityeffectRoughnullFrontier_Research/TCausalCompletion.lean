module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalIdentification

/-!
Existence of a conditionally independent causal completion and identification under every
consistent exchangeable completion.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


-- @node: prop:causal-completion
/-- Every benchmark law has an independent-potential completion; all consistent exchangeable
completions have the identified potential densities and their squared L² contrast equals Psi. -/
theorem causal_completion (P : ObsLaw) (hModel : Model P) :
    (∃ Q : Measure CausalSpace, ∃ hQ : IsProbabilityMeasure Q,
      IsCausalExtension P Q ∧ CausalConsistency Q ∧ CausalExchangeability Q hQ ∧
      IndependentPotentials Q hQ ∧ ∀ a, Q.map (potentialY a) = counterfactualMeasure P a) ∧
    (∀ Q : Measure CausalSpace, ∀ hQ : IsProbabilityMeasure Q,
      IsCausalExtension P Q → CausalConsistency Q → CausalExchangeability Q hQ →
      (∀ a, Q.map (potentialY a) = counterfactualMeasure P a) ∧
      Psi P = ∫ y,
        (marginalDensity P true y - marginalDensity P false y) ^ 2 ∂unitVolume) := by
  refine ⟨independentCausalCompletion_exists P hModel, ?_⟩
  intro Q hQ hExt hCons hEx
  exact ⟨causalExtension_map_potential P hModel Q hQ hExt hCons hEx, rfl⟩

end CausalSmith.Stat.DensityEffectRoughNull

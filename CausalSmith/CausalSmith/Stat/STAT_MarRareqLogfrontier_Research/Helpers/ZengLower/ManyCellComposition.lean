module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.MomentCertificateProof
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedFuzzy

/-! Paper moment certificates composed with conditioned fuzzy testing. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Stat.Minimax.MomentMatchedMixture

/-- For [the specified inputs and assumptions](hyp:ε,c₁,c₂,c₄,n,d,K,M), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def ZengMomentPriorPair.swap
    {ε c₁ c₂ c₄ : ℝ} {n d K : ℕ}
    (M : ZengMomentPriorPair ε c₁ c₂ c₄ n d K) :
    ZengMomentPriorPair ε c₁ c₂ c₄ n d K where
  prior0 := M.prior1
  prior1 := M.prior0
  probability0 := M.probability1
  probability1 := M.probability0
  degree_pos := M.degree_pos
  degree_calibration := M.degree_calibration
  finite_support := by
    obtain ⟨s0, s1, hs0, hs1, h0, h1⟩ := M.finite_support
    exact ⟨s1, s0, hs1, hs0, h1, h0⟩
  matched_moments := by
    intro i j k hijk
    exact (M.matched_moments i j k hijk).symm
  mean_p_eq := M.mean_p_eq.symm
  mean_p_le := by
    rw [← M.mean_p_eq]
    exact M.mean_p_le
  separated_pmu := by
    simpa [abs_sub_comm] using M.separated_pmu

/-- Given [the specified inputs and assumptions](hyp:ε,c₁,c₂,c₄,n,d,K,M), [the stated mathematical conclusion holds](goal). -/
lemma ZengMomentPriorPair.gap_or_swap_gap
    {ε c₁ c₂ c₄ : ℝ} {n d K : ℕ}
    (M : ZengMomentPriorPair ε c₁ c₂ c₄ n d K) :
    c₄ / ((n : ℝ) * Real.log n) ≤
        (∫ t, targetFunctional t ∂M.prior1) -
          ∫ t, targetFunctional t ∂M.prior0 ∨
      c₄ / ((n : ℝ) * Real.log n) ≤
        (∫ t, targetFunctional t ∂M.swap.prior1) -
          ∫ t, targetFunctional t ∂M.swap.prior0 := by
  let a := (∫ t, targetFunctional t ∂M.prior1) -
    ∫ t, targetFunctional t ∂M.prior0
  have hsep : c₄ / ((n : ℝ) * Real.log n) ≤ |a| := by
    simpa [a, targetFunctional] using M.separated_pmu
  by_cases ha : 0 ≤ a
  · left
    simpa [abs_of_nonneg ha, a] using hsep
  · right
    have hneg : a < 0 := lt_of_not_ge ha
    simpa [ZengMomentPriorPair.swap, a, abs_of_neg hneg] using hsep

end CausalSmith.Stat.MarRareqLogfrontier

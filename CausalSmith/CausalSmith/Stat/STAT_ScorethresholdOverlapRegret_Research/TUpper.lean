module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTail
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperComparison
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperIntegrability
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperExpectation
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperPeeling
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperRates

/-! # Score-threshold overlap regret — uniform upper bound

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

-- @node: thm:upper
/-- Uniform expected regret for the selector ordered false, true, then increasing
cutoffs with left orientation before right orientation at each cutoff. -/
theorem upper_bound (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ n ≥ N, ∀ P : RowLaw, ∀ e : ℝ → ℝ,
        ∀ hP : LawClass α γ θ n P e,
        (∫ d, regret (P.toWellFormedLaw hP.wf hP.bounded)
          (measurablePolicy (rateSelector α γ θ e d)) ∂sampleLaw P n)
          ≤ C*(n:ℝ)^(-rExp α γ θ) := by
  obtain ⟨Cm, hCm, hfour⟩ := four_chain_l4
  obtain ⟨Cr, hCr, hrem⟩ := upperRates_uniform_remainder α γ θ hα hγ hθ
  have hlarge := upperRates_schedule_eventually α γ θ 1 hα hγ hθ zero_lt_one
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e),
        (∫ d, regret (P.toWellFormedLaw hP.wf hP.bounded)
          (measurablePolicy (rateSelector α γ θ e d)) ∂sampleLaw P n) ≤
          ((16+65536*Cm)*Cr)*(n:ℝ)^(-rExp α γ θ) := by
    filter_upwards [hrem, hlarge] with n hrem hn
    intro P e hP
    let a := deletionSchedule α γ θ n
    have ha : 0 < a ∧ a ≤ 1/4 :=
      ⟨hn.2.2.1, hn.2.2.2.trans (min_le_right _ _)⟩
    have hm := fun z hz => hfour α γ θ n P e hα hγ hθ hn.1 hP a z ha.1 ha.2 hz
    have hloss := upperExpectation_selector_loss α γ θ n P e hP a Cm hn.1 ha hCm
      (upperIntegrability_selector_loss α γ θ n P e hP a ha.1)
      (fun z hz => upperIntegrability_process_fourth α γ θ n P e hP a z ha hn.1 (hm z hz).1)
      (fun z hz => (hm z hz).2)
    calc
      _ ≤ ∫ d, regularizedLoss P a (sortedSelector a e d) ∂sampleLaw P n :=
        upperIntegrability_selector_regret_le_loss α γ θ n P e hP a ha.1
      _ ≤ (16+65536*Cm)*(biasFunctional P a + ((n:ℝ)*a)⁻¹) := hloss
      _ ≤ (16+65536*Cm)*(Cr*(n:ℝ)^(-rExp α γ θ)) :=
        mul_le_mul_of_nonneg_left (hrem P e hP) (by positivity)
      _ = _ := by ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbound
  exact ⟨(16+65536*Cm)*Cr, N, by positivity, hN⟩

end CausalSmith.Stat.ScorethresholdOverlapRegret

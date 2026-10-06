module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TMixedCountUpper
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TFullExperimentLower

/-! TMatchedMinimaxFrontier for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:matched-minimax-frontier
/-- [the stated mathematical conclusion holds](goal). -/
theorem matched_minimax_frontier :
    -- @realizes \(\underline c\)(lower constant)
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes \(\overline C\)(upper constant)
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        RareArrivalSlice n q →
          c * frontierRate n d q ≤ minimaxRisk n d q ∧
          minimaxRisk n d q ≤ C * frontierRate n d q := by
  obtain ⟨c, hc, hlow⟩ := full_experiment_lower
  obtain ⟨C₀, hC₀, hupp⟩ := mixed_count_upper
  let C := max c C₀
  refine ⟨c, C, hc, le_max_left _ _, ?_⟩
  intro n d q hn hd hq hq1 hslice
  constructor
  · exact hlow n d q hn hd hq hq1 hslice
  · let f := mixedCountEstimator n d q
    have hEstimator := mixed_count_estimator_regular n d q
    let T : Estimator n d :=
      Estimator.ofMap f hEstimator
    have hrisk : ∀ (T : Estimator n d)
        (P : {P : FullLaw d // RareArrivalModelClass n d q P}),
        0 ≤ squaredRisk T P.1 := by
      intro T P
      exact integral_nonneg (fun s => integral_nonneg (fun t => sq_nonneg _))
    have hbound : ∀ (P : {P : FullLaw d // RareArrivalModelClass n d q P}),
        squaredRisk T P.1 ≤ C * frontierRate n d q := by
      intro P
      have h := hupp n d q P.1 P.2
      have hdet : squaredRisk T P.1 = deterministicRisk f P.1 := by
        simp [squaredRisk, deterministicRisk, T, Estimator.ofMap, Kernel.deterministic_apply]
      rw [hdet]
      have hN : 0 < effectiveSize n q := by
        unfold effectiveSize
        positivity
      have hrate : 0 ≤ frontierRate n d q := by
        unfold frontierRate
        exact le_min (by norm_num) (by positivity)
      exact (h.1.trans h.2.1).trans
        (mul_le_mul_of_nonneg_right (le_max_right c C₀) hrate)
    have hval : minimaxRisk n d q ≤ Causalean.Stat.worstCaseRiskReal
        (fun (T : Estimator n d) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          squaredRisk T P.1) T := by
      exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk T
    refine hval.trans ?_
    unfold Causalean.Stat.worstCaseRiskReal
    by_cases hne : Nonempty {P : FullLaw d // RareArrivalModelClass n d q P}
    · letI := hne
      exact ciSup_le hbound
    · haveI : IsEmpty {P : FullLaw d // RareArrivalModelClass n d q P} := not_nonempty_iff.mp hne
      simpa using (show (0 : ℝ) ≤ C * frontierRate n d q from by
        have hC : 0 ≤ C := le_trans (le_of_lt hC₀) (le_max_right c C₀)
        have hN : 0 < effectiveSize n q := by
          unfold effectiveSize
          positivity
        have hrate : 0 ≤ frontierRate n d q := by
          unfold frontierRate
          exact le_min (by norm_num) (by positivity)
        exact mul_nonneg hC hrate)

end CausalSmith.Stat.MarRareqLogfrontier

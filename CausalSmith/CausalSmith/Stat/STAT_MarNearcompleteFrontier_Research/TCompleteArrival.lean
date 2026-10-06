module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TPointFrontier
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TIntervalFrontier
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.CompleteArrivalRisk

/-!
# Complete-arrival endpoint

At `q=1` the estimator uses only the observed primary outcomes and the rate
loses its many-cell term. The point and interval constants remain uniform in `d`.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: prop:complete-arrival-reduction
/-- Complete arrival gives the projected HT estimator and uniform parametric frontiers. [the stated mathematical conclusion holds](goal). -/
theorem complete_arrival_reduction :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (α : ℝ), α ∈ Set.Ioo 0 ((1 : ℝ) / 2) →
        ∃ cα Cα : ℝ, 0 < cα ∧ cα < Cα ∧
          ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
            gScale n d 1 = 0 ∧
            rate n d 1 = 1 / (n : ℝ) ∧
            (∀ sample : Fin n → Obs d,
              tauhatMM n d 1 sample = completeHT sample) ∧
            (∀ (P : ClassLaw d 1) (sample : Fin n → Obs d),
              |tauhatMM n d 1 sample - tau P.val| ≤
                |unprojectedHT sample - tau P.val|) ∧
            (⨆ P : ClassLaw d 1,
              ∫ sample, (tauhatMM n d 1 sample - tau P.val) ^ 2 ∂
                samplePi P.val n) ≤
              (⨆ P : ClassLaw d 1,
                ∫ sample, (unprojectedHT sample - tau P.val) ^ 2 ∂
                  samplePi P.val n) ∧
            (⨆ P : ClassLaw d 1,
              ∫ sample, (unprojectedHT sample - tau P.val) ^ 2 ∂
                samplePi P.val n) ≤ 4 / (n : ℝ) ∧
            c / (n : ℝ) ≤ pointMinimaxRisk n d 1 ∧
            pointMinimaxRisk n d 1 ≤ C / (n : ℝ) ∧
            cα / Real.sqrt n ≤ lengthMinimaxRisk n d 1 α ∧
            lengthMinimaxRisk n d 1 α ≤ Cα / Real.sqrt n := by
  obtain ⟨c, C, hc, hcC, hpoint⟩ := point_frontier
  refine ⟨c, C, hc, hcC, ?_⟩
  intro α hα
  obtain ⟨cα, Cα, hcα, hcαCα, hinterval⟩ := interval_frontier α hα
  refine ⟨cα, Cα, hcα, hcαCα, ?_⟩
  intro n d hn hd
  have hq : (1 : ℝ) ∈ Set.Icc ((1 : ℝ) / 2) 1 := by constructor <;> norm_num
  have hp := hpoint n d 1 hn hd hq
  have hi := hinterval n d 1 hn hd hq
  letI : Nonempty (ClassLaw d 1) :=
    ⟨pairedClassLaw n d 1 0 hn hd hq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
      ⟨fun _ => Sum.inr (), fun _ => false⟩⟩
  have hunproj :
      (⨆ P : ClassLaw d 1,
        ∫ sample, (unprojectedHT sample - tau P.val) ^ 2 ∂samplePi P.val n) ≤
        4 / (n : ℝ) := by
    apply ciSup_le
    intro P
    exact complete_arrival_unprojected_risk_of_mean P.val hn
      (complete_arrival_score_mean P.val P.property)
  have hproj :
      (⨆ P : ClassLaw d 1,
        ∫ sample, (tauhatMM n d 1 sample - tau P.val) ^ 2 ∂samplePi P.val n) ≤
      (⨆ P : ClassLaw d 1,
        ∫ sample, (unprojectedHT sample - tau P.val) ^ 2 ∂samplePi P.val n) := by
    have hb : BddAbove (Set.range fun P : ClassLaw d 1 =>
        ∫ sample, (unprojectedHT sample - tau P.val) ^ 2 ∂samplePi P.val n) := by
      exact ⟨4 / (n : ℝ), fun z ⟨P, hz⟩ => hz ▸
        complete_arrival_unprojected_risk_of_mean P.val hn
          (complete_arrival_score_mean P.val P.property)⟩
    apply ciSup_le
    intro P
    exact le_trans (complete_arrival_projection_risk P.val)
      (le_ciSup hb P)
  refine ⟨complete_arrival_gScale n d, complete_arrival_rate n d,
    complete_arrival_estimator n d, ?_, hproj, hunproj, ?_, ?_, ?_, ?_⟩
  · intro P sample
    exact complete_arrival_projection_error P.val sample
  · simpa [complete_arrival_rate, div_eq_mul_inv] using hp.1
  · simpa [complete_arrival_rate, div_eq_mul_inv] using hp.2
  · simpa [complete_arrival_rate, Real.sqrt_div, div_eq_mul_inv] using hi.1
  · simpa [complete_arrival_rate, Real.sqrt_div, div_eq_mul_inv] using hi.2

end CausalSmith.Stat.MarNearcompleteFrontier

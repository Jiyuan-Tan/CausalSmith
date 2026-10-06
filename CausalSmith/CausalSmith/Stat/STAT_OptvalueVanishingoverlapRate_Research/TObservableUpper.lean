module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedGoodSquare
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullMarked
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedAssembly
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperGoodBadAssembly
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotAggregation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotClipped
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotCenter
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotScale
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedCounts
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedMoments
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperRiskAssembly
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperIndependentAggregation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullCell
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullPilot
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperOccupiedCell
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperLocalizedClipping
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotTail
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotRegularity

/-!
# Uniform observable upper risk
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

-- @node: thm:observable-upper
/-- [There are universal positive tuning constants and a measurable armwise estimator whose worst-case squared error over every admissible observed model is bounded above by a universal constant times the vanishing-overlap rate](goal). -/
theorem observable_upper :
    ∃ (H₀ κ Cstar : ℝ) (D₀ : ℕ),
      ∃ hH₀ : 0 < H₀, ∃ hκ : 0 < κ, ∃ hD₀ : 2 ≤ D₀,
      0 < Cstar ∧
      ∀ (n d : ℕ) (ε : ℝ),
        (hn : 1 ≤ n) → (hd : 2 ≤ d) → (hε : 0 < ε) → (hεhalf : ε ≤ 1 / 2) →
        Measurable (armwiseEstimator H₀ κ D₀ hH₀ hκ hD₀ n d ε hn hd ⟨hε, hεhalf⟩) ∧
        (∀ sampleLaw : ModelLaw d ε → Measure (Fin n → Obs d),
          (∀ P, IidSampling P.1 (sampleLaw P)) →
          (⨆ P : ModelLaw d ε,
            Causalean.Stat.sqRisk (sampleLaw P)
              (armwiseEstimator H₀ κ D₀ hH₀ hκ hD₀ n d ε hn hd ⟨hε, hεhalf⟩) (observedValue P.1)) ≤
            Cstar * rateScale n d ε) := by
  let H₀ : ℝ := Causalean.Stat.Concentration.PoissonSelfNormalized.universalH + 1
  have hH₀ : 0 < H₀ := by
    have h := Causalean.Stat.Concentration.PoissonSelfNormalized.universalH_pos
    dsimp [H₀]
    linarith
  have hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H₀ := by
    dsimp [H₀]
    linarith
  have hHlarge : 1 ≤ H₀ := by
    have h := Causalean.Stat.Concentration.PoissonSelfNormalized.universalH_pos
    dsimp [H₀]
    linarith
  obtain ⟨κ, C, hκ, hC, hmarked⟩ :=
    markedPoissonStatistic_active_rate_tuning_exists H₀ hH₀ hH hHlarge
  have hL := logAlphabet_pos (d := 2) (by omega)
  refine ⟨H₀, κ, 3 + 8 * logAlphabet 2 + 8 * C, 2, hH₀, hκ, by omega,
    by positivity, ?_⟩
  intro n d ε hn hd hε hεhalf
  constructor
  · fun_prop
  · intro sampleLaw hiid
    exact (armwiseEstimator_allBranches_worstRisk_le H₀ κ 2 hH₀ hκ (by omega)
      hn hd hε hεhalf hC.le sampleLaw hiid
      (fun _ hactive P => hmarked hn (by omega) P.1 ε hε hεhalf P.2 hactive)).2
  -- @realizes \(C_\star\)(universal upper constant)

end CausalSmith.Stat.OptvalueVanishingoverlapRate

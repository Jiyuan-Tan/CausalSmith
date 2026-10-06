module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Lower
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellComponents

/-!
# TTwoCellCalibration

Finite original-record private value frontiers: TTwoCellCalibration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


-- @node: thm:two-cell-calibration
/-- The two-cell model has [universal finite private risk bounds, globally honest length bounds,
and explicit attainment](goal). -/
theorem two_cell_calibration :
    ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
      -- @realizes c(universal positive lower constant); @realizes C_0(universal finite upper constant)
      ∀ (n : ℕ) (eps : ℝ), Allowed n 2 eps →
      ∀ (S : SamplingScheme n 2), IidPeople S → IndependentRandomness S →
      ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c * min 1 (1/(n*eps^2))) ≤ minimaxRisk S C eps ∧
        minimaxRisk S C eps ≤ ENNReal.ofReal (C0 * min 1 (1/(n*eps^2))) ∧
        ENNReal.ofReal (c * min 1 (1/(Real.sqrt n*eps))) ≤ honestLength S C eps ∧
        honestLength S C eps ≤ ENNReal.ofReal (C0 * min 1 (1/(Real.sqrt n*eps))) ∧
        CausalAttainment S eps (min 1 (1/(n*eps^2))) (min 1 (1/(Real.sqrt n*eps))) C0 := by
  obtain ⟨c1, hc1, hLower⟩ :=
    dimension_free_private_two_point measurableKernelRadonNikodym_proved
  refine ⟨min c1 1, 1000, lt_min hc1 (by norm_num),
    (min_le_right c1 1).trans (by norm_num), ?_⟩
  intro n eps hAllowed S hIID hRandom C
  have heps : 0 < eps := hAllowed.2.2.1
  have hAttain : CausalAttainment S eps (min 1 (1/(n*eps^2)))
      (min 1 (1/(Real.sqrt n*eps))) 1000 := by
    by_cases ht : (n : ℝ)*eps^2 ≤ 1
    · exact causalAttainment_mono_constant S eps _ _ 1 1000
        (by positivity) (by positivity) (by norm_num)
        (two_cell_saturated_attainment n eps hAllowed S hIID hRandom ht)
    · apply two_cell_unsaturated_attainment_of_components eps hAllowed S hIID hRandom
        (lt_of_not_ge ht)
      exact twoCellComponents_of_sampling n eps hAllowed S hIID hRandom
  obtain ⟨hRiskUpper, hLengthUpper⟩ :=
    causalAttainment_minimax_upper S eps _ _ 1000 hAttain C
  obtain ⟨hRiskLower, hLengthLower⟩ := hLower n 2 eps hAllowed S hIID hRandom C
  refine ⟨?_, hRiskUpper, ?_, hLengthUpper, hAttain⟩
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left c1 1) (by positivity))).trans hRiskLower
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left c1 1) (by positivity))).trans hLengthLower


end CausalSmith.Stat.LdpOptvalueUniformFrontier

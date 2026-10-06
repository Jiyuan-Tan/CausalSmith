module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.EnvelopeRate

/-! TUnrestrictedUniformMixedCountCertificate for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:unrestricted-uniform-mixed-count-certificate
/-- [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_uniform_mixed_count_certificate :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(\overline C\)(universal upper constant)
      ∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        UnrestrictedArrivalModelClass n d q P →
        IIDSampling n (sampleLaw n P)
          (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i) P →
        (∫ s, (mixedCountEstimator n d q s - cellFunctional P) ^ 2
          ∂(sampleLaw n P)) ≤ riskEnvelope n d q ∧
        riskEnvelope n d q ≤ C * frontierRate n d q := by
  obtain ⟨C, hC, hrate⟩ := riskEnvelope_le_frontierRate
  refine ⟨C, hC, ?_⟩
  intro n d q P hP _
  exact ⟨unrestricted_auxiliary_risk_envelope n d q P hP,
    hrate n d q hP.n_pos hP.d_pos hP.q_pos hP.q_le_one⟩

end CausalSmith.Stat.MarRareqLogfrontier

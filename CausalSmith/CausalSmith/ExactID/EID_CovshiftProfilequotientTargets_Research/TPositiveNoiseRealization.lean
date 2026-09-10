import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Completion

/-! # Positive-noise realization theorem -/

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @node: thm:positive-noise-realization
theorem positive_noise_realization {d E r : ℕ} (θ : CovarianceTuple d E)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hBase : BaselinePositive θ) (hRank : AggregateExactRank θ r)
    (hRange : CommonShiftRange θ) (T : Finset (Fin d)) (t : Fin r → Fin d)
    (hCert : Cert θ T t) :
    ∃ M : CovShiftModel d E r,
      LegalCovShiftModel M ∧
      CompletionRealizes (positiveNoiseCompletion θ T t hCert hd hBase) M ∧
      M.target = T ∧ (∀ e, M.covOf e = θ.cov e) ∧
      PositiveStructuralNoise M ∧ PositiveMeasurementNoise M := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets

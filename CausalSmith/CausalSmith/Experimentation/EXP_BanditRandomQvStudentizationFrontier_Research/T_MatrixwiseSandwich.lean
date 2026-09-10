/- Finite-polarization upgrade from contrastwise to matrixwise invariance. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.T_ContrastwiseSandwich

/-! # Matrixwise deterministic-sandwich boundary -/

open Filter MeasureTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

-- @node: thm:matrixwise-deterministic-sandwich-iff
theorem matrixwise_deterministic_sandwich_iff
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q m : ℕ} [MeasurableSpace (Mat d)] [BorelSpace (Mat d)]
    (hd : 0 < d) (S : FiniteAttractorSandwichSequence Ω 𝒳 K d q m)
    (Sigma : Mat d) (hSigma : PositiveDefinite Sigma)
    (hVpositive : ∀ᵐ V ∂S.mu, PositiveDefinite V)
    (hVsymm : ∀ᵐ V ∂S.mu, transpose V = V)
    (hSigmaSymm : transpose Sigma = Sigma) :
    ((∀ c : Vec d, ∀ hc : c ≠ 0, ∀ alpha, ∀ halpha : 0 < alpha ∧ alpha < 1,
      Tendsto (fun l => ((S.E l).law {ω |
        dot c (S.E l).thetaStar ∈ deterministicWaldInterval (S.T l)
          (ipwZEstimator (S.estimator l)) (S.T_pos l) Sigma hSigma c hc alpha halpha ω}).toReal)
        atTop (𝓝 (1 - alpha))) ↔
      (∀ᵐ V ∂S.mu, V = Sigma)) ∧
    ((∀ᵐ V ∂S.mu, V = Sigma) ↔ S.mu {Sigma} = 1) ∧
    ((∀ l, Measure.map
        (terminalV (S.E l) (S.etaInf l) (S.member l).etaInf_mem) (S.E l).law = S.mu) →
      ((∀ᵐ V ∂S.mu, V = Sigma) ↔
        ∀ l, ∀ᵐ ω ∂(S.E l).law,
          terminalV (S.E l) (S.etaInf l) (S.member l).etaInf_mem ω = Sigma)) := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV

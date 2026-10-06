module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ClippedIdealBridge
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.DegreeTuning

/-! Depoissonization and the uniform risk bound for the total estimator. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

lemma known_radius_estimator_risk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n M rho (P : KnownRadiusClass n M rho),
      3 ≤ n →
      DiscreteAteHeterogeneityFrontier.mse P.law
        (knownRadiusEstimator n M rho) ≤ C * M ^ 2 * rate n rho := by
  obtain ⟨Cp, hCp, hpilot⟩ := pilot_risk_bound
  obtain ⟨C, hC, htune⟩ := degree_tuning_concrete_risk_terms Cp hCp.le
  refine ⟨C, hC, ?_⟩
  intro n M rho P hn
  have hfinite := knownRadiusEstimator_sqRisk_le_idealProduct_add_geometric M rho P
  have hideal := idealProduct_pilot_sqRisk_le M rho Cp P
    (hpilot n M rho P hn)
  have ht := htune n M rho hn P.M_ge_one P.radius.1.1 P.radius.1.2
  calc
    _ ≤ (∫ sample : Fin n → SampleObs n,
          ∫ q : Fin n → IdealCellSample n,
            (pilotTau n M sample +
              ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
              DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
            ∂idealProductLaw P.law
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) +
        4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
      simpa only [DiscreteAteHeterogeneityFrontier.mse, Causalean.Stat.sqRisk]
        using hfinite
    _ ≤ (3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
          (degree n rho : ℝ) ^ 4 / n) +
        (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
          (M ^ 2 * rho ^ 2 +
            Cp * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ)))) +
        4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
      simpa only [add_comm] using add_le_add_left hideal
        (4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2))
    _ ≤ _ := ht

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

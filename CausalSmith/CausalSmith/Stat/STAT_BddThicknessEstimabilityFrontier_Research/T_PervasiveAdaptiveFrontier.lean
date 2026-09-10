import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ThicknessEntropySeparation

/-! # Count-adaptive pervasive frontier -/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @node: thm:pervasive-adaptive-frontier
/-- The empirical-count estimator is independent of `κ` and the score density,
attains the pervasive rate uniformly on the base class, includes the explicit
fallback-event contribution, and matches the pervasive lower bound. -/
theorem pervasive_adaptive_frontier (κbar L σ cm Cm h0 : ℝ)
    (A0 A1 B : Set Score)
    (hparams : 2 < κbar ∧ 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧ 0 < h0 ∧ h0 < 1)
    (hgeometry : FixedAssignmentGeometry A0 A1 B)
    (hiid : ∀ n κ P,
      P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B →
      IidSampling n P (observedSampleLaw P n))
    :
    (∀ n, MeasurableBoundaryEstimator
      (geometryMassAdaptiveEstimator n A0 A1 L σ h0)) ∧
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ N : ℕ, ∀ κ, 2 < κ → κ ≤ κbar → ∀ n, N ≤ n →
      (⨆ P : BoundaryLaw,
        ⨆ (_hP : P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B),
        estimatorExpectedSupLoss (geometryMassAdaptiveEstimator n A0 A1 L σ h0) P) ≤
          ENNReal.ofReal (C * pervasiveRate n κ) ∧
      (⨆ P : BoundaryLaw,
        ⨆ (_hP : P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B),
        observedSampleLaw P n {w | ∃ x ∈ B, ∃ t : Fin 2,
          geometryAdmissibleBandwidths A0 A1 w t x h0 = ∅}) ≤
          ENNReal.ofReal (C * n ^ 3 * Real.exp (-c * n * cm * h0 ^ κ)) ∧
      ((lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B).Nonempty →
        ENNReal.ofReal (c * pervasiveRate n κ) ≤
          expectedSupMinimaxRisk n
            (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ∧
        expectedSupMinimaxRisk n
            (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ≤
          expectedSupMinimaxRisk n
            (lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B) ∧
        expectedSupMinimaxRisk n
            (lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B) ≤
          ENNReal.ofReal (C * pervasiveRate n κ)) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

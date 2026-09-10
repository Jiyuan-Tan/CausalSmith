-- The matched-rate conclusion specializes the preceding bracket.
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ArbitraryModulusTwoSidedBracket

/-! # Limitation of a lower-profile-only class -/

open Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @node: thm:lower-profile-only-class-cannot-recover-isolated-frontier
/-- With the one-site lower declaration, the arbitrary-modulus class contains
both isolated and pervasive subclasses, hence inherits the pervasive rate and
cannot recover the isolated frontier. -/
theorem lower_profile_only_class_cannot_recover_isolated_frontier
    (κbar κ L σ cm Cm h0 : ℝ) (A0 A1 B : Set Score) (xstar : Score)
    (hκ : AdmissibleExponentRange κbar κ)
    (hparams : 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧ 0 < h0 ∧ h0 < 1)
    (hcircular : A1 = {z | signedRadius z ≤ 0} ∧
      A0 = {z | 0 < signedRadius z} ∧ B = unitCircle)
    (hgeometry : FixedAssignmentGeometry A0 A1 B)
    (hcertificate : ∀ κ', 2 < κ' → κ' ≤ κbar →
      ∃ Pperv Piso : BoundaryLaw,
        circularThinningWitness Pperv Piso κ' h0 σ xstar ∧
        PervasiveThinningClass Pperv L σ cm Cm κ' h0 ∧
        IsolatedThinningClass Piso L σ cm Cm κ' h0)
    (hiid : ∀ n P,
      P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B →
      IidSampling n P (observedSampleLaw P n)) :
    let m : ℝ → ℝ≥0∞ := fun h => ENNReal.ofReal (cm * h ^ κ)
    let Jminus : ℝ → ℝ≥0∞ → ℕ∞ := fun h u =>
      if ENNReal.ofReal (Cm * h ^ κ) ≤ u then 1 else 0
    lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B ∪
      lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B ⊆
        lawsOnGeometry (modulusProfileLaws L σ h0 m Jminus) A0 A1 B ∧
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ENNReal.ofReal (c * pervasiveRate n κ) ≤
        expectedSupMinimaxRisk n
          (lawsOnGeometry (modulusProfileLaws L σ h0 m Jminus) A0 A1 B) ∧
      expectedSupMinimaxRisk n
          (lawsOnGeometry (modulusProfileLaws L σ h0 m Jminus) A0 A1 B) ≤
        ENNReal.ofReal (C * pervasiveRate n κ) ∧
      pervasiveRate n κ / isolatedRate n κ =
        (Real.log n) ^ (1 / (κ + 2)) ∧
      Tendsto (fun n : ℕ => pervasiveRate n κ / isolatedRate n κ) atTop atTop := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

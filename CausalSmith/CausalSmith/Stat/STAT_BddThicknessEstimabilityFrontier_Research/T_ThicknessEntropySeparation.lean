import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.DiskPattern
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Causalean.Mathlib.Analysis.ClipInterval

/-! # Same-modulus thickness--entropy separation -/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @node: thm:thickness-entropy-separation
/-- Isolated and pervasive classes share the polynomial side-mass modulus but
have different expected-sup minimax frontiers.  The comparison constants are
independent of sample size. -/
theorem thickness_entropy_separation (κbar κ L σ cm Cm h0 : ℝ)
    (A0 A1 B : Set Score)
    (hrange : AdmissibleExponentRange κbar κ)
    (hparams : 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧ 0 < h0 ∧ h0 < 1)
    (hgeometry : FixedAssignmentGeometry A0 A1 B)
    (hiso : (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B).Nonempty)
    (hperv : (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B).Nonempty)
    (hiid : ∀ n P,
      P ∈ lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B ∪
        lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B →
      IidSampling n P (observedSampleLaw P n)) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ENNReal.ofReal (c * isolatedRate n κ) ≤
        expectedSupMinimaxRisk n
          (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B) ∧
      expectedSupMinimaxRisk n
          (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B) ≤
        ENNReal.ofReal (C * isolatedRate n κ) ∧
      ENNReal.ofReal (c * pervasiveRate n κ) ≤
        expectedSupMinimaxRisk n
          (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ∧
      expectedSupMinimaxRisk n
          (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ≤
        ENNReal.ofReal (C * pervasiveRate n κ) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

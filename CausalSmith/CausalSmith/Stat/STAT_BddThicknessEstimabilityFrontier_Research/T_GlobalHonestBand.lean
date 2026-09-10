import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.BandWidth
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.DiskPattern
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_PervasiveAdaptiveFrontier
import Causalean.Stat.Minimax.TotalVariation

/-! # Globally calibrated honest band and width obstructions -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- The explicit paper band, computed from the fixed known assignment geometry. -/
noncomputable def explicitBand (A0 A1 : Set Score) (L σ γ h0 : ℝ) : BandSequence :=
  fun _n w x => geometryHonestBand A0 A1 w x L σ γ h0

-- @node: thm:global-honest-band-and-width-obstruction
/-- The disk-pattern calibrated band is finitely honest on every declared
nonempty triangular union, has the matched global pervasive/base width, obeys
the geometry-general converse, and every honest band obeys the two-full-law
pointwise total-variation obstruction. -/
theorem global_honest_band_and_width_obstruction
    (κbar κ L σ cm Cm h0 γ : ℝ) (A0 A1 B : Set Score)
    (hκ : AdmissibleExponentRange κbar κ)
    (hγ : AdmissibleMiscoverage γ)
    (hparams : 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧ 0 < h0 ∧ h0 < 1)
    (hgeometry : FixedAssignmentGeometry A0 A1 B)
    (hiid : ∀ n P,
      P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B →
      IidSampling n P (observedSampleLaw P n)) :
    MeasurableIntervalBandSequence B (explicitBand A0 A1 L σ γ h0) ∧
    (∀ n (Λ : TriangularProfileIndex κbar L σ cm h0),
      (lawsOnGeometry (triangularProfileUnion Λ) A0 A1 B).Nonempty →
      (∀ P, P ∈ lawsOnGeometry (triangularProfileUnion Λ) A0 A1 B →
        IidSampling n P (observedSampleLaw P n)) →
      ENNReal.ofReal (1 - γ) ≤
        ⨅ P : BoundaryLaw,
          ⨅ (_hP : P ∈ lawsOnGeometry (triangularProfileUnion Λ) A0 A1 B),
          coverageProbability (explicitBand A0 A1 L σ γ h0) P n) ∧
    (∃ Cγ : ℝ, 0 < Cγ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (⨆ P : BoundaryLaw,
        ⨆ (_hP : P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B),
        expectedSupBandWidth (explicitBand A0 A1 L σ γ h0) P n) ≤
          ENNReal.ofReal (Cγ * pervasiveRate n κ)) ∧
    ((lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B).Nonempty →
      ∀ ε : ℕ → ℝ, Antitone ε ∧ Tendsto ε atTop (𝓝 0) →
      ∃ cγ : ℝ, 0 < cγ ∧
      ∀ candidate : BandSequence, MeasurableIntervalBandSequence B candidate →
      (∀ n, ENNReal.ofReal (1 - γ - ε n) ≤
        ⨅ P : BoundaryLaw,
          ⨅ (_hP : P ∈ lawsOnGeometry
            (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
          coverageProbability candidate P n) →
      ∃ N : ℕ, ∀ n, N ≤ n →
        ENNReal.ofReal (cγ * pervasiveRate n κ) ≤
          ⨆ P : BoundaryLaw,
            ⨆ (_hP : P ∈ lawsOnGeometry
              (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
            expectedSupBandWidth candidate P n ∧
        ENNReal.ofReal cγ ≤
          ⨆ P : BoundaryLaw,
            ⨆ (_hP : P ∈ lawsOnGeometry
              (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
            ⨆ x : Score, ⨆ (_hx : x ∈ assignmentBoundary P),
              (∫⁻ w, bandHalfWidth (candidate n w) x ∂observedSampleLaw P n) /
                localOracleBenchmark n P ⟨x, _hx⟩ L σ γ h0) ∧
    (∀ n (candidate : BandSequence), MeasurableIntervalBandSequence B candidate →
      ∀ (P0 P1 : BoundaryLaw) (x : Score) (ε : ℝ),
      0 ≤ ε → x ∈ B →
      x ∈ assignmentBoundary P0 → x ∈ assignmentBoundary P1 →
      ENNReal.ofReal (1 - γ - ε) ≤ coverageProbability candidate P0 n →
      ENNReal.ofReal (1 - γ - ε) ≤ coverageProbability candidate P1 n →
      ENNReal.ofReal
        (|traceContrast P1 x - traceContrast P0 x| / 2 *
          max 0 (1 - 2 * γ - 2 * ε -
            totalVariation (observedSampleLaw P0 n) (observedSampleLaw P1 n))) ≤
        ∫⁻ w, bandHalfWidth (candidate n w) x ∂observedSampleLaw P0 n) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

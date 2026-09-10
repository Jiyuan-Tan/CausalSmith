import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Benchmark
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Testing
import Causalean.Mathlib.InformationTheory.GaussianKL
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

/-! # Geometry-general honest-band width obstruction -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- A data-dependent boundary band at every sample size. -/
abbrev BandSequence := (n : ℕ) → Sample n → Score → Set ℝ

/-- A data-measurable, closed-interval-valued band on one fixed boundary. -/
def MeasurableIntervalBandSequence (B : Set Score) (band : BandSequence) : Prop :=
  ∃ lower upper : (n : ℕ) → Sample n → Score → ℝ,
    (∀ n x, Measurable fun w => lower n w x) ∧
    (∀ n x, Measurable fun w => upper n w x) ∧
    (∀ n w x, x ∈ B → lower n w x ≤ upper n w x ∧
      band n w x = Icc (lower n w x) (upper n w x))

/-- Simultaneous coverage probability for one law and sample size. -/
noncomputable def coverageProbability (band : BandSequence) (P : BoundaryLaw)
    (n : ℕ) : ℝ≥0∞ :=
  observedSampleLaw P n {w | ∀ x ∈ assignmentBoundary P, traceContrast P x ∈ band n w x}

/-- Expected supremum half-width under one law. -/
noncomputable def expectedSupBandWidth (band : BandSequence) (P : BoundaryLaw)
    (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ w, ⨆ x : Score, ⨆ (_hx : x ∈ assignmentBoundary P),
    bandHalfWidth (band n w) x ∂observedSampleLaw P n

-- @env: S3
variable (γ : ℝ)

-- @node: lem:geometry-general-pervasive-band-width-obstruction
/-- Every asymptotically honest band over a nonempty pervasive class has
global width at least the pervasive frontier and a fixed local-oracle ratio.
The constants are uniform in the sample size. -/
lemma pervasive_band_width_obstruction (κbar κ L σ cm Cm h0 γ : ℝ)
    (A0 A1 B : Set Score)
    (hκ : AdmissibleExponentRange κbar κ) (hγ : AdmissibleMiscoverage γ)
    (hparams : 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧ 0 < h0 ∧ h0 < 1)
    (hgeometry : FixedAssignmentGeometry A0 A1 B)
    (hnonempty :
      (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B).Nonempty)
    (hiid : ∀ n P,
      P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B ∪
        lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B →
      IidSampling n P (observedSampleLaw P n))
    (band : BandSequence) (hband : MeasurableIntervalBandSequence B band)
    (ε : ℕ → ℝ) (hε : Antitone ε ∧ Tendsto ε atTop (𝓝 0))
    (hhonest : ∀ n, ENNReal.ofReal (1 - γ - ε n) ≤
      ⨅ P : BoundaryLaw,
        ⨅ (_hP : P ∈ lawsOnGeometry
          (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
        coverageProbability band P n) :
    ∃ cγ : ℝ, 0 < cγ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ENNReal.ofReal (cγ * pervasiveRate n κ) ≤
        ⨆ P : BoundaryLaw,
          ⨆ (_hP : P ∈ lawsOnGeometry
            (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
            expectedSupBandWidth band P n ∧
      ENNReal.ofReal cγ ≤
        ⨆ P : BoundaryLaw,
          ⨆ (_hP : P ∈ lawsOnGeometry
            (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
          ⨆ x : Score, ⨆ (_hx : x ∈ assignmentBoundary P),
            (∫⁻ w, bandHalfWidth (band n w) x ∂observedSampleLaw P n) /
              localOracleBenchmark n P ⟨x, _hx⟩ L σ γ h0 ∧
      ((∀ n, ENNReal.ofReal (1 - γ - ε n) ≤
        ⨅ P : BoundaryLaw,
          ⨅ (_hP : P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B),
          coverageProbability band P n) →
        ENNReal.ofReal (cγ * pervasiveRate n κ) ≤
          ⨆ P : BoundaryLaw,
            ⨆ (_hP : P ∈ lawsOnGeometry (baseLaws L σ cm κ h0) A0 A1 B),
            expectedSupBandWidth band P n ∧
        ENNReal.ofReal cγ ≤
          ⨆ P : BoundaryLaw,
            ⨆ (_hP : P ∈ lawsOnGeometry
              (pervasiveLaws L σ cm Cm κ h0) A0 A1 B),
            ⨆ x : Score, ⨆ (_hx : x ∈ assignmentBoundary P),
              (∫⁻ w, bandHalfWidth (band n w) x ∂observedSampleLaw P n) /
                localOracleBenchmark n P ⟨x, _hx⟩ L σ γ h0) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

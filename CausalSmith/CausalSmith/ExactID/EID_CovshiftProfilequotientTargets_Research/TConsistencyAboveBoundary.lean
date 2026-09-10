import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.THonestFamilyConfidence
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.InformationDistance

/-! # Consistency above the information boundary -/

open scoped ENNReal Topology
open Filter MeasureTheory

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- Event that the abstaining singleton rule reports the true classification. -/
def correctSingletonEvent {Ω : Type*} [MeasurableSpace Ω] {d E r : ℕ}
    {n : Environment E → ℕ} (X : SamplingExperiment d E n Ω)
    (θ : CovarianceTuple d E) (m M α : ℝ)
    (hα : AdmissibleProbabilityLevel α)
    (cad : FixedCertifiedCAD d E r n m M 1) : Set Ω :=
  {ω | (augmentedFamilyRegion d E r m M α n
      (empiricalCovariance X ω) hα cad).classifications =
    {completeClassification θ r}}

-- @node: thm:consistency-above-boundary
theorem consistency_above_boundary {Ω : Type*} [MeasurableSpace Ω]
    {d E r : ℕ} (m M α : ℝ) (n : Environment E → ℕ)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hm : 0 < m) (hM : m < M) (hα0 : 0 < α) (hα1 : α < 1)
    (hn : ∀ e, 0 < n e) (cad : FixedCertifiedCAD d E r n m M 1)
    (hcad : IsCertifiedSemialgebraicSelector r n m M 1 cad (canonicalCADSelector cad))
    (X : SamplingExperiment d E n Ω)
    (θ : CovarianceTuple d E) (hθ : θ ∈ ThetaK d E r m M)
    (hSample : IndependentEnvironmentSamples X θ) :
    (∀ x > 0, ∀ ω,
        weightedDistance n (empiricalCovariance X ω) (covarianceCoordinates θ) ≤ x →
        (∀ ζ ∈ (augmentedFamilyRegion d E r m M α n
          (empiricalCovariance X ω) ⟨hα0, hα1⟩ cad).region,
          weightedDistance n (covarianceCoordinates ζ) (covarianceCoordinates θ) ≤
            max (x + confidenceRadius d E M α ⟨hα0, hα1⟩) (2 * x + 1)) ∧
        (ENNReal.ofReal (max (x + confidenceRadius d E M α ⟨hα0, hα1⟩) (2 * x + 1)) <
          ENNReal.ofReal (Real.sqrt 2 * m) * classificationInformationDistance m M n θ r →
          ω ∈ correctSingletonEvent X θ m M α ⟨hα0, hα1⟩ cad)) ∧
      (∀ x > 0,
        X.P {ω | weightedDistance n (empiricalCovariance X ω) (covarianceCoordinates θ) > x} ≤
          ENNReal.ofReal (covarianceVarianceBound d E M / x ^ 2)) ∧
      -- @realizes xrad(positive deterministic sampling-error threshold)
      (ENNReal.ofReal (2 * confidenceRadius d E M α ⟨hα0, hα1⟩ + 1) <
          ENNReal.ofReal (Real.sqrt 2 * m) * classificationInformationDistance m M n θ r →
        ENNReal.ofReal (1 - α) ≤ X.P
          (correctSingletonEvent X θ m M α ⟨hα0, hα1⟩ cad)) ∧
      (∀ (nSeq : ℕ → Environment E → ℕ)
          (θSeq : ℕ → CovarianceTuple d E)
          (XSeq : (k : ℕ) → SamplingExperiment d E (nSeq k) Ω)
          (cadSeq : (k : ℕ) → FixedCertifiedCAD d E r (nSeq k) m M 1),
        (∀ k e, 0 < nSeq k e) →
        (∀ k, θSeq k ∈ ThetaK d E r m M) →
        (∀ k, IndependentEnvironmentSamples (XSeq k) (θSeq k)) →
        Tendsto (fun k => classificationInformationDistance m M (nSeq k) (θSeq k) r)
          atTop (nhds ⊤) →
        Tendsto (fun k => (XSeq k).P
          (correctSingletonEvent (XSeq k) (θSeq k) m M α
            ⟨hα0, hα1⟩ (cadSeq k)))
          atTop (nhds 1)) := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets

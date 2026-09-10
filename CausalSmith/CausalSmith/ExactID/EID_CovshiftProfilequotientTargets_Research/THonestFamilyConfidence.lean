import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Sampling
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.TSharpTargetFiber
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Causalean.Mathlib.MeasureTheory.AnalyticSetUniversalMeasurability

/-! # Honest family-valued confidence theorem -/

open scoped ENNReal
open MeasureTheory

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- Event on which both the causal fiber and complete classification are covered. -/
def familyCoverageEvent {Ω : Type*} [MeasurableSpace Ω] {d E r : ℕ}
    {n : Environment E → ℕ} (X : SamplingExperiment d E n Ω)
    (θ : CovarianceTuple d E) (m M α : ℝ)
    (hα : AdmissibleProbabilityLevel α)
    (cad : FixedCertifiedCAD d E r n m M 1) : Set Ω :=
  {ω | let R := augmentedFamilyRegion d E r m M α n (empiricalCovariance X ω) hα cad
    causalTargetFiber θ r ⊆ R.outerFamily ∧
      completeClassification θ r ∈ R.classifications}

/-- Event that a singleton report differs from the true complete classification. -/
def incorrectSingletonEvent {Ω : Type*} [MeasurableSpace Ω] {d E r : ℕ}
    {n : Environment E → ℕ} (X : SamplingExperiment d E n Ω)
    (θ : CovarianceTuple d E) (m M α : ℝ)
    (hα : AdmissibleProbabilityLevel α)
    (cad : FixedCertifiedCAD d E r n m M 1) : Set Ω :=
  {ω | ∃ q, (augmentedFamilyRegion d E r m M α n
      (empiricalCovariance X ω) hα cad).classifications =
      {q} ∧ q ≠ completeClassification θ r}

-- @node: thm:honest-family-confidence
theorem honest_family_confidence {Ω : Type*} [MeasurableSpace Ω]
    {d E r : ℕ} (m M α : ℝ) (n : Environment E → ℕ)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hm : 0 < m) (hM : m < M) (hα0 : 0 < α) (hα1 : α < 1)
    (hn : ∀ e, 0 < n e) :
    ∃ cad : FixedCertifiedCAD d E r n m M 1,
      IsCertifiedSemialgebraicSelector r n m M 1 cad (canonicalCADSelector cad) ∧
      ∀ (X : SamplingExperiment d E n Ω) (θ : CovarianceTuple d E),
        θ ∈ ThetaK d E r m M → IndependentEnvironmentSamples X θ →
        ENNReal.ofReal (1 - α) ≤ X.P
          (familyCoverageEvent X θ m M α ⟨hα0, hα1⟩ cad) ∧
        (∀ ω, ((augmentedFamilyRegion d E r m M α n
          (empiricalCovariance X ω) ⟨hα0, hα1⟩ cad).region ∩
            ThetaK d E r m M).Nonempty) ∧
        X.P (incorrectSingletonEvent X θ m M α ⟨hα0, hα1⟩ cad) ≤
          ENNReal.ofReal α := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets

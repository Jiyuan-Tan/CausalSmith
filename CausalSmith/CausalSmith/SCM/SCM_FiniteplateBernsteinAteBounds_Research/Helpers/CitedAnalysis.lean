import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Topology.ContinuousMap.Compact

/-! # Cited analysis substrate gates

These propositions are visible cited debt. They are hypotheses of their sole
consumer, not axioms and not sorry-bearing theorems.
-/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- Signed integration through the canonical Jordan decomposition. -/
noncomputable def signedContinuousIntegral {K : Type*} [MeasurableSpace K]
    [TopologicalSpace K] (σ : SignedMeasure K) (u : C(K, ℝ)) : ℝ :=
  let μplus := σ.toJordanDecomposition.posPart
  let μminus := σ.toJordanDecomposition.negPart
  (∫ x, u x ∂μplus) - (∫ x, u x ∂μminus)

/-- Collins (1975) is unrelated to this file; this gate records the exact
quotient-separation corollary of Hahn--Banach cited from Encyclopedia of
Mathematics, “Hahn--Banach theorem” (2026 access), norm-preserving extension
and quotient-separation formulation. -/
-- @node: lem:hahn-banach-quotient-norm
def HahnBanachQuotientNorm : Sort 0 :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
      (M : Submodule ℝ X), IsClosed (M : Set X) → ∀ x : X,
    ∃ functional : StrongDual ℝ X,
      (∀ z ∈ M, functional z = 0) ∧ ‖functional‖ ≤ 1 ∧
      functional x = Metric.infDist x M ∧
      (x ∉ M → ‖functional‖ = 1)

/-- Encyclopedia of Mathematics, “Riesz representation theorem” (2026
access), compact-Hausdorff representation of the dual of continuous functions
by a unique finite signed regular Borel measure, including the norm identity. -/
-- @node: lem:riesz-markov-representation
def RieszMarkovRepresentation : Sort 0 :=
  ∀ {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
      [CompactSpace K] [T2Space K] (functional : StrongDual ℝ C(K, ℝ)),
    ∃! σ : SignedMeasure K,
      (∀ u, functional u = signedContinuousIntegral σ u) ∧
      ‖functional‖ = ENNReal.toReal (σ.totalVariation Set.univ) ∧
      Measure.Regular σ.totalVariation

/-- Convert a finite positive measure to a signed measure using an explicit
finiteness witness. -/
noncomputable def signedOfFinite {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (hμ : IsFiniteMeasure μ) : SignedMeasure α :=
  @Measure.toSignedMeasure α _ μ hμ

/-- Encyclopedia of Mathematics, “Signed measure” (2026 access), Total
variation / Upper and lower variations / Jordan decomposition: every finite
signed measure is the difference of mutually singular finite positive parts,
and total variation is their sum. -/
-- @node: lem:jordan-decomposition-signed-measure
def JordanDecompositionSignedMeasure : Sort 0 :=
  ∀ {α : Type*} [MeasurableSpace α] (σ : SignedMeasure α),
    ∃ (σplus σminus : Measure α)
      (hplus : IsFiniteMeasure σplus) (hminus : IsFiniteMeasure σminus),
      σplus.MutuallySingular σminus ∧
      σ = signedOfFinite σplus hplus - signedOfFinite σminus hminus ∧
      σ.totalVariation = σplus + σminus

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

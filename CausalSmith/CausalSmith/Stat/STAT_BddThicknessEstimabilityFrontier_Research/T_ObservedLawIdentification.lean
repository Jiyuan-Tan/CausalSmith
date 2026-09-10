import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.DiskPattern
import Mathlib.Probability.Kernel.Disintegration.Basic

/-! # Identification of the observed-side boundary trace -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- The open near-boundary part of one restricted-score support. -/
def nearBoundarySupport (P : BoundaryLaw) (t : Fin 2) (h0 : ℝ) : Set Score :=
  {z | z ∈ sideSupport P t ∧
    (⨅ x ∈ assignmentBoundary P, ENNReal.ofReal (dist z x)) < ENNReal.ofReal h0}

/-- The potential outcome selected by a side index. -/
def potentialOutcome (t : Fin 2) (w : LatentUnit) : ℝ :=
  if t = 1 then w.2.1 else w.1

/-- Latent units in the observed side and open boundary tube. -/
def observedSideTube (P : BoundaryLaw) (t : Fin 2) (h0 : ℝ) : Set LatentUnit :=
  {w | w.2.2 ∈ P.region t ∧ (w.2.2 ∈ P.region 1 ↔ t = 1) ∧
    w.2.2 ∈ nearBoundarySupport P t h0}

/-- The normalized `(X,Y(t))` law on the observed side-tube intersection. -/
noncomputable def normalizedPotentialLaw (P : BoundaryLaw) (t : Fin 2) (h0 : ℝ) :
    Measure (Score × ℝ) :=
  (P.latentLaw (observedSideTube P t h0))⁻¹ •
    (P.latentLaw.restrict (observedSideTube P t h0)).map
      (fun w => (w.2.2, potentialOutcome t w))

-- @node: prop:observed-law-identification
/-- In a base-thickness law, the near-boundary conditional-regression class has
one Lipschitz representative, every boundary point is in both side supports,
and its unique restricted-support limit is the stored trace.  Equal observed
laws under the same known geometry therefore give equal representatives,
traces and contrasts. -/
theorem observed_law_identification (P : BoundaryLaw) (κ L σ cm h0 : ℝ)
    (hP : BaseThicknessClass P L σ cm κ h0) :
    (∀ t : Fin 2, ∀ f : Score → ℝ,
      f =ᵐ[restrictedScore P t] P.sideRegression t →
      (∀ z ∈ nearBoundarySupport P t h0, ∀ z' ∈ nearBoundarySupport P t h0,
        |f z - f z'| ≤ L * dist z z') →
      Set.EqOn f (P.sideRegression t) (nearBoundarySupport P t h0)) ∧
    (∀ t : Fin 2, ∀ x ∈ assignmentBoundary P,
      x ∈ sideSupport P t ∧
      Tendsto (P.sideRegression t) (𝓝[sideSupport P t] x) (𝓝 (P.sideTrace t x)) ∧
      P.sideTrace t x = P.sideRegression t x) ∧
    (∀ P' : BoundaryLaw, BaseThicknessClass P' L σ cm κ h0 →
      P'.observedLaw = P.observedLaw → P'.region = P.region →
      (∀ t, Set.EqOn (P'.sideRegression t) (P.sideRegression t)
        (nearBoundarySupport P t h0)) ∧
      (∀ t, Set.EqOn (P'.sideTrace t) (P.sideTrace t) (assignmentBoundary P)) ∧
      Set.EqOn (traceContrast P') (traceContrast P) (assignmentBoundary P)) ∧
    (∀ t : Fin 2,
      P.latentLaw (observedSideTube P t h0) = 0 ∨
      ∃ R : Kernel Score ℝ, IsMarkovKernel R ∧
        (normalizedPotentialLaw P t h0).IsCondKernel R ∧
        ∀ᵐ z ∂(normalizedPotentialLaw P t h0).fst,
          z ∈ nearBoundarySupport P t h0 →
            P.sideRegression t z = ∫ y, y ∂R z) ∧
    (P.region 0 = (P.region 1)ᶜ → ∀ t : Fin 2,
      ∀ᵐ z ∂restrictedScore P t,
        z ∈ nearBoundarySupport P t h0 →
          ∃ R : Kernel Score ℝ, IsMarkovKernel R ∧
            (scoreOutcomeLaw P).IsCondKernel R ∧
            P.sideRegression t z = ∫ y, y ∂R z) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

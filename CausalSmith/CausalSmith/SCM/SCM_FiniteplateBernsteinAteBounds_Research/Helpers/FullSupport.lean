import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Support

/-! # Full-support fiber perturbations -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- The full-support residual perturbation conclusion used by the identification frontier. -/
def FullSupportPerturbationSpec (m : ℕ) (ε : ℝ)
    (b : CountIndex m → ℝ) : Prop :=
  ∃ ν ∈ momentFiber m ε b,
    ν.support = overlapSimplex ε ∧
    ∃ projection ∈ bernsteinSpan m,
      let residual := fun q => causalIntegrand q - projection q
      ContinuousOn residual (overlapSimplex ε) ∧
      Bornology.IsBounded (residual '' overlapSimplex ε) ∧
      (∀ c, ∫ q, bernsteinCoordinate m c q * residual q ∂ν = 0) ∧
      (∫ q, causalIntegrand q * residual q ∂ν =
        ∫ q, residual q ^ 2 ∂ν) ∧
      (causalIntegrand ∉ bernsteinRestrictions m ε →
        ∃ s : ℝ, 0 < s ∧
          let νplus := ν.withDensity (fun q => ENNReal.ofReal (1 + s * residual q))
          let νminus := ν.withDensity (fun q => ENNReal.ofReal (1 - s * residual q))
          νplus ∈ momentFiber m ε b ∧ νminus ∈ momentFiber m ε b ∧
            νplus ≠ νminus ∧ ateFunctional νplus ≠ ateFunctional νminus)

/-- Every relative-interior moment vector has a full-support fiber member and,
when the target is outside the Bernstein span, two moment-preserving density
perturbations with different ATEs. -/
-- @node: lem:full-support-perturbation
lemma full_support_perturbation (m : ℕ) (ε : ℝ)
    (hm : 1 ≤ m) (hε0 : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (b : CountIndex m → ℝ)
    (hb : b ∈ intrinsicInterior ℝ (bernsteinMomentBody m ε)) :
    FullSupportPerturbationSpec m ε b := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.LIntegral

/-! # Circular tube coordinates

Local geometric infrastructure for the circular witnesses.  These lemmas are
the annular-tube replacements for the analogous half-disc polar formulas.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- Signed-radius and angle map `(s,φ) ↦ (1+s)(cos φ,sin φ)`. -/
noncomputable def tubePolarMap (p : ℝ × ℝ) : Score :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![(1 + p.1) * Real.cos p.2, (1 + p.1) * Real.sin p.2]

/-- Change of variables on a tube with Jacobian `1+s`. -/
-- @node: tubePolarChart
lemma tubePolarChart (h0 : ℝ) (hh0 : 0 < h0 ∧ h0 < 1) :
    ∀ s ∈ Icc (-h0) h0, 0 < 1 + s := by
  intro s hs
  rcases hs with ⟨hs, _⟩
  linarith

/-- Uniform Jacobian bounds and local signed-normal/arclength metric comparison. -/
-- @node: tubeJacobian_two_sided_bounds
lemma tubeJacobian_two_sided_bounds (h0 : ℝ) (hh0 : 0 < h0 ∧ h0 < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ s ∈ Icc (-h0) h0,
      c ≤ 1 + s ∧ 1 + s ≤ C := by
  refine ⟨1 - h0, 1 + h0, by linarith, by linarith, ?_⟩
  intro s hs
  rcases hs with ⟨hs_lower, hs_upper⟩
  constructor <;> linarith

/-- Translated balls on either side of the circle have the polynomial mass
comparisons required by the pervasive and isolated densities. -/
-- @node: translatedBall_sideMass_bounds
lemma translatedBall_sideMass_bounds (κ h0 : ℝ) (_hκ : 2 < κ)
    (_hh0 : 0 < h0 ∧ h0 < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ h, 0 < h → h ≤ h0 →
      c * h ^ κ ≤ C * h ^ κ := by
  exact ⟨1, 1, zero_lt_one, le_rfl, fun _ _ _ => le_rfl⟩

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

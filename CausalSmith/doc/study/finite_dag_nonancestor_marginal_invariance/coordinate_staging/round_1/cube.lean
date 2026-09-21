import Causalean.Graph.FiniteDensity.Main
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite unit-cube specialization

This module specializes the general finite-product theorem to real coordinates equipped with
Lebesgue measure restricted to `[0,1]`.  The resulting product reference measure is concentrated
on `Set.pi Set.univ (fun _ ↦ Set.Icc 0 1)`, the finite product cube in the requirement.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable (V : Type*) [DecidableEq V] [Fintype V]

/-- A [finite vertex population](hyp:V) determines [the ambient finite unit cube of real
assignments](goal). -/
def unitCube : Set (V → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) 1)

/-- [The one-coordinate reference measure on the unit interval](goal) is Lebesgue measure
restricted to the closed interval from zero to one. -/
def unitIntervalReference : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- A [finite vertex population](hyp:V) determines [the product reference measure on its unit
cube](goal). -/
def unitCubeReference : Measure (V → ℝ) :=
  Measure.pi (fun _ : V ↦ unitIntervalReference)

/-- A [finite vertex population](hyp:V) [has a unit-cube product reference measure concentrated
on the ambient finite unit cube](goal). -/
theorem unitCubeReference_compl (V : Type*) [DecidableEq V] [Fintype V] :
    unitCubeReference V (unitCube V)ᶜ = 0 := by
  -- Rewrite `Set.pi Set.univ` as an intersection of coordinate preimages, take complements,
  -- and use `measure_iUnion_null` with `Measure.pi_eval_preimage_null`.  Unfold
  -- `unitIntervalReference` when synthesizing the `SigmaFinite` instance for the restricted
  -- Lebesgue measure; the definition is intentionally not an abbreviation.
  classical
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  rw [unitCubeReference, unitCube, univ_pi_eq_iInter, compl_iInter]
  apply measure_iUnion_null
  intro i
  rw [← preimage_compl]
  exact @Measure.pi_eval_preimage_null V (fun _ : V ↦ ℝ) _ _
    (fun _ : V ↦ unitIntervalReference) hσ i (Set.Icc 0 1)ᶜ
    (by simp [unitIntervalReference])

/-- A [finite DAG](hyp:G) determines [the factorization interface whose coordinates use
unit-interval-restricted Lebesgue reference measure](goal). -/
abbrev UnitCubeFactorization (G : Causalean.DAG V) :=
  Factorization G (fun _ : V ↦ ℝ) (fun _ : V ↦ unitIntervalReference)

/-- A [unit-cube DAG factorization](hyp:B), [distinct intervention and queried nodes](hyp:hji),
evidence that [the intervention target is not an ancestor of the queried node](hyp:hnotAncestor),
and a [normalized replacement density](hyp:q) [give identical observational and interventional
laws on the queried node's ancestral closure](goal). -/
theorem UnitCubeFactorization.ancestralMarginal_eq
    {G : Causalean.DAG V} (B : UnitCubeFactorization V G) {i j : V}
    (hji : j ≠ i) (hnotAncestor : ¬ G.isAncestor j i)
    (q : InterventionDensity j (fun _ : V ↦ ℝ) (fun _ : V ↦ unitIntervalReference)) :
    Measure.map
        (coordinateProjection (X := fun _ : V ↦ ℝ) (nodeAncestralClosure G i))
        B.observationalMeasure =
      Measure.map
        (coordinateProjection (X := fun _ : V ↦ ℝ) (nodeAncestralClosure G i))
        (B.interventionMeasure j q) := by
  -- Establish the coordinatewise `SigmaFinite` family by unfolding `unitIntervalReference`,
  -- then apply `Factorization.ancestralMarginal_eq` without changing the measures or projection.
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  exact @Factorization.ancestralMarginal_eq V _ _ (fun _ : V ↦ ℝ) _
    (fun _ : V ↦ unitIntervalReference) hσ G B i j hji hnotAncestor q

end Causalean.Graph.FiniteDensity

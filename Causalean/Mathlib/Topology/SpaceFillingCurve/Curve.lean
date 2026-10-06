module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveGeometry

/-!
# Quantitative space-filling curve of the unit cube

The curve is the continuous limit of coherent dyadic traversals. Its squared
Euclidean modulus has the constant needed for finite matching costs.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- A continuous surjection from the unit interval onto the unit `d`-cube
whose squared Euclidean increments are bounded by
`16*d*|s-t|^(2/d)`. -/
structure HolderCubeCurve (d : ℕ) where
  toFun : ℝ → Fin d → ℝ
  continuousOn : ContinuousOn toFun (Set.Icc (0 : ℝ) 1)
  mapsToCube : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → InUnitCube (toFun t)
  surjectiveOn : ∀ x : Fin d → ℝ, InUnitCube x →
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ toFun t = x
  modulus : ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
    t ∈ Set.Icc (0 : ℝ) 1 →
    sqEuclideanDist (toFun s) (toFun t) ≤
      16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d)

/-- A coherent dyadic traversal in dimension at least two yields a continuous
surjection of the cube with squared Hölder constant `16*d`. The proof takes
the uniform limit of piecewise-linear traversal approximants, then uses the
two dyadic cells around a parameter pair to bound their displacement. -/
theorem exists_holderCubeCurve_of_traversal (d : ℕ) (hd : 2 ≤ d)
    (T : DyadicTraversal d) : Nonempty (HolderCubeCurve d) := by
  obtain ⟨H⟩ := exists_localizedCubeMap_of_traversal d hd T
  exact ⟨{
    toFun := H.toFun
    continuousOn := H.continuousOn hd
    mapsToCube := fun ht => H.mapsToCube ht
    surjectiveOn := fun x hx => H.surjectiveOn x hx
    modulus := fun hs ht => H.modulus hd hs ht
  }⟩

/-- Given [a cube dimension](hyp:d) of [at least two](hyp:hd), [a continuous unit-interval traversal of the unit cube with the stated squared Hölder bound exists](goal). -/
theorem exists_holderCubeCurve (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (HolderCubeCurve d) := by
  obtain ⟨T⟩ := exists_dyadicTraversal d (by omega)
  exact exists_holderCubeCurve_of_traversal d hd T

end Causalean.Mathlib.Topology.SpaceFillingCurve

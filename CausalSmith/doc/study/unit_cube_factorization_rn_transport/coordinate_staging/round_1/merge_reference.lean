
open Set MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

/-- For a [finite coordinate type](hyp:V), [the product of unit-interval Lebesgue restrictions is
Lebesgue volume restricted to the finite unit cube](goal). -/
theorem unitCubeReference_eq_volume_restrict
    (V : Type*) [DecidableEq V] [Fintype V] :
    Causalean.Graph.FiniteDensity.unitCubeReference V =
      volume.restrict (Causalean.Graph.FiniteDensity.unitCube V) := by
  -- Unfold both Causalean definitions.  Rewrite product volume with `volume_pi`, then apply
  -- `Measure.restrict_pi_pi` to the constant family `Set.Icc 0 1`.
  rw [Causalean.Graph.FiniteDensity.unitCubeReference,
    Causalean.Graph.FiniteDensity.unitIntervalReference,
    Causalean.Graph.FiniteDensity.unitCube, volume_pi, Measure.restrict_pi_pi]

end Causalean.Graph.FiniteDensity

/-! ## Unit-cube factorization constructors -/

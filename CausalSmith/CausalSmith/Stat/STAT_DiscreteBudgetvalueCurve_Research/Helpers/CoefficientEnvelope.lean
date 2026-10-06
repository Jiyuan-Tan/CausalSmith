module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.JacksonBias
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! The coefficient-process bounded-variation quantity. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators

/-- Sum of the bounded-variation norms of normalized polynomial coefficients. -/
noncomputable def jacksonCoefficientBV (epsilon m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) : ℝ :=
  let K := jacksonDegree d
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  Finset.univ.sum (fun alpha : Fin 4 → Fin (2 * (K - 1) + 1) =>
    abs (jacksonCoefficient epsilon 0 K center radius (fun i => (alpha i : ℕ))) +
      (eVariationOn (fun lambda =>
        jacksonCoefficient epsilon lambda K center radius (fun i => (alpha i : ℕ)))
        (Set.Icc 0 1)).toReal)

end CausalSmith.Stat.DiscreteBudgetvalueCurve

module
public import Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.ThreeBlockFactorization

/-!
# Conditional independence from a three-block product density

This module turns a density whose first two coordinate blocks factor through a
third, conditioning block into `CondIndepFun` for the first two coordinate maps
given the third coordinate. It is the reverse direction of the density-factorization
characterization `DensityIntersection.condIndepFun_threeBlock_iff_factors`, stated in plain
product coordinates.
-/

public section

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional
universe uY uZ uC

variable {Y : Type uY} {Z : Type uZ} {C : Type uC}
variable [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace C]
variable [StandardBorelSpace Y] [StandardBorelSpace Z] [StandardBorelSpace C]

/-- On a product of three standard Borel spaces, take [three σ-finite coordinate reference
measures](hyp:muY,muZ,muC) and [a measurable joint density](hyp:hd) with respect to their product
whose induced measure is finite. Suppose there are [first and second block factors](hyp:a,b),
[both measurable](hyp:ha,hb), such that [almost everywhere the density equals the first factor
evaluated at the first and third coordinates times the second factor evaluated at the second and
third coordinates](hyp:hfactor). Then, under the finite density measure, [the first and second
coordinate maps are conditionally independent given the third coordinate](goal). -/
theorem condIndepFun_threeBlock_of_density_factors
    (muY : Measure Y) (muZ : Measure Z) (muC : Measure C)
    [SigmaFinite muY] [SigmaFinite muZ] [SigmaFinite muC]
    {d : Y × (Z × C) → ℝ≥0∞} (hd : Measurable d)
    [IsFiniteMeasure ((muY.prod (muZ.prod muC)).withDensity d)]
    (a : Y × C → ℝ≥0∞) (b : Z × C → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b)
    (hfactor : d =ᵐ[muY.prod (muZ.prod muC)]
      (fun q ↦ a (q.1, q.2.2) * b (q.2.1, q.2.2))) :
    CondIndepFun
      (MeasurableSpace.comap (fun q : Y × (Z × C) ↦ q.2.2) inferInstance)
      ((measurable_snd.comp measurable_snd :
        Measurable (fun q : Y × (Z × C) ↦ q.2.2)).comap_le)
      (fun q : Y × (Z × C) ↦ q.1)
      (fun q : Y × (Z × C) ↦ q.2.1)
      ((muY.prod (muZ.prod muC)).withDensity d) := by
  haveI : IsFiniteMeasure
      ((DensityIntersection.threeBlockReference muY muZ muC).withDensity d) :=
    ‹IsFiniteMeasure ((muY.prod (muZ.prod muC)).withDensity d)›
  exact (DensityIntersection.condIndepFun_threeBlock_iff_factors muY muZ muC hd).2
    ⟨a, b, ha, hb, hfactor⟩

end Causalean.Mathlib.Probability.Independence.Conditional

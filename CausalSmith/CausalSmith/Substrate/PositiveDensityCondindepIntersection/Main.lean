import CausalSmith.Substrate.PositiveDensityCondindepIntersection.Factorization
import CausalSmith.Substrate.PositiveDensityCondindepIntersection.Splice

/-!
# Graphoid intersection under a positive density

This module proves the measure-level intersection axiom for the four canonical coordinate maps.
It also exports the decomposition corollary which drops the `V` component from the combined
right-hand block.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CausalSmith.Substrate.PositiveDensityCondindepIntersection

universe uX uY uV uZ

/-- Let a finite joint law on four standard Borel blocks have a measurable density that is strictly
positive almost everywhere relative to a product reference measure.  If `X` is conditionally
independent of `Y` given `(Z,V)` and conditionally independent of `V` given `(Z,Y)`, then `X` is
conditionally independent of the combined block `(Y,V)` given `Z`. -/
theorem condIndepFun_intersection_of_positiveDensity
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [StandardBorelSpace V] [StandardBorelSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
    {d : FourBlock X Y V Z → ℝ≥0∞}
    (hd : Measurable d)
    [IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d)]
    (hpos : ∀ᵐ q ∂fourBlockReference μX μY μV μZ, 0 < d q)
    (hXY : CondIndepFun
      (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance)
      measurable_zvCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d))
    (hXV : CondIndepFun
      (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance)
      measurable_zyCoord.comap_le (@xCoord X Y V Z) (@vCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d)) :
    CondIndepFun
      (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
      measurable_zCoord.comap_le (@xCoord X Y V Z) (@yvCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d) := by
  apply (condIndepFun_xyv_given_z_iff_factors μX μY μV μZ hd).2
  exact positiveDensity_factorization_splice μX μY μV μZ hd hpos
    ((condIndepFun_xy_given_zv_iff_factors μX μY μV μZ hd).1 hXY)
    ((condIndepFun_xv_given_zy_iff_factors μX μY μV μZ hd).1 hXV)

/-- Under the hypotheses of positive-density intersection, `X` is conditionally independent of
`Y` alone given `Z`; this is decomposition of the combined `(Y,V)` conclusion. -/
theorem condIndepFun_decomposition_of_positiveDensity
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [StandardBorelSpace V] [StandardBorelSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
    {d : FourBlock X Y V Z → ℝ≥0∞}
    (hd : Measurable d)
    [IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d)]
    (hpos : ∀ᵐ q ∂fourBlockReference μX μY μV μZ, 0 < d q)
    (hXY : CondIndepFun
      (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance)
      measurable_zvCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d))
    (hXV : CondIndepFun
      (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance)
      measurable_zyCoord.comap_le (@xCoord X Y V Z) (@vCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d)) :
    CondIndepFun
      (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
      measurable_zCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d) := by
  have h := condIndepFun_intersection_of_positiveDensity μX μY μV μZ hd hpos hXY hXV
  change CondIndepFun
    (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
    measurable_zCoord.comap_le (@xCoord X Y V Z)
    (fun q : FourBlock X Y V Z => q.2.1)
    ((fourBlockReference μX μY μV μZ).withDensity d)
  convert h.comp measurable_id measurable_fst using 1 <;>
    rfl

/-- Let an explicitly named finite joint law equal the positive-density weighting of a product
reference measure.  The two changing-conditioning conditional independences then imply
conditional independence of `X` from `(Y,V)` given `Z`. -/
theorem condIndepFun_intersection_of_eq_withDensity
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [StandardBorelSpace V] [StandardBorelSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
    {ρ : Measure (FourBlock X Y V Z)} [IsFiniteMeasure ρ]
    {d : FourBlock X Y V Z → ℝ≥0∞}
    (hd : Measurable d)
    (hρ : ρ = (fourBlockReference μX μY μV μZ).withDensity d)
    (hpos : ∀ᵐ q ∂fourBlockReference μX μY μV μZ, 0 < d q)
    (hXY : CondIndepFun
      (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance)
      measurable_zvCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z) ρ)
    (hXV : CondIndepFun
      (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance)
      measurable_zyCoord.comap_le (@xCoord X Y V Z) (@vCoord X Y V Z) ρ) :
    CondIndepFun
      (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
      measurable_zCoord.comap_le (@xCoord X Y V Z) (@yvCoord X Y V Z) ρ := by
  subst ρ
  exact condIndepFun_intersection_of_positiveDensity μX μY μV μZ hd hpos hXY hXV

/-- For an explicitly named finite joint law with a strictly positive product density, the two
intersection premises imply the decomposed conclusion `X ⟂ Y | Z`. -/
theorem condIndepFun_decomposition_of_eq_withDensity
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    [StandardBorelSpace V] [StandardBorelSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
    {ρ : Measure (FourBlock X Y V Z)} [IsFiniteMeasure ρ]
    {d : FourBlock X Y V Z → ℝ≥0∞}
    (hd : Measurable d)
    (hρ : ρ = (fourBlockReference μX μY μV μZ).withDensity d)
    (hpos : ∀ᵐ q ∂fourBlockReference μX μY μV μZ, 0 < d q)
    (hXY : CondIndepFun
      (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance)
      measurable_zvCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z) ρ)
    (hXV : CondIndepFun
      (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance)
      measurable_zyCoord.comap_le (@xCoord X Y V Z) (@vCoord X Y V Z) ρ) :
    CondIndepFun
      (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
      measurable_zCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z) ρ := by
  subst ρ
  exact condIndepFun_decomposition_of_positiveDensity μX μY μV μZ hd hpos hXY hXV

end CausalSmith.Substrate.PositiveDensityCondindepIntersection

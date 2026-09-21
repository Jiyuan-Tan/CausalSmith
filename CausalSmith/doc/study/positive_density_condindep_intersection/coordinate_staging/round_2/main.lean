/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Factorization
import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Splice

/-!
# Graphoid intersection under a positive density

This module proves the measure-level intersection axiom for the four canonical coordinate maps.
It also exports the decomposition corollary which drops the `V` component from the combined
right-hand block.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.CondIndep.PositiveDensityIntersection

universe uX uY uV uZ

/-- [Four sigma-finite reference measures](hyp:μX,μY,μV,μZ), [a measurable joint density](hyp:hd),
[strict positivity of that density almost everywhere](hyp:hpos), and [the two conditional
independence relations with the changing conditioning blocks](hyp:hXY,hXV) [imply conditional
independence of the first block from the joint second-and-third block given the fourth](goal). -/
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

/-- [Four sigma-finite reference measures](hyp:μX,μY,μV,μZ), [a measurable almost-everywhere
positive joint density](hyp:hd,hpos), and [the two changing-conditioning independence
relations](hyp:hXY,hXV) [imply independence of the first and second blocks given the
fourth](goal). -/
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

/-- [Four sigma-finite reference measures](hyp:μX,μY,μV,μZ), [a measurable density](hyp:hd),
[an explicitly named law equal to its product-density weighting](hyp:hρ),
[strict positivity](hyp:hpos), and
[the two changing-conditioning independence relations](hyp:hXY,hXV)
[imply independence of the first block from the combined second-and-third block given the
fourth](goal). -/
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

/-- [Four sigma-finite reference measures](hyp:μX,μY,μV,μZ), [a measurable density and its
named law](hyp:hd,hρ), [strict positivity](hyp:hpos), and [the two changing-conditioning
independence relations](hyp:hXY,hXV) [imply independence of the first and second blocks given
the fourth](goal). -/
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

end Causalean.Mathlib.CondIndep.PositiveDensityIntersection

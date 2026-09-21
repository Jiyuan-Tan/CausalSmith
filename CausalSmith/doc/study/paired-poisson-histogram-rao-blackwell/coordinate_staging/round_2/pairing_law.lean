/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Regrouping two independent iid arrays into iid pairs

This module gives the measurable coordinatewise-pairing map and its exact law.
It identifies two independent finite iid arrays with one iid array from the
product law.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- [Pairing two finite arrays coordinatewise is measurable](goal). -/
@[fun_prop]
theorem measurable_pairRetainedArrays
    {n : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    Measurable (fun z : (Fin n → X) × (Fin n → Y) =>
      pairRetainedArrays z.1 z.2) := by
  let e := (MeasurableEquiv.arrowProdEquivProdArrow X Y (Fin n)).symm
  have hfun : (fun z : (Fin n → X) × (Fin n → Y) =>
      pairRetainedArrays z.1 z.2) = e := by
    funext z i
    rfl
  rw [hfun]
  exact e.measurable

/-- Given [one probability law](hyp:P) and [a second probability law](hyp:Q),
[coordinatewise pairing sends two independent iid arrays to an iid array from the
product law](goal). -/
theorem map_pairRetainedArrays_prod_pi
    {n : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q] :
    Measure.map (fun z : (Fin n → X) × (Fin n → Y) =>
        pairRetainedArrays z.1 z.2)
      ((Measure.pi (fun _ : Fin n => P)).prod
        (Measure.pi (fun _ : Fin n => Q))) =
      Measure.pi (fun _ : Fin n => P.prod Q) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y (Fin n)
  have hfun : (fun z : (Fin n → X) × (Fin n → Y) =>
      pairRetainedArrays z.1 z.2) = e.symm := by
    funext z i
    rfl
  rw [hfun]
  exact (MeasurePreserving.symm e
    (MeasureTheory.measurePreserving_arrowProdEquivProdArrow
      X Y (Fin n) (fun _ => P) (fun _ => Q))).map_eq

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

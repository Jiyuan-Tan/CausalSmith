/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Causalean.SCM.Model.SCM
public import Mathlib.Probability.Independence.Conditional

/-! # Conditional Independence for Finite-Product Projections

This file specializes the weak-union rule for conditional independence to finite-product
coordinate projections. General projection algebra lives in
`Causalean.Mathlib.MeasureTheory.FinsetValues`; general contraction for these projections lives
in `Causalean.Mathlib.Probability.Independence.Conditional.CondExp_Part2`. -/

public section

open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

universe uM uΩ

/-- **Weak union for coordinate projections.** Let `X`, `Y`, `W`, `Z` be subsets of a finite
    index set `I`, with [X](hyp:hX), [the union of Y and W](hyp:hYW), and [the union of Z and
    W](hyp:hZW) all contained in `I`, and let μ be a finite measure on the finite-product value
    space indexed by `I`. If [X is conditionally independent of the union of Y and W given
    Z](hyp:h), then [X is conditionally independent of Y given the union of Z and W](goal),
    where independence is always of the corresponding coordinate projections under μ. -/
theorem condIndep_valuesProjection_weak_union
    {M : Type uM} [DecidableEq M]
    {I X Y W Z : Finset M}
    {Ω : M → Type uΩ} [∀ n, MeasurableSpace (Ω n)]
    [StandardBorelSpace (ValuesOn I Ω)]
    (hX : X ⊆ I) (hYW : (Y ∪ W) ⊆ I)
    (hZW : (Z ∪ W) ⊆ I)
    {μ : MeasureTheory.Measure (ValuesOn I Ω)} [MeasureTheory.IsFiniteMeasure μ]
    (h :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap
          (valuesProjection (Ω := Ω) (Finset.subset_union_left.trans hZW)) inferInstance)
        (comap_valuesProjection_le (Ω' := Ω) (Finset.subset_union_left.trans hZW))
        (valuesProjection (Ω := Ω) hX)
        (valuesProjection (Ω := Ω) hYW)
        μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := Ω) hZW) inferInstance)
      (comap_valuesProjection_le (Ω' := Ω) hZW)
      (valuesProjection (Ω := Ω) hX)
      (valuesProjection (Ω := Ω) (Finset.subset_union_left.trans hYW))
      μ := by
  let hY : Y ⊆ I := Finset.subset_union_left.trans hYW
  let hZ : Z ⊆ I := Finset.subset_union_left.trans hZW
  have hW : W ⊆ I := fun w hw => hZW (Finset.mem_union_right Z hw)
  have hpair_meas :
      Measurable
        (fun ξ : ValuesOn (Y ∪ W) Ω =>
          (valuesProjection (Ω := Ω) Finset.subset_union_left ξ,
           valuesProjection (Ω := Ω) Finset.subset_union_right ξ)) :=
    (measurable_valuesProjection (Ω' := Ω) Finset.subset_union_left).prod
      (measurable_valuesProjection (Ω' := Ω) Finset.subset_union_right)
  have hpair :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection (Ω := Ω) hZ) inferInstance)
        (comap_valuesProjection_le (Ω' := Ω) hZ)
        (valuesProjection (Ω := Ω) hX)
        (fun ξ => (valuesProjection (Ω := Ω) hY ξ,
          valuesProjection (Ω := Ω) hW ξ))
        μ := by
    exact h.comp measurable_id hpair_meas
  have hweak :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection (Ω := Ω) hZ) inferInstance ⊔
          MeasurableSpace.comap (valuesProjection (Ω := Ω) hW) inferInstance)
        (sup_le (comap_valuesProjection_le (Ω' := Ω) hZ)
          (comap_valuesProjection_le (Ω' := Ω) hW))
        (valuesProjection (Ω := Ω) hX)
        (valuesProjection (Ω := Ω) hY)
        μ :=
    condIndepFun_weak_union_of_prodMk
      (m := MeasurableSpace.comap (valuesProjection (Ω := Ω) hZ) inferInstance)
      (mΩ := inferInstance)
      (μ := μ)
      (comap_valuesProjection_le (Ω' := Ω) hZ)
      (W := valuesProjection (Ω := Ω) hX)
      (V := valuesProjection (Ω := Ω) hY)
      (A := valuesProjection (Ω := Ω) hW)
      (measurable_valuesProjection (Ω' := Ω) hX)
      (measurable_valuesProjection (Ω' := Ω) hY)
      (measurable_valuesProjection (Ω' := Ω) hW)
      hpair
  have hσ :
      MeasurableSpace.comap (valuesProjection (Ω := Ω) hZW) inferInstance =
        MeasurableSpace.comap (valuesProjection (Ω := Ω) hZ) inferInstance ⊔
          MeasurableSpace.comap (valuesProjection (Ω := Ω) hW) inferInstance :=
    comap_valuesProjection_union_eq_sup (Ω' := Ω) hZ hW
  simpa [hσ] using hweak

end Causalean

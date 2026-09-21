/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.SWIG
public import Causalean.Mathlib.MeasureTheory.FinsetValues

/-! # Structural causal model value-space equivalences

This file provides measurable equivalences for value assignments indexed by
structural causal model nodes. In particular, it identifies assignments on a
disjoint union of node sets with pairs of assignments on the two parts.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory

/-- For [two sets of graph nodes](hyp:A) that are [disjoint](hyp:hDisj), the [value-assignment equivalence for their union](goal) is a measurable bijection between assignments on their union and pairs consisting of an assignment on each set.

The forward map projects to each part and the inverse recombines them; disjointness
ensures the first part's priority cannot overwrite the second part. -/
noncomputable def valuesUnionEquiv {A B : Finset (SWIGNode N)}
    (hDisj : Disjoint A B) :
    ValuesOn (A ∪ B) (swigΩ Ω) ≃ᵐ
      ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) where
  toFun ξ :=
    (valuesProjection (Finset.subset_union_left) ξ,
     valuesProjection (Finset.subset_union_right) ξ)
  invFun p := valuesUnionMk p.1 p.2
  left_inv ξ := by
    funext ⟨v, hv⟩
    by_cases hA : v ∈ A
    · simp [valuesProjection, valuesUnionMk_apply_left _ _ hA]
    · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
      simp [valuesUnionMk_apply_right _ _ hv hA, valuesProjection]
  right_inv := by
    rintro ⟨a, b⟩
    ext
    · rename_i i
      obtain ⟨v, hvA⟩ := i
      have hv : v ∈ A ∪ B := Finset.subset_union_left hvA
      simp [valuesProjection, valuesUnionMk_apply_left _ _ hvA]
    · rename_i i
      obtain ⟨v, hvB⟩ := i
      have hv : v ∈ A ∪ B := Finset.subset_union_right hvB
      have hA : v ∉ A := fun hA' =>
        (Finset.disjoint_left.mp hDisj hA') hvB
      simp [valuesProjection, valuesUnionMk_apply_right _ _ hv hA]
  measurable_toFun :=
    (measurable_valuesProjection _).prodMk (measurable_valuesProjection _)
  measurable_invFun := by
    change Measurable (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
      valuesUnionMk p.1 p.2)
    refine measurable_pi_iff.mpr ?_
    rintro ⟨v, hv⟩
    by_cases hA : v ∈ A
    · have h_eq :
          (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk p.1 p.2 ⟨v, hv⟩)
            = (fun p => p.1 ⟨v, hA⟩) :=
        funext fun _ => valuesUnionMk_apply_left _ _ hA
      rw [h_eq]
      exact (measurable_pi_apply _).comp measurable_fst
    · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
      have h_eq :
          (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk p.1 p.2 ⟨v, hv⟩)
            = (fun p => p.2 ⟨v, hB⟩) :=
        funext fun _ => valuesUnionMk_apply_right _ _ hv hA
      rw [h_eq]
      exact (measurable_pi_apply _).comp measurable_snd

end SCM
end Causalean

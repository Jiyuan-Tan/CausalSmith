/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.Data.Finset.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Dependent functions over finite index sets

This file provides dependent function spaces over finite index sets, measurable coordinate
restrictions, canonical equivalences and product-measure transport for equal index sets, and
assembly over unions.

The restriction map `valuesProjection` coincides definitionally with Mathlib's
`Finset.restrict₂`.
-/

@[expose] public section

open scoped MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

/-- The [dependent function space over a finite coordinate set](goal) selects [a finite
subset](hyp:I) of [an index type](hyp:M) and assigns each selected index a value in its
[associated coordinate type](hyp:Ω). -/
abbrev ValuesOn {M : Type*}
    (I : Finset M) (Ω : M → Type*) :=
  ∀ i : {i // i ∈ I}, Ω i.val

/-- The [coordinate-restriction map](goal) takes dependent functions over [a finite set of
indices](hyp:I) in [an index type](hyp:M) with [measurable coordinate types](hyp:Ω) and retains
only coordinates in [a contained finite subset](hyp:J,hJI).

    This coincides definitionally with Mathlib's `Finset.restrict₂`; we keep the explicit
    lambda body because a large number of downstream proofs `simp [valuesProjection]` and rely
    on it unfolding to `fun ξ j => ξ ⟨j.val, hJI j.property⟩`. -/
def valuesProjection {M : Type*}
    {I J : Finset M} {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)]
    (hJI : J ⊆ I) : ValuesOn I Ω → ValuesOn J Ω :=
  fun ξ j => ξ ⟨j.val, hJI j.property⟩

/-- [Restricting a dependent function to a contained finite set of coordinates is
measurable](goal) for [an index type](hyp:M), [the original and retained finite
sets](hyp:I,J), [measurable coordinate types](hyp:Ω'), and [the stated containment](hyp:hJI).

    Coordinate restriction `valuesProjection hJI` is measurable; since it coincides with
    `Finset.restrict₂ hJI`, measurability is exactly `Finset.measurable_restrict₂`. -/
@[fun_prop]
theorem measurable_valuesProjection {M : Type*}
    {I J : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hJI : J ⊆ I) : Measurable (valuesProjection (Ω := Ω') hJI) :=
  Finset.measurable_restrict₂ hJI

/-- [Pulling back the product σ-algebra along coordinate restriction yields a sub-σ-algebra of
the original product space](goal) for [an index type](hyp:M), [the original and retained finite
sets](hyp:I,W), [measurable coordinate types](hyp:Ω'), and [their containment](hyp:hW).

    The comap of `valuesProjection` gives a sub-σ-algebra of the ambient
    measurable space on `ValuesOn I Ω`. -/
theorem comap_valuesProjection_le {M : Type*}
    {I W : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hW : W ⊆ I) :
    MeasurableSpace.comap (valuesProjection (Ω := Ω') hW) inferInstance ≤
      (inferInstance : MeasurableSpace (ValuesOn I Ω')) :=
  Measurable.comap_le (measurable_valuesProjection hW)

/-- For [finite sets `K`, `J`, and `I`](hyp:K,J,I), [an index type](hyp:M),
[measurable coordinate types](hyp:Ω'), [the inclusion `K ⊆ J`](hyp:hKJ), and
[the inclusion `J ⊆ I`](hyp:hJI), [coordinate restriction composes](goal). -/
theorem valuesProjection_comp {M : Type*}
    {I J K : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hKJ : K ⊆ J) (hJI : J ⊆ I) :
    valuesProjection (Ω := Ω') (hKJ.trans hJI) =
      valuesProjection hKJ ∘ valuesProjection hJI := by
  funext ξ ⟨k, hk⟩
  simp only [Function.comp_apply, valuesProjection]

/-- For [finite sets `A`, `B`, and `I`](hyp:A,B,I), [an index type](hyp:M),
[measurable coordinate types](hyp:Ω'), [the inclusion `A ⊆ B`](hyp:hAB), and
[the inclusion `B ⊆ I`](hyp:hBI), [the projection pullbacks are monotone](goal). -/
theorem comap_valuesProjection_mono {M : Type*}
    {I A B : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hAB : A ⊆ B) (hBI : B ⊆ I) :
    MeasurableSpace.comap (valuesProjection (Ω := Ω') (hAB.trans hBI)) inferInstance ≤
      MeasurableSpace.comap (valuesProjection (Ω := Ω') hBI) inferInstance := by
  have hcomp := valuesProjection_comp (Ω' := Ω') hAB hBI
  rw [hcomp]
  intro s ⟨t, ht, hts⟩
  exact ⟨valuesProjection hAB ⁻¹' t, measurable_valuesProjection hAB ht, hts⟩

/-- For [finite sets `A`, `B`, and `I`](hyp:A,B,I), [a decidable index type](hyp:M),
[measurable coordinate types](hyp:Ω'), and [inclusions in `I`](hyp:hA,hB),
[union projection is measurable for the supremum pullback](goal). -/
theorem measurable_valuesProjection_union_sup
    {M : Type*} [DecidableEq M]
    {I A B : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hA : A ⊆ I) (hB : B ⊆ I) :
    @Measurable (ValuesOn I Ω') (ValuesOn (A ∪ B) Ω')
      (MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
        MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance)
      inferInstance
      (valuesProjection (Ω := Ω') (Finset.union_subset hA hB)) := by
  let hAB : A ∪ B ⊆ I := Finset.union_subset hA hB
  change @Measurable (ValuesOn I Ω') (∀ i : {i // i ∈ A ∪ B}, Ω' i.val)
    (MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
      MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance)
    inferInstance
    (fun ξ : ValuesOn I Ω' => fun i : {i // i ∈ A ∪ B} =>
      ξ ⟨i.val, hAB i.property⟩)
  refine (@measurable_pi_iff (ValuesOn I Ω') {i // i ∈ A ∪ B}
    (fun i : {i // i ∈ A ∪ B} => Ω' i.val)
    (MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
      MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance)
    inferInstance
    (fun ξ : ValuesOn I Ω' => fun i : {i // i ∈ A ∪ B} =>
      ξ ⟨i.val, hAB i.property⟩)).2 ?_
  intro ⟨i, hiAB⟩
  by_cases hiA : i ∈ A
  · have hπA :
        @Measurable (ValuesOn I Ω') (ValuesOn A Ω')
          (MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
            MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance)
          inferInstance
          (valuesProjection (Ω := Ω') hA) :=
      Measurable.of_comap_le le_sup_left
    exact (measurable_pi_apply (⟨i, hiA⟩ : {j // j ∈ A})).comp hπA
  · have hiB : i ∈ B := (Finset.mem_union.mp hiAB).resolve_left hiA
    have hπB :
        @Measurable (ValuesOn I Ω') (ValuesOn B Ω')
          (MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
            MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance)
          inferInstance
          (valuesProjection (Ω := Ω') hB) :=
      Measurable.of_comap_le le_sup_right
    exact (measurable_pi_apply (⟨i, hiB⟩ : {j // j ∈ B})).comp hπB

/-- For [finite sets `A`, `B`, and `I`](hyp:A,B,I), [a decidable index type](hyp:M),
[measurable coordinate types](hyp:Ω'), and [inclusions in `I`](hyp:hA,hB),
[the union-projection pullback equals the supremum of the separate pullbacks](goal). -/
theorem comap_valuesProjection_union_eq_sup
    {M : Type*} [DecidableEq M]
    {I A B : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hA : A ⊆ I) (hB : B ⊆ I) :
    MeasurableSpace.comap
        (valuesProjection (Ω := Ω') (Finset.union_subset hA hB)) inferInstance =
      MeasurableSpace.comap (valuesProjection (Ω := Ω') hA) inferInstance ⊔
        MeasurableSpace.comap (valuesProjection (Ω := Ω') hB) inferInstance := by
  let hAB : A ∪ B ⊆ I := Finset.union_subset hA hB
  apply le_antisymm
  · exact Measurable.comap_le (measurable_valuesProjection_union_sup (Ω' := Ω') hA hB)
  · exact sup_le
      (comap_valuesProjection_mono (Ω' := Ω') Finset.subset_union_left hAB)
      (comap_valuesProjection_mono (Ω' := Ω') Finset.subset_union_right hAB)

/-- [Equal finite index sets determine a canonical measurable equivalence between their
dependent function spaces](goal). The construction uses [an index type](hyp:M), [the two finite
sets](hyp:I,J), [measurable coordinate types](hyp:Ω), and [the equality identifying the
sets](hyp:h).

    `ValuesOn I Ω` and `ValuesOn J Ω` are canonically measurably-equivalent when the
    index `Finset`s agree propositionally.  Packages the `valuesProjection`
    inverse pair so call sites avoid ad-hoc `▸`/`HEq` on the `Subtype` index. -/
noncomputable def valuesEquivOfEq {M : Type*}
    {I J : Finset M} {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)]
    (h : I = J) : ValuesOn I Ω ≃ᵐ ValuesOn J Ω where
  toFun := valuesProjection (le_of_eq h.symm)
  invFun := valuesProjection (le_of_eq h)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := measurable_valuesProjection (le_of_eq h.symm)
  measurable_invFun := measurable_valuesProjection (le_of_eq h)

/-- [The canonical equivalence between equal finite index sets preserves their coordinatewise
product measures](goal). It uses [an index type](hyp:M), [the two finite sets](hyp:I,J),
[measurable coordinate types](hyp:Ω), [their equality](hyp:h), and [one measure for each
coordinate of the first set](hyp:μ).

    `Measure.pi` transports along `valuesEquivOfEq`: the equiv is measure-preserving
    between the two `Measure.pi`'s whose per-coordinate measures agree through the
    subtype transport of the index equality. -/
lemma measurePreserving_valuesEquivOfEq {M : Type*}
    {I J : Finset M} {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)]
    (h : I = J)
    (μ : (i : {i // i ∈ I}) → MeasureTheory.Measure (Ω i.val)) :
    MeasureTheory.MeasurePreserving (valuesEquivOfEq (Ω := Ω) h)
      (MeasureTheory.Measure.pi μ)
      (MeasureTheory.Measure.pi
        (fun j : {j // j ∈ J} => μ ⟨j.val, h ▸ j.property⟩)) := by
  subst h
  refine ⟨(valuesEquivOfEq (Ω := Ω) rfl).measurable, ?_⟩
  have hid : (⇑(valuesEquivOfEq (Ω := Ω) (rfl : I = I))
      : ValuesOn I Ω → ValuesOn I Ω) = id := by
    funext ξ; rfl
  rw [show (MeasureTheory.Measure.map (valuesEquivOfEq (Ω := Ω) rfl)
        (MeasureTheory.Measure.pi μ) : MeasureTheory.Measure _)
      = MeasureTheory.Measure.map id (MeasureTheory.Measure.pi μ) from by rw [hid]]
  rw [MeasureTheory.Measure.map_id]

/-- The [union assignment](goal) combines [dependent functions on two finite index
sets](hyp:A,B,a,b) drawn from [a decidable index type](hyp:M) with [measurable coordinate
types](hyp:Ω); the first function supplies values on overlaps.

The first assignment takes priority on overlapping coordinates; the second
assignment is used on the remaining coordinates. -/
noncomputable def valuesUnionMk {M : Type*} [DecidableEq M]
    {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)] {A B : Finset M}
    (a : ValuesOn A Ω) (b : ValuesOn B Ω) :
    ValuesOn (A ∪ B) Ω := fun ⟨v, hv⟩ =>
  if hA : v ∈ A then a ⟨v, hA⟩
  else b ⟨v, (Finset.mem_union.mp hv).resolve_left hA⟩

/-- Projecting a union assignment to a coordinate from the first input returns that value. -/
@[simp] lemma valuesUnionMk_apply_left {M : Type*} [DecidableEq M]
    {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)] {A B : Finset M}
    (a : ValuesOn A Ω) (b : ValuesOn B Ω)
    {v : M} (hA : v ∈ A) :
    valuesUnionMk a b ⟨v, Finset.mem_union_left B hA⟩ = a ⟨v, hA⟩ := by
  unfold valuesUnionMk
  exact dif_pos hA

/-- Projecting a union assignment outside the first input returns the second input's value. -/
@[simp] lemma valuesUnionMk_apply_right {M : Type*} [DecidableEq M]
    {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)] {A B : Finset M}
    (a : ValuesOn A Ω) (b : ValuesOn B Ω)
    {v : M} (hv : v ∈ A ∪ B) (hA : v ∉ A) :
    valuesUnionMk a b ⟨v, hv⟩ = b ⟨v, (Finset.mem_union.mp hv).resolve_left hA⟩ := by
  unfold valuesUnionMk
  exact dif_neg hA

/-- Combining dependent functions is measurable in the second input with the first held fixed.

At every output coordinate the value is either constant or a coordinate
projection of the second assignment. -/
@[fun_prop]
lemma measurable_valuesUnionMk_right {M : Type*} [DecidableEq M]
    {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)] {A B : Finset M}
    (a : ValuesOn A Ω) :
    Measurable (fun b : ValuesOn B Ω => valuesUnionMk a b) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨v, hv⟩
  by_cases hA : v ∈ A
  · have h_eq :
        (fun b : ValuesOn B Ω => valuesUnionMk a b ⟨v, hv⟩)
          = (fun _ => a ⟨v, hA⟩) :=
      funext fun _ => valuesUnionMk_apply_left a _ hA
    rw [h_eq]
    exact measurable_const
  · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
    have h_eq :
        (fun b : ValuesOn B Ω => valuesUnionMk a b ⟨v, hv⟩)
          = (fun b => b ⟨v, hB⟩) :=
      funext fun _ => valuesUnionMk_apply_right a _ hv hA
    rw [h_eq]
    exact measurable_pi_apply _

/-- Combining dependent functions is jointly measurable in both inputs. -/
@[fun_prop]
lemma measurable_valuesUnionMk {M : Type*} [DecidableEq M]
    {Ω : M → Type*} [∀ n, MeasurableSpace (Ω n)] {A B : Finset M} :
    Measurable
      (fun p : ValuesOn A Ω × ValuesOn B Ω =>
        valuesUnionMk p.1 p.2) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨v, hv⟩
  by_cases hA : v ∈ A
  · have h_eq :
        (fun p : ValuesOn A Ω × ValuesOn B Ω =>
            valuesUnionMk p.1 p.2 ⟨v, hv⟩)
          = (fun p => p.1 ⟨v, hA⟩) := by
      funext p
      exact valuesUnionMk_apply_left _ _ hA
    rw [h_eq]
    exact (measurable_pi_apply _).comp measurable_fst
  · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hA
    have h_eq :
        (fun p : ValuesOn A Ω × ValuesOn B Ω =>
            valuesUnionMk p.1 p.2 ⟨v, hv⟩)
          = (fun p => p.2 ⟨v, hB⟩) := by
      funext p
      exact valuesUnionMk_apply_right _ _ hv hA
    rw [h_eq]
    exact (measurable_pi_apply _).comp measurable_snd

/-- For [finite sets `A`, `B`, and `I`](hyp:A,B,I), [a decidable index type](hyp:M),
[measurable coordinate types](hyp:Ω'), and [inclusions in `I`](hyp:hA,hB),
[assembling the projected blocks equals projection to their union](goal). -/
theorem valuesUnionMk_projection_comp
    {M : Type*} [DecidableEq M]
    {I A B : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (hA : A ⊆ I) (hB : B ⊆ I) :
    (fun ξ : ValuesOn I Ω' =>
      valuesUnionMk (Ω := Ω') (valuesProjection hA ξ) (valuesProjection hB ξ)) =
      valuesProjection (Finset.union_subset hA hB) := by
  let hAB : A ∪ B ⊆ I := Finset.union_subset hA hB
  funext ξ ⟨i, hiAB⟩
  by_cases hiA : i ∈ A
  · simp [valuesUnionMk, valuesProjection, hiA]
  · simp [valuesUnionMk, valuesProjection, hiA]

/-- For [finite sets `A` and `B`](hyp:A,B), [their disjointness](hyp:hAB),
[a decidable index type](hyp:M), [measurable coordinate types](hyp:Ω), and
[dependent functions `a` and `b`](hyp:a,b), [union commutativity swaps the inputs](goal). -/
lemma valuesUnionMk_comm {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A B : Finset M} (hAB : Disjoint A B)
    (a : ValuesOn A Ω) (b : ValuesOn B Ω) :
    valuesEquivOfEq (Finset.union_comm A B) (valuesUnionMk a b) =
      valuesUnionMk b a := by
  funext ⟨v, hv⟩
  have hvAB : v ∈ A ∪ B := by rwa [Finset.union_comm]
  change valuesUnionMk a b ⟨v, hvAB⟩ = valuesUnionMk b a ⟨v, hv⟩
  by_cases hA : v ∈ A
  · have hB : v ∉ B := fun h => Finset.disjoint_left.mp hAB hA h
    simp only [valuesUnionMk, dif_pos hA, dif_neg hB]
  · have hB : v ∈ B := (Finset.mem_union.mp hv).resolve_right hA
    simp only [valuesUnionMk, dif_pos hB, dif_neg hA]

/-- For [a finite set `A`](hyp:A), [a decidable index type](hyp:M),
[measurable coordinate types](hyp:Ω), [a dependent function `a`](hyp:a), and
[an empty-domain function `e`](hyp:e), [right union with `e` recovers `a`](goal). -/
lemma valuesUnionMk_empty_right {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A : Finset M}
    (a : ValuesOn A Ω) (e : ValuesOn (∅ : Finset M) Ω) :
    valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e) = a := by
  funext ⟨v, hv⟩
  have hvA : v ∈ A ∪ (∅ : Finset M) := by rwa [Finset.union_empty]
  change valuesUnionMk a e ⟨v, hvA⟩ = a ⟨v, hv⟩
  simp only [valuesUnionMk, dif_pos hv]

/-- For [finite sets `I` and `J`](hyp:I,J), [their equality](hyp:h),
[measurable coordinate types](hyp:Ω), [a dependent function `x`](hyp:x), and an [index
type](hyp:M), [canonical transport is heterogeneously equal to the original function](goal). -/
lemma valuesEquivOfEq_heq {M : Type*} {Ω : M → Type*} [∀ m, MeasurableSpace (Ω m)]
    {I J : Finset M} (h : I = J) (x : ValuesOn I Ω) :
    HEq (valuesEquivOfEq h x) x := by
  subst h
  exact heq_of_eq rfl

/-- For [finite sets `A` and `B`](hyp:A,B), [their disjointness](hyp:hAB),
[a decidable index type](hyp:M), [measurable coordinate types](hyp:Ω), and
[dependent functions `a` and `b`](hyp:a,b), [the two union orders are heterogeneously
equal](goal). -/
lemma valuesUnionMk_comm_heq {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A B : Finset M} (hAB : Disjoint A B)
    (a : ValuesOn A Ω) (b : ValuesOn B Ω) :
    HEq (valuesUnionMk a b) (valuesUnionMk b a) := by
  rw [← valuesUnionMk_comm hAB a b]
  exact (valuesEquivOfEq_heq _ _).symm

/-- For [a finite set `A`](hyp:A), [a decidable index type](hyp:M),
[measurable coordinate types](hyp:Ω), [a dependent function `a`](hyp:a), and
[an empty-domain function `e`](hyp:e), [their union is heterogeneously equal to `a`](goal). -/
lemma valuesUnionMk_empty_right_heq {M : Type*} [DecidableEq M] {Ω : M → Type*}
    [∀ m, MeasurableSpace (Ω m)] {A : Finset M}
    (a : ValuesOn A Ω) (e : ValuesOn (∅ : Finset M) Ω) :
    HEq (valuesUnionMk a e) a := by
  have h : valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e) = a :=
    valuesUnionMk_empty_right a e
  have hx : HEq (valuesUnionMk a e)
      (valuesEquivOfEq (Finset.union_empty A) (valuesUnionMk a e)) :=
    (valuesEquivOfEq_heq (Finset.union_empty A) (valuesUnionMk a e)).symm
  rw [h] at hx
  exact hx

/-- For [finite sets `I` and `J`](hyp:I,J), [their equality](hyp:hIJ),
[an index type](hyp:M), [measurable coordinate types](hyp:Ω), [dependent functions `f` and
`g`](hyp:f,g), and [coordinatewise agreement](hyp:h), [the functions are heterogeneously
equal](goal). -/
lemma valuesOn_heq_of_coord {M : Type*} {Ω : M → Type*} [∀ m, MeasurableSpace (Ω m)]
    {I J : Finset M} (hIJ : I = J) (f : ValuesOn I Ω) (g : ValuesOn J Ω)
    (h : ∀ (v : M) (hI : v ∈ I) (hJ : v ∈ J), f ⟨v, hI⟩ = g ⟨v, hJ⟩) :
    HEq f g := by
  apply Function.hfunext (congrArg (fun S : Finset M => {i // i ∈ S}) hIJ)
  rintro ⟨v, hvI⟩ ⟨v', hvJ⟩ hidx
  have hv_eq : v = v' := (Subtype.heq_iff_coe_eq (by intro x; rw [hIJ])).mp hidx
  subst hv_eq
  exact heq_of_eq (h v hvI hvJ)

/-- For [an index type `ι`](hyp:ι), [coordinate types](hyp:α), [an index `v`](hyp:v), and
[a singleton assignment `x`](hyp:x), [the singleton-coordinate value](goal) is its value at `v`. -/
noncomputable def singletonValue {ι : Type*} {α : ι → Type*}
    {v : ι} (x : ValuesOn ({v} : Finset ι) α) : α v :=
  x ⟨v, by simp⟩

/-- For [an index type `ι`](hyp:ι), [coordinate types](hyp:α), [an index `v`](hyp:v), and
[a value `x`](hyp:x), [the singleton assignment](goal) assigns `x` to its sole coordinate. -/
noncomputable def singletonValues {ι : Type*} {α : ι → Type*}
    {v : ι} (x : α v) : ValuesOn ({v} : Finset ι) α :=
  fun ⟨w, hw⟩ => by
    have h : w = v := by simpa using hw
    exact h ▸ x

/-- For [an index type `ι`](hyp:ι), [measurable coordinate types](hyp:α), and
[an index `v`](hyp:v), [reading a singleton assignment is measurable](goal). -/
@[fun_prop]
lemma measurable_singletonValue {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {v : ι} :
    Measurable (singletonValue (α := α) (v := v)) := by
  unfold singletonValue
  exact measurable_pi_apply (⟨v, by simp⟩ : {w // w ∈ ({v} : Finset ι)})

/-- For [an index type `ι`](hyp:ι), [measurable coordinate types](hyp:α), and
[an index `v`](hyp:v), [building a singleton assignment is measurable](goal). -/
@[fun_prop]
lemma measurable_singletonValues {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {v : ι} :
    Measurable (singletonValues (α := α) (v := v)) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨w, hw⟩
  have h : w = v := by simpa using hw
  subst w
  change Measurable (id : α v → α v)
  exact measurable_id

/-- For [an index type `ι`](hyp:ι), [coordinate types](hyp:α), [an index `v`](hyp:v), and
[a value `x`](hyp:x), [reading its singleton assignment returns `x`](goal). -/
@[simp] lemma singletonValue_singletonValues {ι : Type*} {α : ι → Type*}
    {v : ι} (x : α v) :
    singletonValue (α := α) (v := v) (singletonValues (α := α) (v := v) x) = x := by
  rfl

/-- For [an index type `ι`](hyp:ι), [coordinate types](hyp:α), [an index `v`](hyp:v), and
[a singleton assignment `x`](hyp:x), [rebuilding from its value returns `x`](goal). -/
@[simp] lemma singletonValues_singletonValue {ι : Type*} {α : ι → Type*}
    {v : ι} (x : ValuesOn ({v} : Finset ι) α) :
    singletonValues (α := α) (v := v) (singletonValue (α := α) (v := v) x) = x := by
  ext ⟨w, hw⟩
  have hwv : w = v := by simpa using hw
  subst w
  rfl

/-- For [finite sets `S` and `P`](hyp:S,P), [a finite decidable index type](hyp:M'),
[measurable coordinate types](hyp:Ω'), and [the inclusion `S ⊆ P`](hyp:hS),
[the measurable equivalence](goal) removes the redundant nested subtype index. -/
noncomputable def reindexSubtypeProj {M' : Type*} [DecidableEq M'] [Fintype M']
    {Ω' : M' → Type*} [∀ n, MeasurableSpace (Ω' n)] {P : Finset M'}
    (S : Finset M') (hS : S ⊆ P) :
    ((i : {i // i ∈ (S.subtype (· ∈ P))}) → Ω' i.val.val) ≃ᵐ
      ((j : {j // j ∈ S}) → Ω' j.val) where
  toFun := fun f j => f ⟨⟨j.val, hS j.property⟩, by
    simp only [Finset.mem_subtype]; exact j.property⟩
  invFun := fun g i => g ⟨i.val.val, by
    have := i.property; rw [Finset.mem_subtype] at this; exact this⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := by
    apply measurable_pi_lambda; intro j; exact measurable_pi_apply _
  measurable_invFun := by
    apply measurable_pi_lambda; intro i; exact measurable_pi_apply _

end Causalean.Mathlib.MeasureTheory

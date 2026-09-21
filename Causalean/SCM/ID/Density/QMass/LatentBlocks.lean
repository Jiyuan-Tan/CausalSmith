/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.LatentBlocks
public import Causalean.SCM.ID.Density.IdentifyMass
public import Causalean.SCM.ID.Density.MassBridge
public import Causalean.SCM.ID.DiscreteID.Positive
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Mathlib.Probability.Independence.InfinitePi
public import Causalean.Tactic.Attr
public import Causalean.SCM.ID.Density.QMass.Basic

/-! # Measurability of latent-block consistency events

This file identifies the latent coordinates on which local-consistency events
depend and proves the corresponding product-measurability statements.  The
results prepare those events for independence and factorization across
c-components.
-/

@[expose] public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The latent-product mass of a singleton latent assignment equals the product
of the singleton masses assigned by the latent distributions at every unobserved node. -/
lemma latentProduct_singleton_eq_prod
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ℓ₀ : M.LatentValues) :
    M.latentProduct ({ℓ₀} : Set M.LatentValues) =
      ∏ u : {u // u ∈ M.unobserved},
        M.latentDist u ({ℓ₀ u} : Set (swigΩ Ω u.val)) := by
  classical
  haveI : ∀ u : {u // u ∈ M.unobserved},
      MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
    M.isProbability_latent
  haveI : ∀ u : {u // u ∈ M.unobserved},
      MeasureTheory.SigmaFinite (M.latentDist u) := fun _ => inferInstance
  unfold SCM.latentProduct
  have hsingleton :
      ({ℓ₀} : Set M.LatentValues) =
        Set.univ.pi (fun u => ({ℓ₀ u} : Set (swigΩ Ω u.val))) := by
    ext ℓ
    simp [Set.mem_pi, funext_iff]
  rw [hsingleton, MeasureTheory.Measure.pi_pi]

/-- A set of finite product outcomes whose membership depends only on a specified
    finite set of coordinates is measurable with respect to the σ-algebra on those coordinates. -/
lemma measurableSet_comap_piFinset_of_depends
    {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, Fintype (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (S : Finset ι) (A : Set (∀ i, α i))
    (hdep : ∀ ξ ξ', (∀ i (_hi : i ∈ S), ξ i = ξ' i) → (ξ ∈ A ↔ ξ' ∈ A)) :
    MeasurableSet[
      MeasurableSpace.comap (fun ξ : (∀ i, α i) => fun i : S => ξ i)
        inferInstance] A := by
  let B : Set (∀ i : S, α i.val) :=
    {η | ∃ ξ ∈ A, (fun i : S => ξ i) = η}
  refine ⟨B, Set.Finite.measurableSet B.toFinite, ?_⟩
  ext ξ
  change ξ ∈ ((fun ξ : (∀ i, α i) => fun i : S => ξ i) ⁻¹' B) ↔ ξ ∈ A
  constructor
  · rintro ⟨ξ', hξ'A, hξ'⟩
    exact (hdep ξ' ξ (by
      intro i hi
      exact congrFun hξ' ⟨i, hi⟩)).mp hξ'A
  · intro hξA
    exact ⟨ξ, hξA, rfl⟩

/-- For [a structural causal model](hyp:M) and [a set of graph nodes](hyp:C), the
[latent-block index](goal) is the finite collection of the model's unobserved variables that
belong to that set's latent block. It is used to group the independent latent coordinates in
density factorization arguments. -/
noncomputable def latentBlockIndex
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N)) :
    Finset {u // u ∈ M.unobserved} :=
  Finset.univ.filter (fun u : {u // u ∈ M.unobserved} => u.val ∈ M.latentBlock C)

/-- Given [a finite structural causal model, node set, and unobserved node](hyp:N,Ω,M,C,u),
[the unobserved-node index belongs to the set's latent-block index exactly when the underlying
node belongs to its latent block](goal). -/
lemma mem_latentBlockIndex_iff
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N))
    (u : {u // u ∈ M.unobserved}) :
    u ∈ latentBlockIndex M C ↔ u.val ∈ M.latentBlock C := by
  simp [latentBlockIndex]

private lemma latentBlockIndex_pairwise_disjoint
    (M : Causalean.SCM N Ω) {C D : Finset (SWIGNode N)}
    (hC : C ∈ M.toSWIGGraph.cComponentSet)
    (hD : D ∈ M.toSWIGGraph.cComponentSet) (hne : C ≠ D) :
    Disjoint (latentBlockIndex M C) (latentBlockIndex M D) := by
  classical
  rw [Finset.disjoint_left]
  intro u huC huD
  have huC' : u.val ∈ M.latentBlock C :=
    (mem_latentBlockIndex_iff M C u).mp huC
  have huD' : u.val ∈ M.latentBlock D :=
    (mem_latentBlockIndex_iff M D u).mp huD
  exact Finset.disjoint_left.mp (M.latentBlock_pairwise_disjoint hC hD hne) huC' huD'

private lemma latentBlockIndex_pairwise_disjoint_of_latentBlock
    (M : Causalean.SCM N Ω) {C D : Finset (SWIGNode N)}
    (hdisj : Disjoint (M.latentBlock C) (M.latentBlock D)) :
    Disjoint (latentBlockIndex M C) (latentBlockIndex M D) := by
  classical
  rw [Finset.disjoint_left]
  intro u huC huD
  exact Finset.disjoint_left.mp hdisj
    ((mem_latentBlockIndex_iff M C u).mp huC)
    ((mem_latentBlockIndex_iff M D u).mp huD)

/-- Given [a finite structural causal model, a family of node sets, a subfamily, and one member](hyp:N,Ω,M,𝒞,S,C),
if [the subfamily lies in the family](hyp:hS), [the selected set belongs to the family](hyp:hC),
[it is outside the subfamily](hyp:hCnot), and [distinct family members have disjoint latent blocks](hyp:hblock),
then [the union of latent-block indices over the subfamily is disjoint from the selected set's index](goal). -/
lemma latentBlockIndex_biUnion_disjoint_of_pairwise
    (M : Causalean.SCM N Ω) {𝒞 S : Finset (Finset (SWIGNode N))}
    {C : Finset (SWIGNode N)} (hS : S ⊆ 𝒞) (hC : C ∈ 𝒞)
    (hCnot : C ∉ S)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U'))) :
    Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huS huC
  rw [Finset.mem_biUnion] at huS
  rcases huS with ⟨D, hDS, huD⟩
  have hD : D ∈ 𝒞 := hS hDS
  have hne : D ≠ C := by
    intro hDC
    exact hCnot (hDC ▸ hDS)
  exact Finset.disjoint_left.mp
    (latentBlockIndex_pairwise_disjoint_of_latentBlock M
      (hblock hD hC hne)) huD huC

/-- Given [a finite structural causal model, a collection of districts, and another district](hyp:N,Ω,M,S,C),
if [the collection consists of districts](hyp:hS), [the selected set is a district](hyp:hC), and
[it is outside the collection](hyp:hCnot), then [the collection's latent-block indices are disjoint
from the selected district's latent-block index](goal). -/
lemma latentBlockIndex_biUnion_disjoint
    (M : Causalean.SCM N Ω) {S : Finset (Finset (SWIGNode N))}
    {C : Finset (SWIGNode N)} (hS : S ⊆ M.toSWIGGraph.cComponentSet)
    (hC : C ∈ M.toSWIGGraph.cComponentSet) (hCnot : C ∉ S) :
    Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huS huC
  rw [Finset.mem_biUnion] at huS
  rcases huS with ⟨D, hDS, huD⟩
  have hne : D ≠ C := by
    intro hDC
    exact hCnot (hDC ▸ hDS)
  exact Finset.disjoint_left.mp
    (latentBlockIndex_pairwise_disjoint M (hS hDS) hC hne) huD huC

/-- Given [a finite structural causal model, fixed assignment, observed-parent-closed set, observed
assignment, and district](hyp:N,Ω,M,s,P,hP,x,C), if [the set is a district](hyp:hC), then [the latent
assignments locally consistent with the observed values on its intersection with the parent-closed
set form a measurable event](goal). -/
lemma localConsistent_event_measurable_comap_latentBlockIndex
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω))
    {C : Finset (SWIGNode N)} (hC : C ∈ M.toSWIGGraph.cComponentSet) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues => fun u : latentBlockIndex M C => ℓ u)
        inferInstance]
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
        M.localConsistent s x v
          (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ} := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := latentBlockIndex M C) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      M.toSWIGGraph.cComponentOf_eq_of_mem_cComponentSet hC hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ ℓ' (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord)).mp (hℓ v hv)
  · intro hℓ' v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      M.toSWIGGraph.cComponentOf_eq_of_mem_cComponentSet hC hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ' ℓ (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ' v hv)

/-- Given [a finite structural causal model, fixed assignment, observed-parent-closed set, observed
assignment, and collection of districts](hyp:N,Ω,M,s,P,hP,x,S), if [every selected set is a
district](hyp:hS), then [the event of simultaneous local consistency over their intersections with
the parent-closed set is measurable](goal). -/
lemma localConsistent_biInter_event_measurable_comap_latentBlockIndex
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω))
    {S : Finset (Finset (SWIGNode N))}
    (hS : S ⊆ M.toSWIGGraph.cComponentSet) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues =>
          fun u : S.biUnion (latentBlockIndex M) => ℓ u)
        inferInstance]
      (⋂ C ∈ S, {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
        M.localConsistent s x v
          (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ}) := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := S.biUnion (latentBlockIndex M)) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ
    rw [Set.mem_iInter] at hℓ
    rw [Set.mem_iInter]
    intro C
    have hℓC := hℓ C
    rw [Set.mem_iInter] at hℓC
    rw [Set.mem_iInter]
    intro hCS v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      M.toSWIGGraph.cComponentOf_eq_of_mem_cComponentSet (hS hCS) hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ ℓ' (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨C, hCS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord)).mp (hℓC hCS v hv)
  · intro hℓ'
    rw [Set.mem_iInter] at hℓ'
    rw [Set.mem_iInter]
    intro C
    have hℓ'C := hℓ' C
    rw [Set.mem_iInter] at hℓ'C
    rw [Set.mem_iInter]
    intro hCS v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      M.toSWIGGraph.cComponentOf_eq_of_mem_cComponentSet (hS hCS) hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ' ℓ (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨C, hCS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ'C hCS v hv)

/-- Local consistency at an observed node in a node set is unchanged when two latent assignments
agree on every unobserved parent of a node in that set. -/
lemma localConsistent_depends_only_on_latentBlock_of_mem
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) {U : Finset (SWIGNode N)}
    {v : SWIGNode N} (hvU : v ∈ U) (hv : v ∈ M.observed)
    (ℓ ℓ' : M.LatentValues)
    (hℓ : ∀ u (hu : u ∈ M.latentBlock U),
      ℓ ⟨u, (Finset.mem_filter.mp hu).1⟩ =
        ℓ' ⟨u, (Finset.mem_filter.mp hu).1⟩) :
    M.localConsistent s x v hv ℓ ↔ M.localConsistent s x v hv ℓ' := by
  unfold localConsistent
  set j : Fin M.observed.card := M.observedIndex ⟨v, hv⟩ with hj
  have hat : (M.observedAt j).val = v := by
    rw [hj]
    exact M.observedAt_observedIndex ⟨v, hv⟩
  have hfun :
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w)
        =
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ' j.isLt (prevFromObservedValues M x) w) := by
    congr 1
    funext w
    by_cases huo : w.val ∈ M.unobserved
    · rw [parentMap_unobserved M s ℓ j.isLt _ w huo,
          parentMap_unobserved M s ℓ' j.isLt _ w huo]
      have hedge_v : M.dag.edge w.val v := by
        have hedge_at : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        simpa [hat] using hedge_at
      have huBlock : w.val ∈ M.latentBlock U := by
        rw [latentBlock, Finset.mem_filter]
        exact ⟨huo, ⟨v, hvU, hedge_v⟩⟩
      exact hℓ w.val huBlock
    · by_cases hfix : w.val ∈ M.fixed
      · rw [parentMap_fixed M s ℓ j.isLt _ w hfix,
            parentMap_fixed M s ℓ' j.isLt _ w hfix]
      · have hedge : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        rw [parentMap_observed M s ℓ j.isLt _ w hobs,
            parentMap_observed M s ℓ' j.isLt _ w hobs]
  subst j
  change
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
      ↔
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ' (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
  rw [hfun]

/-- Given [a finite structural causal model, fixed assignment, observed node family, and observed
assignment](hyp:N,Ω,M,s,U,x), if [the family is observed](hyp:hUobs), then [the latent assignments
locally consistent at every node in the family form a measurable event](goal). -/
lemma localConsistent_event_measurable_comap_latentBlockIndex_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (U : Finset (SWIGNode N)) (hUobs : U ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues => fun u : latentBlockIndex M U => ℓ u)
        inferInstance]
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (hUobs hv) ℓ} := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := latentBlockIndex M U) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (hUobs hv) ℓ ℓ' (by
        intro u hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord)).mp (hℓ v hv)
  · intro hℓ' v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (hUobs hv) ℓ' ℓ (by
        intro u hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ' v hv)

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[a fixed-node assignment](hyp:s), [a finite family of observed node blocks and a selected
subfamily](hyp:𝒞,S), [containment of the subfamily](hyp:hS), [observability of every block
in the family](hyp:h𝒞obs), and [an observed realization](hyp:x), [the event that all local
consistency equations hold throughout the selected blocks is measurable using only the latent
coordinates in those blocks](goal). -/
lemma localConsistent_biInter_event_measurable_comap_latentBlockIndex_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 S : Finset (Finset (SWIGNode N))) (hS : S ⊆ 𝒞)
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues =>
          fun u : S.biUnion (latentBlockIndex M) => ℓ u)
        inferInstance]
      (⋂ U ∈ S, {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (h𝒞obs U (hS ‹U ∈ S›) hv) ℓ}) := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := S.biUnion (latentBlockIndex M)) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ
    rw [Set.mem_iInter] at hℓ
    rw [Set.mem_iInter]
    intro U
    have hℓU := hℓ U
    rw [Set.mem_iInter] at hℓU
    rw [Set.mem_iInter]
    intro hUS v hv
    have hlocal :
        M.localConsistent s x v (h𝒞obs U (hS hUS) hv) ℓ := by
      simpa [hS hUS] using hℓU hUS v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (h𝒞obs U (hS hUS) hv) ℓ ℓ' (by
        intro u hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨U, hUS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord)).mp hlocal
  · intro hℓ'
    rw [Set.mem_iInter] at hℓ'
    rw [Set.mem_iInter]
    intro U
    have hℓ'U := hℓ' U
    rw [Set.mem_iInter] at hℓ'U
    rw [Set.mem_iInter]
    intro hUS v hv
    have hlocal :
        M.localConsistent s x v (h𝒞obs U (hS hUS) hv) ℓ' := by
      simpa [hS hUS] using hℓ'U hUS v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (h𝒞obs U (hS hUS) hv) ℓ' ℓ (by
        intro u hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨U, hUS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord.symm)).mp hlocal


end Causalean.SCM

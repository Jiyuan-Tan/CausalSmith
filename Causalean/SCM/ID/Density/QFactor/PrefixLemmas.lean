/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.MechCFactor
public import Causalean.Graph.DSep.InduceTransport
public import Causalean.SCM.ID.Density.QFactor.Defs

/-! # Prefix and component lemmas for q-factor recovery

This file proves the topological-prefix closure and component-intersection facts
needed to factor `qLocalMass` along successive prefixes.  It also provides the
fixed-edge fact used when the ambient model is replaced by a do-model.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- Membership in a graph-ordered prefix of `D` is exactly index membership
below the prefix length. -/
lemma mem_prefixIn_iff (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (n : ℕ) (v : SWIGNode N) :
    v ∈ H.prefixIn D n ↔
      ∃ h : v ∈ D, (H.nodeIndex D ⟨v, h⟩).val < n := by
  unfold SWIGGraph.prefixIn
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hD, hltif⟩
    exact ⟨hD, by simpa [hD] using hltif⟩
  · rintro ⟨hD, hlt⟩
    exact Finset.mem_filter.mpr ⟨hD, by simpa [hD] using hlt⟩

/-- The `D`-prefix of length zero is empty. -/
lemma prefixIn_zero (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D 0 = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff H D 0 v).mp hv with ⟨_, hlt⟩
    omega
  · simp

/-- The node at index `i` belongs to the first `n` `D`-nodes iff `i < n`. -/
lemma nodesAt_mem_prefixIn_iff (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (n : ℕ) (i : Fin D.card) :
    (H.nodesAt D i).val ∈ H.prefixIn D n ↔ i.val < n := by
  rw [mem_prefixIn_iff]
  constructor
  · rintro ⟨hD, hlt⟩
    have hidx : H.nodeIndex D ⟨(H.nodesAt D i).val, hD⟩ = i := by
      have hsub :
          (⟨(H.nodesAt D i).val, hD⟩ : {v // v ∈ D}) = H.nodesAt D i :=
        Subtype.ext rfl
      rw [hsub]
      simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
    rwa [hidx] at hlt
  · intro hlt
    exact ⟨(H.nodesAt D i).property,
      by
        have hidx : H.nodeIndex D (H.nodesAt D i) = i := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        simpa [hidx] using hlt⟩

/-- The full `D`-prefix is `D`. -/
lemma prefixIn_card (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D D.card = D := by
  ext v
  constructor
  · exact fun hv => H.prefixIn_subset D D.card hv
  · intro hv
    exact (mem_prefixIn_iff H D D.card v).mpr
      ⟨hv, (H.nodeIndex D ⟨v, hv⟩).isLt⟩

/-- Prefix sets are monotone in the prefix length. -/
lemma prefixIn_mono (H : SWIGGraph N) (D : Finset (SWIGNode N)) {m k : ℕ}
    (h : m ≤ k) :
    H.prefixIn D m ⊆ H.prefixIn D k := by
  intro v hv
  rcases (mem_prefixIn_iff H D m v).mp hv with ⟨hD, hlt⟩
  exact (mem_prefixIn_iff H D k v).mpr ⟨hD, lt_of_lt_of_le hlt h⟩

/-- The next `D`-node is not in the previous `D`-prefix. -/
lemma nodesAt_not_mem_prefixIn (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    (H.nodesAt D ⟨n, hn⟩).val ∉ H.prefixIn D n := by
  rw [nodesAt_mem_prefixIn_iff H D n ⟨n, hn⟩]
  exact Nat.lt_irrefl n

/-- The successor `D`-prefix is obtained by adjoining the next `D`-node. -/
lemma prefixIn_succ (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    H.prefixIn D (n + 1) =
      H.prefixIn D n ∪ {(H.nodesAt D ⟨n, hn⟩).val} := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff H D (n + 1) v).mp hv with ⟨hD, hlt⟩
    by_cases hlt_n : (H.nodeIndex D ⟨v, hD⟩).val < n
    · exact Finset.mem_union_left _ ((mem_prefixIn_iff H D n v).mpr ⟨hD, hlt_n⟩)
    · have hidx_val : (H.nodeIndex D ⟨v, hD⟩).val = n := by omega
      have hidx : H.nodeIndex D ⟨v, hD⟩ = ⟨n, hn⟩ := Fin.ext hidx_val
      have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by
        have hround : H.nodesAt D (H.nodeIndex D ⟨v, hD⟩) = ⟨v, hD⟩ := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        rw [hidx] at hround
        exact congrArg Subtype.val hround.symm
      exact Finset.mem_union_right _ (by simp [hv_eq])
  · intro hv
    rcases Finset.mem_union.mp hv with hvpre | hvlast
    · rcases (mem_prefixIn_iff H D n v).mp hvpre with ⟨hD, hlt⟩
      exact (mem_prefixIn_iff H D (n + 1) v).mpr ⟨hD, by omega⟩
    · have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by simpa using hvlast
      subst hv_eq
      rw [nodesAt_mem_prefixIn_iff H D (n + 1) ⟨n, hn⟩]
      exact Nat.lt_succ_self n

/-- The previous `D`-prefix is disjoint from the singleton next node. -/
lemma prefixIn_disjoint_singleton_next (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    Disjoint (H.prefixIn D n)
      ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) := by
  rw [Finset.disjoint_singleton_right]
  exact nodesAt_not_mem_prefixIn H D hn

/-- For [a finite single-world intervention graph and node set](hyp:N,H,D), [the zero-length
topological prefix is empty](goal). -/
@[deprecated prefixIn_zero (since := "2026-09-19")]
lemma prefixIn_zero_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D 0 = ∅ :=
  prefixIn_zero H D

/-- For [a finite single-world intervention graph, node set, prefix length, and valid node
index](hyp:N,H,D,n,i), [the indexed node belongs to the prefix exactly when its index is below
the prefix length](goal). -/
@[deprecated nodesAt_mem_prefixIn_iff (since := "2026-09-19")]
lemma nodesAt_mem_prefixIn_iff_qfactor (H : SWIGGraph N)
    (D : Finset (SWIGNode N)) (n : ℕ) (i : Fin D.card) :
    (H.nodesAt D i).val ∈ H.prefixIn D n ↔ i.val < n :=
  nodesAt_mem_prefixIn_iff H D n i

/-- For [a finite single-world intervention graph and node set](hyp:N,H,D), [the prefix whose
length is the set's cardinality is the entire set](goal). -/
@[deprecated prefixIn_card (since := "2026-09-19")]
lemma prefixIn_card_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D D.card = D :=
  prefixIn_card H D

/-- For [a finite single-world intervention graph, node set, and two prefix lengths](hyp:N,H,D,m,k),
if [the first length does not exceed the second](hyp:h), then [the first prefix is contained in
the second](goal). -/
@[deprecated prefixIn_mono (since := "2026-09-19")]
lemma prefixIn_mono_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {m k : ℕ} (h : m ≤ k) :
    H.prefixIn D m ⊆ H.prefixIn D k :=
  prefixIn_mono H D h

/-- For [a finite single-world intervention graph, node set, and prefix length](hyp:N,H,D,n),
if [the length is below the set's cardinality](hyp:hn), then [the next prefix is the current
prefix with the next topologically ordered node inserted](goal). -/
@[deprecated prefixIn_succ (since := "2026-09-19")]
lemma prefixIn_succ_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    H.prefixIn D (n + 1) =
      H.prefixIn D n ∪ {(H.nodesAt D ⟨n, hn⟩).val} :=
  prefixIn_succ H D hn

/-- Given [a finite structural causal model and an intervention set](hyp:N,Ω,M,X), if [every
intervened random copy is observed](hyp:hObs), [no corresponding fixed copy is already fixed](hyp:hFix),
and [the model is standard](hyp:hStd), then for [a node whose fixed copy is fixed after the
intervention](hyp:n) and [any target node](hyp:v), [the intervened random copy has no outgoing
edge to that target](goal). -/
@[deprecated fixSet_fixed_random_edgeless (since := "2026-09-19")]
lemma fixSet_fixed_random_edgeless_qfactor
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hStd : M.isStandard) :
    ∀ n : N, SWIGNode.fixed n ∈ (M.fixSet X hObs hFix).fixed →
      ∀ v : SWIGNode N, ¬ (M.fixSet X hObs hFix).dag.edge (SWIGNode.random n) v :=
  fixSet_fixed_random_edgeless M X hObs hFix hStd

/-- In an induced set of observed variables, every topological prefix contains all parents
within that set of each variable it contains. -/
lemma prefixIn_parent_closed_induce_observed
    (M : Causalean.SCM N Ω) (A : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (k : ℕ) :
    ∀ v ∈ A, ∀ w ∈ (M.toSWIGGraph.induce A).prefixIn A k,
      M.dag.edge v w → v ∈ (M.toSWIGGraph.induce A).prefixIn A k := by
  classical
  intro v hvA w hwPre hEdge
  let H := M.toSWIGGraph.induce A
  have hwA : w ∈ A := H.prefixIn_subset A k hwPre
  have hEdgeH : H.dag.edge v w := by
    dsimp [H, SWIGGraph.induce]
    rw [SWIGGraph.inducedDag_edge_iff]
    refine ⟨hEdge, ?_, ?_⟩
    · simp [hvA, hA hvA]
    · simp [hwA, hA hwA]
  have hTopo : H.dag.topoOrder v < H.dag.topoOrder w :=
    H.dag.topoOrder_lt v w hEdgeH
  rcases (mem_prefixIn_iff H A k w).mp hwPre with ⟨hwA', hwIdxLt⟩
  letI := H.topoLinearOrder
  have hSubtypeLt : (⟨v, hvA⟩ : {v // v ∈ A}) < ⟨w, hwA'⟩ := by
    change H.dag.topoOrder v < H.dag.topoOrder w
    exact hTopo
  have hIndexLt :
      (H.nodeIndex A ⟨v, hvA⟩).val < (H.nodeIndex A ⟨w, hwA'⟩).val := by
    have hIndexLtFin : H.nodeIndex A ⟨v, hvA⟩ < H.nodeIndex A ⟨w, hwA'⟩ := by
      simpa [SWIGGraph.nodeIndex] using
        ((A.orderIsoOfFin rfl).symm.strictMono hSubtypeLt)
    simpa [SWIGGraph.nodeIndex] using hIndexLtFin
  exact (mem_prefixIn_iff H A k v).mpr
    ⟨hvA, lt_trans hIndexLt hwIdxLt⟩

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[a fixed-node assignment](hyp:s), [an observed ancestral node set](hyp:A), [evidence that it is
observed](hyp:hA), [a prefix length](hyp:k), and [an observed realization](hyp:x), [the local
q-mass of the induced graph's prefix factors into the local q-masses of its intersections with
the induced c-components](goal). -/
lemma qLocalMass_prefixIn_eq_prod_induce_components
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (A : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (k : ℕ) (x : ValuesOn M.observed (swigΩ Ω)) :
    let H := M.toSWIGGraph.induce A
    M.qLocalMass s (H.prefixIn A k)
        (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
      ∏ C ∈ H.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k
            (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let H := M.toSWIGGraph.induce A
  have hHobs : H.observed = A := by
    simp [H, SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
  have h𝒞obs : ∀ U ∈ H.cComponentSet, U ⊆ M.observed := by
    intro U hU v hv
    exact hA (hHobs ▸ H.cComponentSet_subset_observed U hU hv)
  have hcover : H.prefixIn A k ⊆ H.cComponentSet.sup id := by
    intro v hv
    have hvObs : v ∈ H.observed := by
      rw [hHobs]
      exact H.prefixIn_subset A k hv
    rw [Finset.mem_sup]
    exact ⟨H.cComponentOf v,
      (by
        rw [SWIGGraph.cComponentSet, Finset.mem_image]
        exact ⟨v, hvObs, rfl⟩),
      H.mem_cComponentOf_self hvObs⟩
  have hblock :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')) := by
    intro U hU V hV hne
    exact latentBlock_pairwise_disjoint_induce_components M A hU hV hne
  have hfac :=
    M.qLocalMass_prod_inter_of_latentBlock_disjoint s
      (H.prefixIn A k) (fun _ hv => hA (H.prefixIn_subset A k hv))
      H.cComponentSet h𝒞obs hcover hblock x
  calc
    M.qLocalMass s (H.prefixIn A k)
        (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
      ∏ C ∈ H.cComponentSet,
        if hC : C ∈ H.cComponentSet then
          M.qLocalMass s (C ∩ H.prefixIn A k)
            (fun _ hv => h𝒞obs C hC (Finset.mem_of_mem_inter_left hv)) x
        else 1 := by
          simpa [H] using hfac
    _ =
      ∏ C ∈ H.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k
            (Finset.mem_of_mem_inter_right hv))) x := by
          refine Finset.prod_congr rfl ?_
          intro C hC
          simp [hC]

/-- Given [a finite structural causal model, a graph, a node set, and two districts](hyp:N,Ω,M,H,D,S,C),
if [the first](hyp:hScomp) and [second](hyp:hCcomp) sets are districts, [the node set is observed](hyp:hDobs),
[the next prefix node lies in the first district](hyp:i,hiS), and [the districts differ](hyp:hCS),
then [intersecting the second district with the prefix is unchanged at that step](goal). -/
lemma cComponent_inter_prefixIn_succ_eq_of_ne
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S C : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hCcomp : C ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin D.card}
    (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (hCS : C ≠ S) :
    C ∩ H.prefixIn D (i.val + 1) = C ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [prefixIn_succ H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      have hnodeObs : (H.nodesAt D i).val ∈ M.observed :=
        hDobs (H.nodesAt D i).property
      have hSC : S = C := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          hnodeObs hCcomp).mp hvC ▸
          ((mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            hnodeObs hScomp).mp hiS).symm
      exact False.elim (hCS hSC.symm)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, prefixIn_mono H D (Nat.le_succ i.val) hvpre⟩

/-- Given [a finite graph, node set, two families, and a prefix index](hyp:N,H,D,S,C,i), if [the
next prefix node lies in the first family](hyp:hiS) and [the families are disjoint](hyp:hdisj),
then [intersecting the second family with the prefix is unchanged at that step](goal). -/
lemma family_inter_prefixIn_succ_eq_of_ne
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S C : Finset (SWIGNode N)} {i : Fin D.card}
    (hiS : (H.nodesAt D i).val ∈ S)
    (hdisj : Disjoint C S) :
    C ∩ H.prefixIn D (i.val + 1) = C ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [prefixIn_succ H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (Finset.disjoint_left.mp hdisj hvC hiS)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, prefixIn_mono H D (Nat.le_succ i.val) hvpre⟩

/-- Given [a finite graph, node set, component, and prefix index](hyp:N,H,D,S,i), if [the next
prefix node is outside the component](hyp:hiS), then [the component's intersection with the
prefix is unchanged at that step](goal). -/
lemma cComponent_inter_prefixIn_succ_eq_of_node_not_mem
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S : Finset (SWIGNode N)} {i : Fin D.card}
    (hiS : (H.nodesAt D i).val ∉ S) :
    S ∩ H.prefixIn D (i.val + 1) = S ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    rw [prefixIn_succ H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvS, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (hiS hvS)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvS, prefixIn_mono H D (Nat.le_succ i.val) hvpre⟩


end SCM.ID
end Causalean

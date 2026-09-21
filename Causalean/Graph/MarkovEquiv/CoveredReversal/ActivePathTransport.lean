/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.AcyclicConstruct
public import Causalean.Graph.MarkovEquiv.Defs
public import Causalean.Graph.MarkovEquiv.CoveredReversal.FlipEdge

/-! # Active-walk transport ingredients for covered-edge reversal

This file develops the local invariance facts used to transport active walks across
`DAG.flipEdge`. It relates d-connection to active walks, proves edge-relation congruence lemmas,
tracks ancestry through a covered reversal, and defines `swapPath` together with the obstruction
and list-surgery operations used by `PathSurgery`. The final transport argument and
`markovEquiv_flipEdge` are in `MarkovEquivalence`.
-/

@[expose] public section

namespace Causalean.Graph

open Causalean.Graph.MarkovEquiv

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)
variable {G}

/-- **Bridge: failure of d-separation is exactly an active walk.** For pairwise-disjoint
query sets, `X` and `Y` are *not* d-separated by `Z` iff there is an active walk from `X` to
`Y` given `Z`. Assembled from `bbReachableVertices_iff_activeWalk`. Reduces the covered-flip
invariance to a pure active-walk statement. -/
theorem not_dSep_iff_hasActiveWalk (H : DAG V) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ¬ H.dSep X Y Z ↔ H.HasActiveWalk X Y Z := by
  unfold DAG.dSep DAG.HasActiveWalk
  constructor
  · intro hnot
    have hReach : ¬ Disjoint (H.bbReachableVertices Z X) Y := by
      intro hReach
      exact hnot ⟨hXY, hXZ, hYZ, hReach⟩
    rw [Finset.not_disjoint_iff] at hReach
    obtain ⟨v, hvR, hvY⟩ := hReach
    obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ :=
      (H.bbReachableVertices_iff_activeWalk X Z v).mp hvR
    exact ⟨p, hlen, hact, by rw [hhead]; exact Finset.mem_image_of_mem _ hxX,
      by rw [hlast]; exact Finset.mem_image_of_mem _ hvY⟩
  · rintro ⟨p, hlen, hact, hhead, hlast⟩ hsep
    obtain ⟨x, hxX, hx⟩ := Finset.mem_image.mp hhead
    obtain ⟨v, hvY, hv⟩ := Finset.mem_image.mp hlast
    have hvReach : v ∈ H.bbReachableVertices Z X := by
      rw [H.bbReachableVertices_iff_activeWalk]
      exact ⟨x, hxX, p, hlen, hact, by rw [hx], by rw [hv]⟩
    exact (Finset.disjoint_left.mp hsep.2.2.2 hvReach) hvY

/-- Graphs with the same directed edges have exactly the same ancestor relations. -/
theorem isAncestor_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {u v : V} :
    G₁.isAncestor u v ↔ G₂.isAncestor u v := by
  constructor
  · intro h
    induction h with
    | edge h => exact isAncestor.edge ((he _ _).mp h)
    | trans _ h ih => exact isAncestor.trans ih ((he _ _).mp h)
  · intro h
    induction h with
    | edge h => exact isAncestor.edge ((he _ _).mpr h)
    | trans _ h ih => exact isAncestor.trans ih ((he _ _).mpr h)

/-- Graphs with the same directed edges have exactly the same sets of vertices
    that are ancestors of the conditioning set and can activate colliders. -/
theorem bbZAncestors_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) (Z : Finset V) (v : V) :
    v ∈ G₁.bbZAncestors Z ↔ v ∈ G₂.bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hv | ⟨w, hw, h⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨w, hw, (isAncestor_edge_congr he).mp h⟩
  · rintro (hv | ⟨w, hw, h⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨w, hw, (isAncestor_edge_congr he).mpr h⟩

/-- Graphs with the same directed edges have exactly the same undirected adjacencies. -/
theorem uAdj_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {u v : V} :
    G₁.UAdj u v ↔ G₂.UAdj u v := by
  unfold UAdj
  exact or_congr (he u v) (he v u)

/-- Graphs with the same directed edges have exactly the same collider triples. -/
theorem isCollider_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {l m r : V} :
    G₁.IsCollider l m r ↔ G₂.IsCollider l m r := by
  unfold IsCollider
  exact and_congr (he l m) (he r m)

/-- Graphs with the same directed edges have exactly the same active walks for
    every conditioning set. -/
theorem isActiveWalk_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w)
    (Z : Finset V) (p : List V) :
    G₁.IsActiveWalk Z p ↔ G₂.IsActiveWalk Z p := by
  constructor
  · intro h
    obtain ⟨hadj, htri⟩ := h
    refine ⟨fun i hi => (uAdj_edge_congr he).mp (hadj i hi), fun i hi => ?_⟩
    let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hciff : G₁.IsCollider l m r ↔ G₂.IsCollider l m r := isCollider_edge_congr he
    have haiff : m ∈ G₁.bbZAncestors Z ↔ m ∈ G₂.bbZAncestors Z :=
      bbZAncestors_edge_congr he Z m
    have hval := htri i hi
    change (if G₁.IsCollider l m r then m ∈ G₁.bbZAncestors Z else m ∉ Z) at hval
    change (if G₂.IsCollider l m r then m ∈ G₂.bbZAncestors Z else m ∉ Z)
    by_cases hC : G₁.IsCollider l m r
    · rw [if_pos (hciff.mp hC), ← haiff]
      rwa [if_pos hC] at hval
    · have hC₂ : ¬ G₂.IsCollider l m r := fun h => hC (hciff.mpr h)
      rw [if_neg hC₂]
      rwa [if_neg hC] at hval
  · intro h
    obtain ⟨hadj, htri⟩ := h
    refine ⟨fun i hi => (uAdj_edge_congr he).mpr (hadj i hi), fun i hi => ?_⟩
    let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hciff : G₁.IsCollider l m r ↔ G₂.IsCollider l m r := isCollider_edge_congr he
    have haiff : m ∈ G₁.bbZAncestors Z ↔ m ∈ G₂.bbZAncestors Z :=
      bbZAncestors_edge_congr he Z m
    have hval := htri i hi
    change (if G₂.IsCollider l m r then m ∈ G₂.bbZAncestors Z else m ∉ Z) at hval
    change (if G₁.IsCollider l m r then m ∈ G₁.bbZAncestors Z else m ∉ Z)
    by_cases hC : G₂.IsCollider l m r
    · rw [if_pos (hciff.mpr hC), haiff]
      rwa [if_pos hC] at hval
    · have hC₁ : ¬ G₁.IsCollider l m r := fun h => hC (hciff.mp h)
      rw [if_neg hC₁]
      rwa [if_neg hC] at hval

/-- Equal directed-edge relations preserve existence of active walks. -/
theorem hasActiveWalk_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) (X Y Z : Finset V) :
    G₁.HasActiveWalk X Y Z ↔ G₂.HasActiveWalk X Y Z := by
  constructor
  · rintro ⟨p, hlen, hact, hhead, hlast⟩
    exact ⟨p, hlen, (isActiveWalk_edge_congr he Z p).mp hact, hhead, hlast⟩
  · rintro ⟨p, hlen, hact, hhead, hlast⟩
    exact ⟨p, hlen, (isActiveWalk_edge_congr he Z p).mpr hact, hhead, hlast⟩

/-- In the flipped graph, the reversed edge `b → a` is covered. -/
theorem flipEdge_isCoveredEdge_back {a b : V} (hcov : G.IsCoveredEdge a b) :
    (flipEdge hcov).IsCoveredEdge b a := by
  constructor
  · rw [flipEdge_edge]
    exact Or.inr ⟨rfl, rfl⟩
  · intro c hcb
    by_cases hca : c = a
    · subst c
      rw [flipEdge_edge, flipEdge_edge]
      constructor
      · rintro (⟨_, hnot⟩ | ⟨hab, _⟩)
        · exact absurd ⟨rfl, rfl⟩ hnot
        · exact absurd hab hcov.ne
      · rintro (⟨haa, _⟩ | ⟨hab, _⟩)
        · exact absurd haa (G.irrefl a)
        · exact absurd hab hcov.ne
    · rw [flipEdge_edge, flipEdge_edge]
      constructor
      · rintro (⟨hcbG, _⟩ | ⟨hcb', _⟩)
        · left
          refine ⟨(hcov.2 c hca).mpr hcbG, ?_⟩
          rintro ⟨hca', _⟩
          exact hca hca'
        · exact absurd hcb' hcb
      · rintro (⟨hcaG, _⟩ | ⟨hcb', _⟩)
        · left
          refine ⟨(hcov.2 c hca).mp hcaG, ?_⟩
          rintro ⟨hca', _⟩
          exact hca hca'
        · exact absurd hcb' hcb

/-- Flipping the reversed covered edge restores the original edge relation. -/
theorem flipEdge_flipEdge_edge {a b : V} (hcov : G.IsCoveredEdge a b) :
    ∀ u w : V, (flipEdge (flipEdge_isCoveredEdge_back hcov)).edge u w ↔ G.edge u w := by
  intro u w
  rw [flipEdge_edge, flipEdge_edge]
  constructor
  · rintro (h | ⟨hub, hwa⟩)
    · rcases h with ⟨h, hnot⟩
      rcases h with ⟨hG, hnot_ab⟩ | ⟨hub, hwa⟩
      · exact hG
      · exact absurd ⟨hub, hwa⟩ hnot
    · subst hub; subst hwa
      exact hcov.1
  · intro hG
    by_cases hab : u = a ∧ w = b
    · obtain ⟨rfl, rfl⟩ := hab
      exact Or.inr ⟨rfl, rfl⟩
    · left
      refine ⟨Or.inl ⟨hG, hab⟩, ?_⟩
      rintro ⟨hub, hwa⟩
      subst hub; subst hwa
      exact G.asymm hcov.1 hG

/-- If one node is a strict ancestor of another in a directed acyclic graph,
then it either has a direct edge to the latter or is a strict ancestor of a
node that has a direct edge to the latter. -/
theorem isAncestor_last {H : DAG V} {u v : V} (h : H.isAncestor u v) :
    H.edge u v ∨ ∃ w, H.isAncestor u w ∧ H.edge w v := by
  induction h with
  | edge he => exact Or.inl he
  | trans h₁ he _ => exact Or.inr ⟨_, h₁, he⟩

/-- Any flipped ancestor of `a`, except `b` itself, can be rerouted to an ancestor of `b`. -/
private theorem isAncestor_flip_to_b {a b v : V} (hcov : G.IsCoveredEdge a b)
    (hvb : v ≠ b) :
    (flipEdge hcov).isAncestor v a → (flipEdge hcov).isAncestor v b := by
  intro h
  rcases isAncestor_last h with hdir | ⟨q, hvq, hqa⟩
  · rw [flipEdge_edge] at hdir
    rcases hdir with ⟨hvaG, _⟩ | ⟨hvb', _⟩
    · have hva : v ≠ a := fun hv => G.irrefl a (hv ▸ hvaG)
      have hvbG : G.edge v b := (hcov.2 v hva).mp hvaG
      exact isAncestor.edge (by
        rw [flipEdge_edge]
        exact Or.inl ⟨hvbG, fun hab => hva hab.1⟩)
    · exact absurd hvb' hvb
  · rw [flipEdge_edge] at hqa
    rcases hqa with ⟨hqaG, _⟩ | ⟨hqb, _⟩
    · have hqne : q ≠ a := fun hq => G.irrefl a (hq ▸ hqaG)
      have hqbG : G.edge q b := (hcov.2 q hqne).mp hqaG
      exact isAncestor.trans hvq (by
        rw [flipEdge_edge]
        exact Or.inl ⟨hqbG, fun hab => hqne hab.1⟩)
    · subst hqb
      exact hvq

/-- Under a covered reversal of the edge from `a` to `b`, every directed edge of the original
    graph either remains an edge or is the deleted edge from `a` to `b`. -/
theorem flipEdge_edge_or_deleted {a b u w : V} (hcov : G.IsCoveredEdge a b)
    (he : G.edge u w) : (flipEdge hcov).edge u w ∨ (u = a ∧ w = b) := by
  by_cases hab : u = a ∧ w = b
  · exact Or.inr hab
  · exact Or.inl (by
      rw [flipEdge_edge]
      exact Or.inl ⟨he, hab⟩)

/-- A `G`-ancestor path whose start is not `a` survives the covered flip, rerouting only
the deleted `a → b` step through the shared parents. -/
private theorem isAncestor_flip {a b s z : V} (hcov : G.IsCoveredEdge a b)
    (hsa : s ≠ a) (h : G.isAncestor s z) :
    (flipEdge hcov).isAncestor s z := by
  induction h with
  | edge he =>
      rcases flipEdge_edge_or_deleted hcov he with hF | hdel
      · exact isAncestor.edge hF
      · exact absurd hdel.1 hsa
  | trans h₁ he ih =>
      rcases flipEdge_edge_or_deleted hcov he with hF | hdel
      · exact isAncestor.trans ih hF
      · have hsaAnc : G.isAncestor s a := by
          simpa [hdel.1] using h₁
        have ihA : (flipEdge hcov).isAncestor s a := by
          simpa [hdel.1] using ih
        have hsb : s ≠ b := by
          intro hsb
          have hba : G.topoOrder s < G.topoOrder a := G.isAncestor_topoOrder_lt hsaAnc
          have hab : G.topoOrder a < G.topoOrder b := G.topoOrder_lt _ _ hcov.1
          rw [hsb] at hba
          omega
        simpa [hdel.2] using isAncestor_flip_to_b hcov hsb ihA

/-- If a vertex other than the reversed tail belongs to the Bayes-ball ancestor closure of a
    conditioning set before a covered reversal, it belongs to that closure after the reversal. -/
theorem bbZAncestors_flip_of_ne {a b v : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (hva : v ≠ a) :
    v ∈ G.bbZAncestors Z → v ∈ (flipEdge hcov).bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rintro (hvZ | ⟨z, hzZ, hvz⟩)
  · exact Or.inl hvZ
  · exact Or.inr ⟨z, hzZ, isAncestor_flip hcov hva hvz⟩

/-- The vertex `b` keeps its Bayes-ball ancestor-set membership after flipping `a → b`. -/
theorem bbZAncestors_flip_of_b {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) :
    b ∈ G.bbZAncestors Z → b ∈ (flipEdge hcov).bbZAncestors Z :=
  bbZAncestors_flip_of_ne hcov Z hcov.ne.symm

/-- If `a` reaches `Z` in `G` but not after the flip, that route used `a → b`, so `b` reaches
`Z`; hence `b` is activated in the flipped graph. -/
theorem bbZAncestors_flip_of_lost {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (h1 : a ∈ G.bbZAncestors Z) (h2 : a ∉ (flipEdge hcov).bbZAncestors Z) :
    b ∈ (flipEdge hcov).bbZAncestors Z := by
  apply bbZAncestors_flip_of_b hcov Z
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at h1 ⊢
  have hmemflip : ∀ {w : V}, (∃ z ∈ Z, (flipEdge hcov).isAncestor w z) →
      w ∈ (flipEdge hcov).bbZAncestors Z := by
    intro w hw
    simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr hw
  have haZ : a ∉ Z := fun h => h2 (hmemflip ⟨a, h, isAncestor.edge (by
    rw [flipEdge_edge]; exact Or.inr ⟨rfl, rfl⟩)⟩ |> fun _ => by
    simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact Or.inl h)
  rcases h1 with hZ | ⟨z, hzZ, haz⟩
  · exact absurd hZ haZ
  · rcases G.isAncestor_child haz with hedge | ⟨c, hac, hcz⟩
    · by_cases hzb : z = b
      · exact Or.inl (hzb ▸ hzZ)
      · exact absurd (hmemflip ⟨z, hzZ, isAncestor.edge (by
          rw [flipEdge_edge]; exact Or.inl ⟨hedge, fun h => hzb h.2⟩)⟩) h2
    · by_cases hcb : c = b
      · subst hcb; exact Or.inr ⟨z, hzZ, hcz⟩
      · have hca : c ≠ a := fun h => G.irrefl a (h ▸ hac)
        have hacF : (flipEdge hcov).edge a c := by
          rw [flipEdge_edge]; exact Or.inl ⟨hac, fun h => hcb h.2⟩
        exact absurd (hmemflip ⟨z, hzZ,
          (flipEdge hcov).isAncestor_trans (isAncestor.edge hacF)
            (isAncestor_flip hcov hca hcz)⟩) h2

/-- Away from `b`, Bayes-ball ancestor membership in the flipped graph transports back to `G`. -/
private theorem bbZAncestors_unflip_of_ne {a b v : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (hvb : v ≠ b) :
    v ∈ (flipEdge hcov).bbZAncestors Z → v ∈ G.bbZAncestors Z := by
  have hback := flipEdge_isCoveredEdge_back hcov
  intro hv
  have hv₂ : v ∈ (flipEdge hback).bbZAncestors Z :=
    bbZAncestors_flip_of_ne (G := flipEdge hcov) hback Z hvb hv
  exact (bbZAncestors_edge_congr (flipEdge_flipEdge_edge hcov) Z v).mp hv₂

/-- Away from `a`, the covered flip leaves directed edges unchanged. -/
theorem flipEdge_edge_iff_of_ne_a {a b u w : V} (hcov : G.IsCoveredEdge a b)
    (hua : u ≠ a) (hwa : w ≠ a) :
    (flipEdge hcov).edge u w ↔ G.edge u w := by
  rw [flipEdge_edge]
  constructor
  · rintro (⟨he, _⟩ | ⟨_, hwa'⟩)
    · exact he
    · exact absurd hwa' hwa
  · intro he
    exact Or.inl ⟨he, fun hdel => hua hdel.1⟩

/-- Away from `a`, the covered flip leaves collider status unchanged. -/
private theorem flipEdge_isCollider_iff_of_ne_a {a b l m r : V}
    (hcov : G.IsCoveredEdge a b) (hla : l ≠ a) (hma : m ≠ a) (hra : r ≠ a) :
    (flipEdge hcov).IsCollider l m r ↔ G.IsCollider l m r := by
  unfold IsCollider
  exact and_congr (flipEdge_edge_iff_of_ne_a hcov hla hma)
    (flipEdge_edge_iff_of_ne_a hcov hra hma)

/-- For [a DAG, edge endpoints, conditioning set, and walk](hyp:V,G,a,b,Z,p), if
[the edge is covered](hyp:hcov), [the walk is active](hyp:hact), and
[the walk omits the reversed edge's tail](hyp:hna), then
[that walk remains active after the covered reversal](goal).

A walk that is active relative to a conditioning set and does not contain the tail of a
covered reversed edge remains active relative to the same set after the reversal. -/
theorem isActiveWalk_flip_of_not_mem {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActiveWalk Z p) (hna : a ∉ p) :
    (flipEdge hcov).IsActiveWalk Z p := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · exact (flipEdge_sameSkeleton hcov _ _).mp (hadj i hi)
  · let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hla : l ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i, by omega⟩
    have hma : m ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i + 1, by omega⟩
    have hra : r ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i + 2, hi⟩
    have hciff : (flipEdge hcov).IsCollider l m r ↔ G.IsCollider l m r :=
      flipEdge_isCollider_iff_of_ne_a hcov hla hma hra
    have hval := htri i hi
    change (if G.IsCollider l m r then m ∈ G.bbZAncestors Z else m ∉ Z) at hval
    change (if (flipEdge hcov).IsCollider l m r
      then m ∈ (flipEdge hcov).bbZAncestors Z else m ∉ Z)
    by_cases hC : G.IsCollider l m r
    · rw [if_pos ((hciff).mpr hC)]
      exact bbZAncestors_flip_of_ne hcov Z hma (by rwa [if_pos hC] at hval)
    · have hCF : ¬ (flipEdge hcov).IsCollider l m r := fun h => hC ((hciff).mp h)
      rw [if_neg hCF]
      rwa [if_neg hC] at hval

/-- Walks with no interior triple transfer across the covered flip by skeleton preservation. -/
private theorem isActiveWalk_flip_of_length_le_two {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActiveWalk Z p) (hlen : p.length ≤ 2) :
    (flipEdge hcov).IsActiveWalk Z p := by
  obtain ⟨hadj, _htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · exact (flipEdge_sameSkeleton hcov _ _).mp (hadj i hi)
  · omega

/-- The walk `p` with each interior **collider** occurrence of `a` whose activation is lost in
the flipped graph (`a ∉ (flipEdge).bbZAncestors Z`) replaced by `b`. Same length as `p`;
endpoints are never touched (they are not interior). -/
noncomputable def swapPath {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : List V :=
  List.ofFn (fun i : Fin p.length =>
    if h : 1 ≤ i.val ∧ i.val + 1 < p.length then
      if p.get i = a ∧ a ∉ (flipEdge hcov).bbZAncestors Z ∧
          G.IsCollider (p.get ⟨i.val - 1, by have := i.isLt; omega⟩) (p.get i)
            (p.get ⟨i.val + 1, h.2⟩)
        then b else p.get i
    else p.get i)

/-- For
[a directed acyclic graph, a covered edge, a conditioning set, and a walk](hyp:V,G,a,b,hcov,Z,p),
[replacing affected collider occurrences along the walk preserves its length](goal). -/
@[simp] theorem swapPath_length {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (p : List V) : (swapPath hcov Z p).length = p.length := by
  simp [swapPath]

/-- Each entry of `swapPath` is either the original vertex, or `b` at an interior collider
occurrence of `a` whose activation is lost. -/
theorem swapPath_get_eq {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) (i : ℕ) (hi : i < (swapPath hcov Z p).length) (hi' : i < p.length) :
    (swapPath hcov Z p).get ⟨i, hi⟩ = p.get ⟨i, hi'⟩ ∨
      ((swapPath hcov Z p).get ⟨i, hi⟩ = b ∧ p.get ⟨i, hi'⟩ = a ∧
        1 ≤ i ∧ ∃ (h2 : i + 1 < p.length),
          G.IsCollider (p.get ⟨i - 1, by omega⟩) (p.get ⟨i, hi'⟩) (p.get ⟨i + 1, h2⟩) ∧
          a ∉ (flipEdge hcov).bbZAncestors Z) := by
  simp only [swapPath, List.get_ofFn, Fin.cast_mk]
  split_ifs with h hc
  · exact Or.inr ⟨rfl, hc.1, h.1, h.2, hc.2.2, hc.2.1⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- When the swap predicate holds at `i`, the entry is `b`. -/
theorem swapPath_get_b_of {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) (i : ℕ) (hi : i < (swapPath hcov Z p).length) (hi' : i < p.length)
    (h1 : 1 ≤ i) (h2 : i + 1 < p.length) (ha : p.get ⟨i, hi'⟩ = a)
    (hanc : a ∉ (flipEdge hcov).bbZAncestors Z)
    (hcol : G.IsCollider (p.get ⟨i - 1, by omega⟩) (p.get ⟨i, hi'⟩) (p.get ⟨i + 1, h2⟩)) :
    (swapPath hcov Z p).get ⟨i, hi⟩ = b := by
  simp only [swapPath, List.get_ofFn, Fin.cast_mk]
  rw [dif_pos ⟨h1, h2⟩, if_pos ⟨ha, hanc, hcol⟩]

/-- An edge **into** a vertex `m ∉ {a, b}` is unaffected by the flip. -/
theorem flipEdge_edge_into_iff {a b m : V} (hcov : G.IsCoveredEdge a b)
    (hma : m ≠ a) (hmb : m ≠ b) (u : V) :
    (flipEdge hcov).edge u m ↔ G.edge u m := by
  rw [flipEdge_edge]
  refine ⟨fun h => h.elim (·.1) (fun hh => absurd hh.2 hma),
    fun h => Or.inl ⟨h, fun hh => hmb hh.2⟩⟩

/-- The `(l, m, r)` configurations that the covered flip turns into an *un-repairable* block.
Each is an `a`/`b` adjacency whose far arrowhead either makes `a` an **inactive** collider after
the flip (clauses 1–2) or destroys the **active** collider at `b` (clauses 3–4). The two
backtracks `b — a — b` and `a — b — a` are special cases (the first via clause 1 with `r = b`,
the second via clause 4 with `l = a`, since `a → b`). `swapPath` cannot repair these locally;
the assembly removes them by dropping/excising one vertex before swapping. -/
def FlipObstruct (a b l m r : V) : Prop :=
  (m = a ∧ l = b ∧ (G.edge r a ∨ r = b)) ∨
  (m = a ∧ r = b ∧ (G.edge l a ∨ l = b)) ∨
  (m = b ∧ l = a ∧ G.edge r b) ∨
  (m = b ∧ r = a ∧ G.edge l b)

/-- Ancestor-set membership moves backwards along a directed edge. -/
theorem bbZAncestors_of_edge {Z : Finset V} {u w : V}
    (huw : G.edge u w) (hw : w ∈ G.bbZAncestors Z) :
    u ∈ G.bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with hwZ | ⟨z, hzZ, hwz⟩
  · exact Or.inr ⟨w, hwZ, isAncestor.edge huw⟩
  · exact Or.inr ⟨z, hzZ, G.isAncestor_trans (isAncestor.edge huw) hwz⟩

/-- [A list of values and an index](hyp:V,p,k) determine [the list of length one less whose
entries before the index are unchanged and whose later entries are shifted forward by one](goal).

It is defined by `ofFn` so its indexing equations are definitional after `simp`. -/
def skipOne (p : List V) (k : ℕ) : List V :=
  List.ofFn (fun i : Fin (p.length - 1) =>
    if h : i.val < k then
      p.get ⟨i.val, by omega⟩
    else
      p.get ⟨i.val + 1, by omega⟩)

omit [DecidableEq V] [Fintype V] in
/-- For [a list of values and an index](hyp:V,p,k),
[skipping one entry reduces the length by one](goal). -/
@[simp] theorem skipOne_length (p : List V) (k : ℕ) :
    (skipOne p k).length = p.length - 1 := by
  simp [skipOne]

/-- [A list of values and an index](hyp:V,p,k) determine [the list of length two less whose
entries before the index are unchanged and whose later entries are shifted forward by two](goal). -/
def skipTwo (p : List V) (k : ℕ) : List V :=
  List.ofFn (fun i : Fin (p.length - 2) =>
    if h : i.val < k then
      p.get ⟨i.val, by omega⟩
    else
      p.get ⟨i.val + 2, by omega⟩)

omit [DecidableEq V] [Fintype V] in
/-- For [a list of values and an index](hyp:V,p,k),
[skipping two entries reduces the length by two](goal). -/
@[simp] theorem skipTwo_length (p : List V) (k : ℕ) :
    (skipTwo p k).length = p.length - 2 := by
  simp [skipTwo]

omit [DecidableEq V] [Fintype V] in
/-- If [an index is positive](hyp:hk0) and [lies within a list of values](hyp:V,p,k,hk), then
[skipping that entry preserves the first entry](goal). -/
theorem skipOne_head? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k < p.length) :
    (skipOne p k).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  have hp0 : 0 < p.length := by omega
  have hq0 : 0 < (skipOne p k).length := by simp [skipOne_length]; omega
  rw [List.getElem?_eq_getElem hq0, List.getElem?_eq_getElem hp0]
  simp [skipOne, hk0]

omit [DecidableEq V] [Fintype V] in
/-- If [an index and its successor lie before the end of a list of values](hyp:V,p,k,hk), then
[skipping that entry preserves the last entry](goal). -/
theorem skipOne_getLast? {p : List V} {k : ℕ} (hk : k + 1 < p.length) :
    (skipOne p k).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, skipOne_length]
  have hp0 : 0 < p.length := by omega
  rw [List.getElem?_eq_getElem (by rw [skipOne_length]; omega),
    List.getElem?_eq_getElem (by omega)]
  have hnot : ¬ (p.length - 1 - 1 < k) := by omega
  simp [skipOne, hnot, show p.length - 1 - 1 + 1 = p.length - 1 by omega]

omit [DecidableEq V] [Fintype V] in
/-- If
[an index is positive and its successor lies before the end of a list of values](hyp:V,p,k,hk0,hk),
then [skipping the two entries beginning there preserves the first entry](goal). -/
theorem skipTwo_head? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k + 1 < p.length) :
    (skipTwo p k).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  have hp0 : 0 < p.length := by omega
  have hq0 : 0 < (skipTwo p k).length := by simp [skipTwo_length]; omega
  rw [List.getElem?_eq_getElem hq0, List.getElem?_eq_getElem hp0]
  simp [skipTwo, hk0]

omit [DecidableEq V] [Fintype V] in
/-- If [a positive index and its successor lie before the end of a list of values](hyp:V,p,k,hk0,hk)
and [the entries immediately before and after the index agree](hyp:hsame), then [skipping the two
entries beginning at the index preserves the last entry](goal). -/
theorem skipTwo_getLast? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k + 1 < p.length)
    (hsame : p.get ⟨k - 1, by omega⟩ = p.get ⟨k + 1, hk⟩) :
    (skipTwo p k).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, skipTwo_length]
  have hp0 : 0 < p.length := by omega
  rw [List.getElem?_eq_getElem (by rw [skipTwo_length]; omega),
    List.getElem?_eq_getElem (by omega)]
  by_cases htail : k + 2 < p.length
  · have hnot : ¬ (p.length - 2 - 1 < k) := by omega
    simp [skipTwo, hnot, show p.length - 2 - 1 + 2 = p.length - 1 by omega]
  · have hk_last : k + 1 = p.length - 1 := by omega
    have hq_last : p.length - 2 - 1 = k - 1 := by omega
    have htrue : k - 1 < k := by omega
    simpa [skipTwo, hq_last, hk_last, htrue] using hsame

end DAG

end Causalean.Graph

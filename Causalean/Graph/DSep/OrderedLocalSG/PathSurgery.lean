/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DSep.Ancestral
public import Causalean.Graph.DSep.OrderedLocalSG.Defs

/-! # Walk surgery for the ordered-local peel

This file proves the d-separation and active-walk transformations used when the
ordered-local induction removes a topologically maximal vertex. The results cover
parent inheritance, erasing a maximal random conditioning vertex, changing a walk's
conditioning set, orienting its final edge, and joining walks at a conditioned collider.
-/

public section

namespace Causalean.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- § 3. d-separation surgery lemmas for the peel
-- ============================================================

/-- In [a finite directed acyclic graph](hyp:V,G), if [a vertex, target set, and
conditioning set](hyp:n,Y,D) satisfy
[d-separation of the vertex from the target](hyp:hdSep), then [the vertex's parents are
disjoint from the target set](goal). -/
theorem parents_disjoint_of_dSep_singleton {n : V} {Y D : Finset V}
    (hdSep : G.dSep {n} Y D) : Disjoint (G.parents n) Y := by
  rw [Finset.disjoint_left]
  intro a haPar haY
  -- The walk `[n, a]` is active given `D` (no interior vertex), from `n` to `a ∈ Y`.
  have hedge : G.edge a n := G.mem_parents.mp haPar
  have hact : G.IsActiveWalk D [n, a] := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · -- length 2 ⟹ i = 0; the only adjacency is `UAdj n a`, from `edge a n`.
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact Or.inr (by simpa using hedge)
    · -- length 2 ⟹ no interior triple
      simp only [List.length_cons, List.length_nil] at hi
      omega
  have hmem : a ∈ G.bbReachableVertices D {n} := by
    rw [G.bbReachableVertices_iff_activeWalk]
    exact ⟨n, Finset.mem_singleton_self n, [n, a], by simp, hact, rfl, rfl⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 hmem) haY

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a source vertex, target
set, conditioning set, and selected parent set](hyp:n,Y,D,A0). If [the source is
d-separated from the target](hyp:hdSep), [every selected vertex is a parent of the
source](hyp:hA0_par), and [none is conditioned on](hyp:hA0_D), then [the selected parents
are d-separated from the target under the same conditioning set](goal).

    Graphically: an active `a → … → Y` walk can be prepended with the edge
    `a → n` (giving `n, a, …, Y`); the new interior vertex `a` is a non-collider
    there (`a → n`, not `n → a`), and `a ∉ D`, so the extended walk is active from
    `n` to `Y`, contradicting `dSep {n} Y D`. -/
theorem dSep_parents_of_maximal_source {n : V} {Y D A0 : Finset V}
    (hdSep : G.dSep {n} Y D)
    (hA0_par : ∀ a ∈ A0, G.edge a n)
    (hA0_D : ∀ a ∈ A0, a ∉ D) :
    G.dSep A0 Y D := by
  refine ⟨?_, ?_, hdSep.2.2.1, ?_⟩
  · exact (G.parents_disjoint_of_dSep_singleton hdSep).mono_left (by
      intro a ha
      exact G.mem_parents.mpr (hA0_par a ha))
  · exact Finset.disjoint_left.mpr hA0_D
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  -- Extract an active walk `a → … → y` for some `a ∈ A0`.
  rw [G.bbReachableVertices_iff_activeWalk] at hyReach
  obtain ⟨a, haA0, p, hlen, hact, hhead, hlast⟩ := hyReach
  -- `p` has length ≥ 2 and head `a`, so `p = a :: u :: r`.
  obtain ⟨u, r, hp⟩ : ∃ u r, p = a :: u :: r := by
    match p, hlen, hhead with
    | _ :: u :: r, _, hhead =>
        exact ⟨u, r, by simp only [List.head?_cons, Option.some_inj] at hhead; subst hhead; rfl⟩
  subst hp
  -- Prepend `n` via the edge `a → n`; `a` is a non-collider in `(n, a, u)`.
  have hedge : G.edge a n := hA0_par a haA0
  have hnotcoll : ¬ G.IsCollider n a u := fun hC => G.asymm hedge hC.1
  have htri : (if G.IsCollider n a u then a ∈ G.bbZAncestors D else a ∉ D) := by
    rw [if_neg hnotcoll]; exact hA0_D a haA0
  have hact' : G.IsActiveWalk D (n :: a :: u :: r) :=
    G.isActiveWalk_cons_of_active_triple (Or.inr hedge) htri hact
  -- This new active walk witnesses `y ∈ bbReachableVertices D {n}`, contradiction.
  have hyReach' : y ∈ G.bbReachableVertices D {n} := by
    rw [G.bbReachableVertices_iff_activeWalk]
    refine ⟨n, Finset.mem_singleton_self n, n :: a :: u :: r, by simp, hact', rfl, ?_⟩
    simpa using hlast
  exact (Finset.disjoint_left.mp hdSep.2.2.2 hyReach') hyY

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a conditioning set, walk,
and added vertex](hyp:D,p,n). If [the walk is active](hyp:hact) and [the added vertex can
occur internally only as a collider](hyp:hno), then [the walk remains active after that
vertex is added to the conditioning set](goal).

    If `p` is active
    given `D` and `n` never sits as a *non-collider* on `p`, then `p` stays active
    given `insert n D`: adding `n` to the conditioning set can only widen collider
    activation (the ancestral set grows) and the only non-collider it could block
    is `n` itself, which is excluded by hypothesis. -/
theorem isActiveWalk_insert_cond {D : Finset V} {p : List V} {n : V}
    (hact : G.IsActiveWalk D p)
    (hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)) :
    G.IsActiveWalk (insert n D) p := by
  obtain ⟨hadj, hcoll⟩ := hact
  refine ⟨hadj, fun i hi => ?_⟩
  have hval := hcoll i hi
  simp only at hval ⊢
  set l := p.get ⟨i, by omega⟩
  set m := p.get ⟨i + 1, by omega⟩
  set r := p.get ⟨i + 2, hi⟩
  by_cases hC : G.IsCollider l m r
  · rw [if_pos hC] at hval ⊢
    exact (G.ancestralSet_mono (Finset.subset_insert n D)) hval
  · rw [if_neg hC] at hval ⊢
    rw [Finset.mem_insert, not_or]
    refine ⟨fun hmn => hC (hno i hi hmn), hval⟩

/-- For [a finite directed acyclic graph, two endpoint sets, random and fixed conditioning sets,
and a selected vertex](hyp:V,G,X,Y,Zr,Zf,n), if [the vertex belongs to the random conditioning
set](hyp:hnZr), [it is topologically maximal in the ancestral closure of the query](hyp:hmax),
and [the endpoint sets are d-separated by the full conditioning set](hyp:hdSep), then [erasing
that vertex from the random conditioning set preserves the d-separation](goal).

**A maximal random conditioning node can be dropped.** If `n ∈ Zr` is the
    topological maximum of the query's ancestral set, then deleting it from the
    conditioning set preserves d-separation of `X` and `Y`.

    Graphically: since `n` is topologically maximal among all ancestors of
    `X ∪ Y ∪ Zr ∪ Zf`, no proper descendant of `n` lies in that ancestral set, so
    on every active `X → Y` walk the node `n` (if present) can only be a collider,
    and that collider is activated solely by `n` itself. Removing `n` from the
    conditioning set therefore closes every active walk through `n` and creates none. -/
theorem dSep_erase_maximal_random_condition {X Y Zr Zf : Finset V} {n : V}
    (hnZr : n ∈ Zr)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.dSep X Y ((Zr.erase n) ∪ Zf) := by
  refine ⟨hdSep.1, ?_, ?_, ?_⟩
  · exact hdSep.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz)
  · exact hdSep.2.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz)
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  -- Active walk `p : x → y` given `Z' ∪ Zf`.
  rw [G.bbReachableVertices_iff_activeWalk] at hyReach
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hyReach
  -- Every node of `p` lies in `ancestralSet Q` (Q = X∪Y∪Zr∪Zf).
  have hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf) := by
    intro v hv
    have := G.activeWalk_nodes_are_ancestors hxX hyY hact hhead hlast v hv
    refine G.ancestralSet_mono ?_ this
    intro z hz
    simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
    rcases hz with (h | h) | h | h
    exacts [Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inl (Or.inr h)),
      Or.inl (Or.inr h.2), Or.inr h]
  -- `n` is never a non-collider on `p` (it would force a strictly-larger node).
  have hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hadj_lm := hadj i (by omega)
    have hadj_mr := hadj (i + 1) (by omega)
    -- Outgoing edge from `m = n` to a path neighbour.
    have hout := G.nonCollider_has_outgoing hadj_lm hadj_mr hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have hAnc := hpAnc _ (List.get_mem p ⟨i, by omega⟩)
      have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
    · have hAnc := hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩)
      have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
  -- Hence `p` is active given `insert n (Z' ∪ Zf) = Zr ∪ Zf`, contradicting `hdSep`.
  have hact' : G.IsActiveWalk (insert n (Zr.erase n ∪ Zf)) p :=
    G.isActiveWalk_insert_cond hact hno
  have hins : insert n (Zr.erase n ∪ Zf) = Zr ∪ Zf := by
    ext z; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | (⟨_, h⟩ | h) )
      exacts [Or.inl hnZr, Or.inl h, Or.inr h]
    · rintro (h | h)
      · by_cases hz : z = n
        · exact Or.inl hz
        · exact Or.inr (Or.inl ⟨hz, h⟩)
      · exact Or.inr (Or.inr h)
  rw [hins] at hact'
  have : y ∈ G.bbReachableVertices (Zr ∪ Zf) X := by
    rw [G.bbReachableVertices_iff_activeWalk]
    exact ⟨x, hxX, p, hlen, hact', hhead, hlast⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 this) hyY

/-- In [a finite directed acyclic graph](hyp:V,G), consider [conditioning sets, a walk,
and an added vertex](hyp:S,W,p,n). If [the walk is active under both sets](hyp:hact),
[every interior collider is activated by the first set](hyp:hcollS), and
[the added vertex can occur internally only as a collider](hyp:hno_n), then [the walk is
active when only the first set and added vertex are conditioned on](goal). -/
theorem lift_crosscond_to_insert {S W : Finset V} {p : List V} {n : V}
    (hact : G.IsActiveWalk (S ∪ W) p)
    (hcollS : ∀ (i : ℕ) (hi : i + 2 < p.length),
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) →
      p.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S)
    (hno_n : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)) :
    G.IsActiveWalk (insert n S) p := by
  obtain ⟨hadj, hcoll⟩ := hact
  refine ⟨hadj, fun i hi => ?_⟩
  have hval := hcoll i hi
  simp only at hval ⊢
  set l := p.get ⟨i, by omega⟩ with hl
  set m := p.get ⟨i + 1, by omega⟩ with hm
  set r := p.get ⟨i + 2, hi⟩ with hr
  by_cases hC : G.IsCollider l m r
  · rw [if_pos hC] at hval ⊢
    show m ∈ G.bbZAncestors (insert n S)
    exact (G.ancestralSet_mono (Finset.subset_insert n S)) (hcollS i hi hC)
  · rw [if_neg hC] at hval ⊢
    rw [Finset.mem_insert, not_or]
    refine ⟨fun hmn => hC (hno_n i hi hmn), fun hmS => hval (Finset.mem_union_left _ hmS)⟩

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a conditioning set,
ancestral seed, active walk, and selected endpoint](hyp:D,bigQ,p,n). If [the walk is
nontrivial](hyp:hp_len), [is active](hyp:hact), [ends at the selected vertex](hyp:hlast),
[lies in the seed's ancestral closure](hyp:hpAnc), and [the endpoint maximizes topological
order there](hyp:hmax), then [the walk's final edge points into that endpoint](goal). -/
theorem last_edge_into_max
    {D bigQ : Finset V} {p : List V} {n : V}
    (hp_len : p.length ≥ 2) (hact : G.IsActiveWalk D p) (hlast : p.getLast? = some n)
    (hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet bigQ)
    (hmax : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n) :
    G.edge (p.get ⟨p.length - 2, by omega⟩) n := by
  -- The last adjacency is between `p[len-2]` and `p[len-1] = n`.
  have hadj := hact.1 (p.length - 2) (by omega)
  have hlast_get : p.get ⟨p.length - 2 + 1, by omega⟩ = n := by
    have hpne : p ≠ [] := by intro h; rw [h] at hp_len; simp at hp_len
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h
    have hn_eq : p.getLast hpne = n := Option.some_inj.mp h.symm
    have hidx : (⟨p.length - 2 + 1, by omega⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
      Fin.ext (show p.length - 2 + 1 = p.length - 1 by omega)
    rw [hidx, List.get_eq_getElem, ← hn_eq, List.getLast_eq_getElem]
  rw [hlast_get] at hadj
  -- `hadj : UAdj p[len-2] n`. Rule out `edge n p[len-2]` by topo-maximality.
  rcases hadj with hin | hout
  · exact hin
  · exfalso
    have hAnc := hpAnc _ (List.get_mem p ⟨p.length - 2, by omega⟩)
    have h1 : G.topoOrder (p.get ⟨p.length - 2, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
    have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hout)
    omega

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a conditioning set,
joining vertex, endpoints, and two walks](hyp:Z,n,x,y,pa,pb). If [the first walk is active
from the first endpoint to the join](hyp:hpa_len,hpa_head,hpa_last,hpa_act), [the second
is active from the join to the second endpoint](hyp:hpb_len,hpb_head,hpb_last,hpb_act),
[both seam edges point into the join](hyp:hpa_in,hpb_in), and [the joining vertex is
conditioned on](hyp:hnZ), then [concatenating the walks gives an active walk between the
endpoints](goal). -/
theorem activeWalk_join_at_collider
    {Z : Finset V} {n x y : V} {pa pb : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some x)
    (hpa_last : pa.getLast? = some n) (hpa_act : G.IsActiveWalk Z pa)
    (hpb_len : pb.length ≥ 2) (hpb_head : pb.head? = some n)
    (hpb_last : pb.getLast? = some y) (hpb_act : G.IsActiveWalk Z pb)
    (hpa_in : G.edge (pa.get ⟨pa.length - 2, by omega⟩) n)
    (hpb_in : G.edge (pb.get ⟨1, by omega⟩) n)
    (hnZ : n ∈ Z) :
    let p := pa ++ pb.tail
    p.length ≥ 2 ∧ p.head? = some x ∧ p.getLast? = some y ∧
      G.IsActiveWalk Z p := by
  have hpa_ne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
  have hpb_ne : pb ≠ [] := by intro h; rw [h] at hpb_len; simp at hpb_len
  -- pb.head = n
  have hpb_head_eq : pb.head hpb_ne = n := by
    have h := List.head?_eq_some_head hpb_ne; rw [hpb_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.getLast = n
  have hpa_last_eq : pa.getLast hpa_ne = n := by
    have h := List.getLast?_eq_some_getLast hpa_ne; rw [hpa_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.head = x
  have hpa_head_eq : pa.head hpa_ne = x := by
    have h := List.head?_eq_some_head hpa_ne; rw [hpa_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pb.getLast = y
  have hpb_last_eq : pb.getLast hpb_ne = y := by
    have h := List.getLast?_eq_some_getLast hpb_ne; rw [hpb_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pb = n :: pb.tail
  have hpb_decomp : pb = n :: pb.tail := by
    conv_lhs => rw [← List.cons_head_tail hpb_ne]; rw [hpb_head_eq]
  have hpb_tail_len : pb.tail.length = pb.length - 1 := List.length_tail
  have hpb_tail_ne : pb.tail ≠ [] := by
    rw [← List.length_pos_iff, hpb_tail_len]; omega
  set p := pa ++ pb.tail with hp_def
  set R := pa.length with hR_def
  have hp_len_eq : p.length = R + pb.tail.length := by
    simp only [hp_def, List.length_append, ← hR_def]
  have hp_len : p.length ≥ 2 := by rw [hp_len_eq]; omega
  have hp_head : p.head? = some x := by
    have : p.head? = pa.head? := List.head?_append_of_ne_nil _ hpa_ne
    rw [this, hpa_head]
  have hp_last : p.getLast? = some y := by
    have hlast_tail : pb.tail.getLast? = some y := by
      have heq : pb = [n] ++ pb.tail := by simpa using hpb_decomp
      have := List.getLast?_append_of_ne_nil [n] hpb_tail_ne
      rw [← heq] at this; rw [← this]; exact hpb_last
    simp only [hp_def, List.getLast?_append, hlast_tail]; rfl
  refine ⟨hp_len, hp_head, hp_last, ?_⟩
  -- Index translation: p[k] = pa[k] for k < R; p[k] = pb[k-R+1] for k ≥ R.
  have hp_L : ∀ (k : ℕ) (hkR : k < R),
      p.get ⟨k, by rw [hp_len_eq]; omega⟩ = pa.get ⟨k, hkR⟩ := by
    intro k hkR
    simp only [hp_def, List.get_eq_getElem, List.getElem_append_left (h := hkR)]
  have hpb_tail_get : ∀ (j : ℕ) (hj1 : j < pb.tail.length) (hj2 : j + 1 < pb.length),
      pb.tail[j]'hj1 = pb[j + 1]'hj2 := by
    intro j hj1 hj2
    have : pb[j + 1] = (n :: pb.tail)[j + 1]'(by rw [← hpb_decomp]; exact hj2) := by congr 1
    rw [this]; simp [List.getElem_cons_succ]
  have hp_R : ∀ (k : ℕ) (hkL : R ≤ k) (hk : k < p.length),
      p.get ⟨k, hk⟩ = pb.get ⟨k - R + 1, by
        rw [hp_len_eq, hpb_tail_len] at hk; omega⟩ := by
    intro k hkL hk
    have hk_app : R ≤ k := hkL
    have htail_idx_lt : k - R < pb.tail.length := by
      rw [hp_len_eq] at hk; omega
    have hpget : p.get ⟨k, hk⟩ = pb.tail[k - R]'htail_idx_lt := by
      simp only [hp_def, List.get_eq_getElem]
      rw [List.getElem_append_right (by rw [← hR_def]; exact hk_app)]
    rw [hpget]
    rw [hpb_tail_get (k - R) htail_idx_lt (by rw [hpb_tail_len] at htail_idx_lt; omega)]
    simp [List.get_eq_getElem]
  -- pb[0] = n, pa[R-1] = n.
  have hpb_get_0 : pb.get ⟨0, by omega⟩ = n := by
    rw [List.get_eq_getElem, List.getElem_zero]; exact hpb_head_eq
  have hpa_get_last : pa.get ⟨R - 1, by omega⟩ = n := by
    rw [List.get_eq_getElem]
    have := List.getLast_eq_getElem hpa_ne
    rw [hpa_last_eq] at this
    rw [← this]
  refine ⟨?_, ?_⟩
  · -- Adjacency.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hA1 : i + 1 < R
    · -- Both in pa.
      have hiR : i < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hA1]
      exact hpa_act.1 i hA1
    · push_neg at hA1
      by_cases hA2 : i + 1 = R
      · -- Seam at i = R-1: UAdj(pa[R-1]=n, pb.tail[0]=pb[1]).
        have hi_eq : i = R - 1 := by omega
        subst hi_eq
        have hiR : R - 1 < R := by omega
        rw [hp_L (R - 1) hiR]
        have hi1L : R ≤ R - 1 + 1 := by omega
        have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R (R - 1 + 1) hi1L hi1_lt]
        rw [hpa_get_last]
        have h_yidx : R - 1 + 1 - R + 1 = 1 := by omega
        rw [show (⟨R - 1 + 1 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi1_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_yidx]
        -- UAdj n pb[1] from edge pb[1] → n.
        exact Or.inr hpb_in
      · -- Both in pb.tail. i ≥ R.
        have hiL : R ≤ i := by omega
        have hi1L : R ≤ i + 1 := by omega
        have hi_lt : i < p.length := by rw [hp_len_eq]; omega
        have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt]
        have hidx : (i - R + 1) + 1 < pb.length := by omega
        have hadj := hpb_act.1 (i - R + 1) hidx
        have he : (i - R + 1) + 1 = (i + 1) - R + 1 := by omega
        rw [show (⟨(i - R + 1) + 1, hidx⟩ : Fin pb.length) =
            ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext he] at hadj
        exact hadj
  · -- Collider condition.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hC1 : i + 2 < R
    · -- All three in pa.
      have hiR : i < R := by omega
      have hi1R : i + 1 < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hi1R, hp_L (i + 2) hC1]
      exact hpa_act.2 i hC1
    · push_neg at hC1
      by_cases hC2 : i + 2 = R
      · -- Seam collider: middle = pa[R-1] = n. Triple (pa[R-2], n, pb[1]).
        have hi_eq : i = R - 2 := by omega
        subst hi_eq
        have hiR : R - 2 < R := by omega
        have hi1R : R - 2 + 1 < R := by omega
        have hi2L : R ≤ R - 2 + 2 := by omega
        have hi2_lt : R - 2 + 2 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_L (R - 2) hiR, hp_L (R - 2 + 1) hi1R, hp_R (R - 2 + 2) hi2L hi2_lt]
        rw [show (⟨R - 2 + 1, by omega⟩ : Fin pa.length) = ⟨R - 1, by omega⟩ from
          Fin.ext (show R - 2 + 1 = R - 1 by omega)]
        rw [hpa_get_last]
        have h_ridx : R - 2 + 2 - R + 1 = 1 := by omega
        rw [show (⟨R - 2 + 2 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi2_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_ridx]
        -- left = pa[R-2]; edge into n is hpa_in (pa[R-2]→n); right = pb[1], edge pb[1]→n.
        have hLeq : pa.get ⟨R - 2, by omega⟩ = pa.get ⟨pa.length - 2, by omega⟩ := by
          congr 1
        have hColl : G.IsCollider (pa.get ⟨R - 2, by omega⟩) n (pb.get ⟨1, by omega⟩) := by
          refine ⟨?_, hpb_in⟩
          rw [hLeq]; exact hpa_in
        rw [if_pos hColl]
        -- n ∈ bbZAncestors Z since n ∈ Z.
        show n ∈ G.bbZAncestors Z
        exact G.subset_ancestralSet Z hnZ
      · by_cases hC3 : i + 1 = R
        · -- Straddle: middle = pb.tail[0] = pb[1]. Triple (pa[R-1]=n, pb[1], pb[2]) = pb's index 0.
          have hi_eq : i = R - 1 := by omega
          subst hi_eq
          have hiR : R - 1 < R := by omega
          have hi1L : R ≤ R - 1 + 1 := by omega
          have hi2L : R ≤ R - 1 + 2 := by omega
          have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : R - 1 + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_L (R - 1) hiR, hp_R (R - 1 + 1) hi1L hi1_lt, hp_R (R - 1 + 2) hi2L hi2_lt]
          rw [hpa_get_last]
          rw [show (⟨R - 1 + 1 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨1, by omega⟩ from Fin.ext (show R - 1 + 1 - R + 1 = 1 by omega)]
          rw [show (⟨R - 1 + 2 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨2, by omega⟩ from Fin.ext (show R - 1 + 2 - R + 1 = 2 by omega)]
          -- This matches pb's collider clause at index 0 (triple pb[0]=n, pb[1], pb[2]).
          have hpb0 := hpb_act.2 0 (by omega)
          rw [show (⟨0 + 1, by omega⟩ : Fin pb.length) = ⟨1, by omega⟩ from rfl,
              show (⟨0 + 2, by omega⟩ : Fin pb.length) = ⟨2, by omega⟩ from rfl] at hpb0
          rw [hpb_get_0] at hpb0
          exact hpb0
        · -- All three in pb.tail. i ≥ R.
          have hiL : R ≤ i := by omega
          have hi1L : R ≤ i + 1 := by omega
          have hi2L : R ≤ i + 2 := by omega
          have hi_lt : i < p.length := by rw [hp_len_eq]; omega
          have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : i + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt, hp_R (i + 2) hi2L hi2_lt]
          have hjlen : (i - R + 1) + 2 < pb.length := by omega
          have hpbcoll := hpb_act.2 (i - R + 1) hjlen
          rw [show (⟨(i - R + 1) + 1, by omega⟩ : Fin pb.length) =
              ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext (show (i-R+1)+1 = (i+1)-R+1 by omega),
              show (⟨(i - R + 1) + 2, hjlen⟩ : Fin pb.length) =
              ⟨(i + 2) - R + 1, by omega⟩ from
                Fin.ext (show (i-R+1)+2 = (i+2)-R+1 by omega)] at hpbcoll
          exact hpbcoll


end DAG

end Causalean.Graph

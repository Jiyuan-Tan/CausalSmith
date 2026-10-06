/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DSep.Ancestral
public import Causalean.Graph.DSep.OrderedLocalSG.Defs
public import Causalean.Graph.DSep.OrderedLocalSG.PathSurgery
public import Causalean.Graph.DSep.OrderedLocalSG.PathJoining

/-! # Closure of d-separation under the ordered-local rules

This file carries out the well-founded peel induction proving
`orderedLocalSG_of_dSep_with_fixed`: d-separation with random and fixed conditioning
sets yields a derivation from the ordered-local basis and the semi-graphoid rules. It
also exposes a reachability lemma that extends an active walk by a forward directed arm.
-/

public section

namespace Causalean.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- **Maximal-condition branch split** (the single hardest graph step). If `X`
    and `Y` are d-separated by `insert n (Z' ∪ Zf)` with `n` topologically maximal
    in the query's ancestral set, then `n` is d-separated from one of the two
    sides given the remaining condition together with the other side.

    Graphically: topological maximality forces every edge of a relevant active
    path incident to `n` to point *into* `n`. If `n` were active for both `X` and
    `Y` simultaneously one could concatenate an `X → n` segment with an `n → Y`
    segment through the collider `n` (active since `n` is conditioned), yielding an
    active `X → Y` walk — contradicting `dSep X Y (insert n …)`. Hence one of the
    two one-sided separations holds. -/
private theorem dSep_maximal_condition_branch {X Y Z' Zf : Finset V} {n : V}
    (hnZ' : n ∉ Z') (hnZf : n ∉ Zf)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ (insert n Z') ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (insert n Z' ∪ Zf)) :
    G.dSep X {n} ((Z' ∪ Y) ∪ Zf) ∨ G.dSep Y {n} ((Z' ∪ X) ∪ Zf) := by
  set S : Finset V := Z' ∪ Zf with hS_def
  -- Set bookkeeping: the three conditioning sets in terms of `S`.
  have hSY : (Z' ∪ Y) ∪ Zf = S ∪ Y := by
    rw [hS_def]; ext z; simp only [Finset.mem_union]; tauto
  have hSX : (Z' ∪ X) ∪ Zf = S ∪ X := by
    rw [hS_def]; ext z; simp only [Finset.mem_union]; tauto
  have hinsS : insert n Z' ∪ Zf = insert n S := by
    rw [hS_def]; ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  -- The query (`bigQ`) and topological maximality over it.
  set bigQ : Finset V := X ∪ Y ∪ insert n Z' ∪ Zf with hbigQ_def
  -- Inclusions of the per-side query sets into `bigQ`.
  have hbigQ_X : X ∪ {n} ∪ (S ∪ Y) ⊆ bigQ := by
    rw [hbigQ_def, hS_def]; intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hz ⊢; tauto
  have hbigQ_Y : Y ∪ {n} ∪ (S ∪ X) ⊆ bigQ := by
    rw [hbigQ_def, hS_def]; intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hz ⊢; tauto
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotL, hnotR⟩ := hcon
  -- Failure of each disjunct gives `n` reachable from the respective source.
  have hreachX : n ∈ G.bbReachableVertices ((Z' ∪ Y) ∪ Zf) X := by
    by_contra hnReach
    apply hnotL
    refine ⟨?_, ?_, ?_, Finset.disjoint_singleton_right.mpr hnReach⟩
    · rw [Finset.disjoint_singleton_right]
      intro hnX
      exact Finset.disjoint_left.mp hdSep.2.1 hnX
        (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
    · rw [Finset.disjoint_left]
      intro x hxX hxCond
      simp only [Finset.mem_union] at hxCond
      rcases hxCond with (hxZ' | hxY) | hxZf
      · exact Finset.disjoint_left.mp hdSep.2.1 hxX
          (Finset.mem_union_left _ (Finset.mem_insert_of_mem hxZ'))
      · exact Finset.disjoint_left.mp hdSep.1 hxX hxY
      · exact Finset.disjoint_left.mp hdSep.2.1 hxX (Finset.mem_union_right _ hxZf)
    · rw [Finset.disjoint_singleton_left]
      intro hnCond
      simp only [Finset.mem_union] at hnCond
      rcases hnCond with (hnZ | hnY) | hnF
      · exact hnZ' hnZ
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hnY
          (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
      · exact hnZf hnF
  have hreachY : n ∈ G.bbReachableVertices ((Z' ∪ X) ∪ Zf) Y := by
    by_contra hnReach
    apply hnotR
    refine ⟨?_, ?_, ?_, Finset.disjoint_singleton_right.mpr hnReach⟩
    · rw [Finset.disjoint_singleton_right]
      intro hnY
      exact Finset.disjoint_left.mp hdSep.2.2.1 hnY
        (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
    · rw [Finset.disjoint_left]
      intro y hyY hyCond
      simp only [Finset.mem_union] at hyCond
      rcases hyCond with (hyZ' | hyX) | hyZf
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hyY
          (Finset.mem_union_left _ (Finset.mem_insert_of_mem hyZ'))
      · exact Finset.disjoint_left.mp hdSep.1 hyX hyY
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hyY (Finset.mem_union_right _ hyZf)
    · rw [Finset.disjoint_singleton_left]
      intro hnCond
      simp only [Finset.mem_union] at hnCond
      rcases hnCond with (hnZ | hnX) | hnF
      · exact hnZ' hnZ
      · exact Finset.disjoint_left.mp hdSep.2.1 hnX
          (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
      · exact hnZf hnF
  rw [hSY, G.bbReachableVertices_iff_activeWalk] at hreachX
  rw [hSX, G.bbReachableVertices_iff_activeWalk] at hreachY
  obtain ⟨x, hxX, p1, hp1len, hp1act, hp1head, hp1last⟩ := hreachX
  obtain ⟨y, hyY, p2, hp2len, hp2act, hp2head, hp2last⟩ := hreachY
  have hmaxQ : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n := by
    rw [hbigQ_def]; exact hmax
  -- Any active `X → Y` walk given `insert n S` contradicts `hdSep`.
  have hcontra_XY : ∀ (q : List V) (xa ya : V), xa ∈ X → ya ∈ Y →
      q.length ≥ 2 → G.IsActiveWalk (insert n S) q → q.head? = some xa →
      q.getLast? = some ya → False := by
    intro q xa ya hxaX hyaY hqlen hqact hqhead hqlast
    have hmem : ya ∈ G.bbReachableVertices (insert n S) X := by
      rw [G.bbReachableVertices_iff_activeWalk]
      exact ⟨xa, hxaX, q, hqlen, hqact, hqhead, hqlast⟩
    rw [← hinsS] at hmem
    exact (Finset.disjoint_left.mp hdSep.2.2.2 hmem) hyaY
  -- Process both sides with `survive_or_splice`.
  rcases G.survive_or_splice hbigQ_X hmaxQ hxX hp1len hp1act hp1head hp1last with
    ⟨q, w, hwY, hqlen, hqact, hqhead, hqlast⟩ | ⟨qx, hqx2, hqxact, hqxhead, hqxlast, hqxin⟩
  · -- Splice on the X-side: active `X → Y` walk given `insert n S`.
    exact hcontra_XY q x w hxX hwY hqlen hqact hqhead hqlast
  · -- Survive on the X-side: active `X → n` walk given `insert n S`, last edge into `n`.
    rcases G.survive_or_splice hbigQ_Y hmaxQ hyY hp2len hp2act hp2head hp2last with
      ⟨q', w', hw'X, hq'len, hq'act, hq'head, hq'last⟩ | ⟨qy, hqy2, hqyact, hqyhead, hqylast, hqyin⟩
    · -- Splice on the Y-side: active `Y → X` walk; reverse to `X → Y`.
      have hrev_act : G.IsActiveWalk (insert n S) q'.reverse := G.isActiveWalk_reverse hq'act
      have hrev_len : q'.reverse.length ≥ 2 := by rw [List.length_reverse]; exact hq'len
      have hrev_head : q'.reverse.head? = some w' := by rw [List.head?_reverse]; exact hq'last
      have hrev_last : q'.reverse.getLast? = some y := by rw [List.getLast?_reverse]; exact hq'head
      exact hcontra_XY q'.reverse w' y hw'X hyY hrev_len hrev_act hrev_head hrev_last
    · -- Both survive: join `qx : x → n` with reverse of `qy : y → n` at the collider `n`.
      set pb := qy.reverse with hpb_def
      have hpb_act : G.IsActiveWalk (insert n S) pb := G.isActiveWalk_reverse hqyact
      have hpb_len : pb.length ≥ 2 := by rw [hpb_def, List.length_reverse]; exact hqy2
      have hpb_head : pb.head? = some n := by
        rw [hpb_def, List.head?_reverse]; exact hqylast
      have hpb_last : pb.getLast? = some y := by
        rw [hpb_def, List.getLast?_reverse]; exact hqyhead
      -- First edge of `pb` into `n`: `pb[1] = qy[qy.length - 2]`, and `qy[len-2] → n`.
      have hpb_in : G.edge (pb.get ⟨1, by omega⟩) n := by
        have hpb1 : pb.get ⟨1, by omega⟩ = qy.get ⟨qy.length - 2, by omega⟩ := by
          simp only [hpb_def, List.get_eq_getElem, List.getElem_reverse]
          congr 1
        rw [hpb1]; exact hqyin
      obtain ⟨_, hjhead, hjlast, hjact⟩ :=
        G.activeWalk_join_at_collider hqx2 hqxhead hqxlast hqxact hpb_len hpb_head hpb_last
          hpb_act hqxin hpb_in (Finset.mem_insert_self n S)
      exact hcontra_XY (qx ++ pb.tail) x y hxX hyY (by
        rw [List.length_append]; omega) hjact hjhead hjlast

/-- **A maximal fixed root can be dropped.** If `n ∈ Zf` is a fixed root (no
    parents) and is the topological maximum of the query's ancestral set, then
    deleting it from the conditioning set preserves d-separation of `X` and `Y`.

    Graphically: having no parents, `n` is never a collider, so it cannot be a
    collider-activated node on any active walk; being topologically maximal it
    cannot be a non-collider passing point of a relevant `X → Y` path either.
    Removing it from the condition therefore changes no active walk. -/
private theorem dSep_erase_maximal_fixed_root {X Y Zr Zf : Finset V} {n : V}
    (hnZf : n ∈ Zf)
    (hRoot : G.parents n = ∅)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.dSep X Y (Zr ∪ (Zf.erase n)) := by
  refine ⟨hdSep.1, ?_, ?_, ?_⟩
  · exact hdSep.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz.2)
  · exact hdSep.2.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz.2)
  rw [Finset.disjoint_left]
  intro y hyReach hyY
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
      Or.inl (Or.inr h), Or.inr h.2]
  -- `n` is never a non-collider on `p` (topological maximality, as in A2g).
  have hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hout := G.nonCollider_has_outgoing (hadj i (by omega)) (hadj (i + 1) (by omega)) hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
    · have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
  have hact' : G.IsActiveWalk (insert n (Zr ∪ Zf.erase n)) p :=
    G.isActiveWalk_insert_cond hact hno
  have hins : insert n (Zr ∪ Zf.erase n) = Zr ∪ Zf := by
    ext z; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | h | ⟨_, h⟩)
      exacts [Or.inr hnZf, Or.inl h, Or.inr h]
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · by_cases hz : z = n
        · exact Or.inl hz
        · exact Or.inr (Or.inr ⟨hz, h⟩)
  rw [hins] at hact'
  have : y ∈ G.bbReachableVertices (Zr ∪ Zf) X := by
    rw [G.bbReachableVertices_iff_activeWalk]
    exact ⟨x, hxX, p, hlen, hact', hhead, hlast⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 this) hyY

omit [Fintype V] in
/-- For [a finite vertex population](hyp:V), [four vertex sets and a selected
vertex](hyp:a,b,Zr,c,n), if [the selected vertex belongs to the third set](hyp:hn), then
[removing and reinserting it while forming the union leaves that union unchanged](goal). -/
theorem branch_seed_eq {a b Zr c : Finset V} {n : V} (hn : n ∈ Zr) :
    a ∪ {n} ∪ (Zr.erase n ∪ b) ∪ c = a ∪ b ∪ Zr ∪ c := by
  ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (((h | h) | (h | h)) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (h ▸ hn))
    · exact Or.inl (Or.inr h.2)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr h
  · rintro (((h | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · by_cases hx : x = n
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr (Or.inl ⟨hx, h⟩))
    · exact Or.inr h

-- ============================================================
-- § 4. d-separation ⟹ ordered-local derivation (the crux)
-- ============================================================

/-- **d-separation yields an ordered-local derivation.** In a DAG `G`, suppose
    [every vertex of `Zf` has no parents, i.e. `Zf` consists of fixed roots](hyp:hFixedRoots),
    [`Zf` is disjoint from `R`](hyp:hFR), and [`X`, `Y`, and `Zr` are each contained in
    `R`](hyp:hX,hY,hZr). If [`X` and `Y` are d-separated by `Zr ∪ Zf`](hyp:hdSep), then
    [the conditional-independence triple "`X` ⊥ `Y` given `Zr`" is derivable from the
    ordered-local basis on `R` via the semi-graphoid axioms](goal).

    The conditioning set in the conclusion drops the fixed part `Zf`: fixed roots
    carry no randomness and are excluded from every `parents v ∩ R`, so the
    derivation discharges their blocking role graphically (a maximal fixed root is
    irrelevant to all relevant active walks; a non-maximal one is an ancestor of a
    random node and disappears when that node's basis statement conditions only on
    `parents v ∩ R`).

    Proved by well-founded induction on the ancestral set, peeling the
    topologically-maximal relevant node; this is the constructive form of the
    classical local-to-global Markov theorem. -/
theorem orderedLocalSG_of_dSep_with_fixed
    (R X Y Zr Zf : Finset V)
    (hFixedRoots : ∀ f ∈ Zf, G.parents f = ∅)
    (hFR : Disjoint Zf R)
    (hX : X ⊆ R) (hY : Y ⊆ R) (hZr : Zr ⊆ R)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.OrderedLocalSG R X Y Zr := by
  have hXY : Disjoint X Y := hdSep.1
  have hXZ : Disjoint X Zr := hdSep.2.1.mono_right Finset.subset_union_left
  have hYZ : Disjoint Y Zr := hdSep.2.2.1.mono_right Finset.subset_union_left
  -- Trivial base case: an empty source set.
  rcases Finset.eq_empty_or_nonempty X with hXe | hXne
  · subst hXe; exact OrderedLocalSG.nil Y Zr hY hZr
  -- Abbreviate the query set and select a topological maximum of its ancestral set.
  set Q : Finset V := X ∪ Y ∪ Zr ∪ Zf with hQ_def
  have hQne : (G.ancestralSet Q).Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    exact ⟨x, G.subset_ancestralSet Q (by
      simp only [hQ_def, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hx)))⟩
  obtain ⟨n, hnAnc, hmax⟩ := Finset.exists_max_image (G.ancestralSet Q) G.topoOrder hQne
  have hnQ : n ∈ Q := G.topoMax_mem_seed hnAnc hmax
  -- Membership facts used across the cases.
  have hnR_of_mem : ∀ {S : Finset V}, S ⊆ R → n ∈ S → n ∉ Zf := by
    intro S hSR hnS hnF
    exact (Finset.disjoint_left.mp hFR hnF) (hSR hnS)
  -- Reusable inclusions for the termination (card-drop) arguments.
  have hQanc : Q ⊆ G.ancestralSet Q := G.subset_ancestralSet Q
  have hParAnc : G.parents n ⊆ G.ancestralSet Q := by
    intro a ha
    exact G.mem_ancestralSet_of_isAncestor hnQ (isAncestor.edge (G.mem_parents.mp ha))
  have hXsubQ : X ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hYsubQ : Y ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hZrsubQ : Zr ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hZfsubQ : Zf ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hXQ : X ⊆ G.ancestralSet Q := hXsubQ.trans hQanc
  have hYQ : Y ⊆ G.ancestralSet Q := hYsubQ.trans hQanc
  have hZrQ : Zr ⊆ G.ancestralSet Q := hZrsubQ.trans hQanc
  have hZfQ : Zf ⊆ G.ancestralSet Q := hZfsubQ.trans hQanc
  rw [hQ_def] at hnQ
  simp only [Finset.mem_union] at hnQ
  -- Case analysis on where the maximal node `n` sits.
  rcases hnQ with ((hnX | hnY) | hnZr) | hnZf
  · -- ===== Case n ∈ X =====
    set X' : Finset V := X.erase n with hX'_def
    set A : Finset V := G.parents n ∩ R with hA_def
    set C : Finset V := Zr ∪ X' with hC_def
    set A0 : Finset V := A \ C with hA0_def
    have hnX' : n ∉ X' := Finset.notMem_erase n X
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hX hnX) h
    have hXins : X = insert n X' := (Finset.insert_erase hnX).symm
    have hX'R : X' ⊆ R := (Finset.erase_subset _ _).trans hX
    have hX'X : X' ⊆ X := Finset.erase_subset _ _
    have hnY : n ∉ Y := fun h => (Finset.disjoint_left.mp hXY hnX) h
    have hnZr : n ∉ Zr := fun h => (Finset.disjoint_left.mp hXZ hnX) h
    have hCR : C ⊆ R := Finset.union_subset hZr hX'R
    have hAR : A ⊆ R := Finset.inter_subset_right
    have hA0R : A0 ⊆ R := (Finset.sdiff_subset).trans hAR
    -- `n` is not an ancestor of any query node (topological maximality).
    have hND_Q : ∀ w ∈ Q, ¬ G.isAncestor n w := by
      intro w hwQ hanc
      have h1 : G.topoOrder w ≤ G.topoOrder n := hmax w (G.subset_ancestralSet Q hwQ)
      have h2 : G.topoOrder n < G.topoOrder w := G.isAncestor_topoOrder_lt hanc
      omega
    -- ihX': drop `n` from the source.
    have ihX' : G.OrderedLocalSG R X' Y Zr :=
      orderedLocalSG_of_dSep_with_fixed R X' Y Zr Zf hFixedRoots hFR hX'R hY hZr
        (G.dSep_subset_left hX'X hdSep)
    -- `dSep {n} Y (C ∪ Zf)`.
    have hCZf_eq : C ∪ Zf = (Zr ∪ Zf) ∪ X' := by
      rw [hC_def]; ext x; simp only [Finset.mem_union]; tauto
    have hdSepN : G.dSep {n} Y (C ∪ Zf) := by
      rw [hCZf_eq]
      apply G.dSep_source_to_cond (X := {n}) (S := X')
      · exact Finset.disjoint_singleton_left.mpr hnX'
      · rw [show ({n} : Finset V) ∪ X' = X by rw [hXins, Finset.insert_eq]]
        exact hdSep
    -- Parents disjoint from `Y`; hence `A0` (⊆ parents) too.
    have hParY : Disjoint (G.parents n) Y := G.parents_disjoint_of_dSep_singleton hdSepN
    have hAY : Disjoint A Y := hParY.mono_left Finset.inter_subset_left
    -- A2f: parents inherit the separation.
    have hA0_par : ∀ a ∈ A0, G.edge a n := by
      intro a ha
      have : a ∈ A := (Finset.mem_sdiff.mp ha).1
      exact G.mem_parents.mp (Finset.mem_inter.mp this).1
    have hA0_D : ∀ a ∈ A0, a ∉ C ∪ Zf := by
      intro a ha haCZf
      rw [Finset.mem_union] at haCZf
      rcases haCZf with haC | haZf
      · exact (Finset.mem_sdiff.mp ha).2 haC
      · exact (Finset.disjoint_left.mp hFR haZf) (hA0R ha)
    have hdSepA0 : G.dSep A0 Y (C ∪ Zf) :=
      G.dSep_parents_of_maximal_source hdSepN hA0_par hA0_D
    -- ihA0.
    have ihA0 : G.OrderedLocalSG R A0 Y C :=
      orderedLocalSG_of_dSep_with_fixed R A0 Y C Zf hFixedRoots hFR hA0R hY hCR
        hdSepA0
    -- Basis at `n` with block `P = Y ∪ C ∪ A`.
    have hPR : Y ∪ C ∪ A ⊆ R := Finset.union_subset (Finset.union_subset hY hCR) hAR
    -- `Y ∪ C ⊆ Q` (used to inherit `¬ isAncestor n ·` from topo-maximality).
    have hYC_subQ : Y ∪ C ⊆ Q := by
      rw [hQ_def, hC_def]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hY' | hZr' | hX''
      · exact Or.inl (Or.inl (Or.inr hY'))
      · exact Or.inl (Or.inr hZr')
      · exact Or.inl (Or.inl (Or.inl (hX'X hX'')))
    have hPND : Y ∪ C ∪ A ⊆ G.nonDescendants n := by
      intro w hw
      rw [Finset.mem_union] at hw
      simp only [nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with hwYC | hwA
      · -- w ∈ Y ∪ C ⊆ Q: topo-maximal `n` is no ancestor of `w`, and `w ≠ n`.
        have hwQ : w ∈ Q := hYC_subQ hwYC
        refine ⟨hND_Q w hwQ, ?_⟩
        rintro rfl
        rw [Finset.mem_union, hC_def, Finset.mem_union] at hwYC
        rcases hwYC with h | h | h
        exacts [hnY h, hnZr h, hnX' h]
      · -- w ∈ A = parents n ∩ R: `n` cannot be an ancestor of its own parent.
        have hwPar : w ∈ G.parents n := (Finset.mem_inter.mp hwA).1
        have hedge : G.edge w n := G.mem_parents.mp hwPar
        refine ⟨fun hanc => ?_, fun hwn => G.irrefl n (hwn ▸ hedge)⟩
        exact G.isAncestor_irrefl n (G.isAncestor_trans hanc (isAncestor.edge hedge))
    have hAsubP : A ⊆ Y ∪ C ∪ A := Finset.subset_union_right
    have hPaR_sub : G.parents n ∩ R ⊆ Y ∪ C ∪ A := by rw [← hA_def]; exact hAsubP
    have hbasis := OrderedLocalSG.basis (G := G) (R := R) n (hX hnX) (Y ∪ C ∪ A) hPR hPND hPaR_sub
    -- `(Y ∪ C ∪ A) \ (parents n ∩ R) = Y ∪ (C \ A)`.
    have hsdiff_eq : (Y ∪ C ∪ A) \ (G.parents n ∩ R) = Y ∪ (C \ A) := by
      rw [← hA_def]; ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(hY' | hC') | hA', hnA⟩
        · exact Or.inl hY'
        · exact Or.inr ⟨hC', hnA⟩
        · exact absurd hA' hnA
      · rintro (hY' | ⟨hC', hnA⟩)
        · exact ⟨Or.inl (Or.inl hY'), fun hA' => (Finset.disjoint_left.mp hAY hA') hY'⟩
        · exact ⟨Or.inl (Or.inr hC'), hnA⟩
    rw [hsdiff_eq, ← hA_def] at hbasis
    -- weakUnion: move `C \ A` into the condition; `A ∪ (C \ A) = C ∪ A0`.
    have hweak := OrderedLocalSG.weakUnion (W := C \ A) (Z := A) hbasis
    have hAC_eq : A ∪ (C \ A) = C ∪ A0 := by
      rw [hA0_def]; ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [hAC_eq] at hweak
    -- hweak : {n} ⊥ Y | (C ∪ A0).  Fold with ihA0 to drop `A0`.
    have hstep2 : G.OrderedLocalSG R {n} Y C := by
      have h1 : G.OrderedLocalSG R Y {n} (C ∪ A0) := hweak.symm
      have h2 : G.OrderedLocalSG R Y A0 C := ihA0.symm
      have hc : G.OrderedLocalSG R Y ({n} ∪ A0) C := OrderedLocalSG.contract h1 h2
      exact (OrderedLocalSG.decomp (W := A0) hc).symm
    -- Final fold with ihX': `{n}∪X' = X`.
    have h1 : G.OrderedLocalSG R Y {n} (Zr ∪ X') := by rw [← hC_def]; exact hstep2.symm
    have h2 : G.OrderedLocalSG R Y X' Zr := ihX'.symm
    have hc : G.OrderedLocalSG R Y ({n} ∪ X') Zr := OrderedLocalSG.contract h1 h2
    rw [show ({n} : Finset V) ∪ X' = X by rw [hXins, Finset.insert_eq]] at hc
    exact hc.symm
  · -- ===== Case n ∈ Y =====  (mirror of the n ∈ X case with X ↔ Y)
    refine OrderedLocalSG.symm ?_
    have hdSepYX : G.dSep Y X (Zr ∪ Zf) := G.dSep_symm _ _ _ hdSep
    set Y' : Finset V := Y.erase n with hY'_def
    set A : Finset V := G.parents n ∩ R with hA_def
    set C : Finset V := Zr ∪ Y' with hC_def
    set A0 : Finset V := A \ C with hA0_def
    have hnY' : n ∉ Y' := Finset.notMem_erase n Y
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hY hnY) h
    have hYins : Y = insert n Y' := (Finset.insert_erase hnY).symm
    have hY'R : Y' ⊆ R := (Finset.erase_subset _ _).trans hY
    have hY'Y : Y' ⊆ Y := Finset.erase_subset _ _
    have hnX : n ∉ X := fun h => (Finset.disjoint_left.mp hXY h) hnY
    have hnZr : n ∉ Zr := fun h => (Finset.disjoint_left.mp hYZ hnY) h
    have hCR : C ⊆ R := Finset.union_subset hZr hY'R
    have hAR : A ⊆ R := Finset.inter_subset_right
    have hA0R : A0 ⊆ R := (Finset.sdiff_subset).trans hAR
    have hND_Q : ∀ w ∈ Q, ¬ G.isAncestor n w := by
      intro w hwQ hanc
      have h1 : G.topoOrder w ≤ G.topoOrder n := hmax w (G.subset_ancestralSet Q hwQ)
      have h2 : G.topoOrder n < G.topoOrder w := G.isAncestor_topoOrder_lt hanc
      omega
    have ihY' : G.OrderedLocalSG R Y' X Zr :=
      orderedLocalSG_of_dSep_with_fixed R Y' X Zr Zf hFixedRoots hFR hY'R hX hZr
        (G.dSep_subset_left hY'Y hdSepYX)
    have hCZf_eq : C ∪ Zf = (Zr ∪ Zf) ∪ Y' := by
      rw [hC_def]; ext x; simp only [Finset.mem_union]; tauto
    have hdSepN : G.dSep {n} X (C ∪ Zf) := by
      rw [hCZf_eq]
      apply G.dSep_source_to_cond (X := {n}) (S := Y')
      · exact Finset.disjoint_singleton_left.mpr hnY'
      · rw [show ({n} : Finset V) ∪ Y' = Y by rw [hYins, Finset.insert_eq]]
        exact hdSepYX
    have hParX : Disjoint (G.parents n) X := G.parents_disjoint_of_dSep_singleton hdSepN
    have hAX : Disjoint A X := hParX.mono_left Finset.inter_subset_left
    have hA0_par : ∀ a ∈ A0, G.edge a n := by
      intro a ha
      have : a ∈ A := (Finset.mem_sdiff.mp ha).1
      exact G.mem_parents.mp (Finset.mem_inter.mp this).1
    have hA0_D : ∀ a ∈ A0, a ∉ C ∪ Zf := by
      intro a ha haCZf
      rw [Finset.mem_union] at haCZf
      rcases haCZf with haC | haZf
      · exact (Finset.mem_sdiff.mp ha).2 haC
      · exact (Finset.disjoint_left.mp hFR haZf) (hA0R ha)
    have hdSepA0 : G.dSep A0 X (C ∪ Zf) :=
      G.dSep_parents_of_maximal_source hdSepN hA0_par hA0_D
    have ihA0 : G.OrderedLocalSG R A0 X C :=
      orderedLocalSG_of_dSep_with_fixed R A0 X C Zf hFixedRoots hFR hA0R hX hCR
        hdSepA0
    have hPR : X ∪ C ∪ A ⊆ R := Finset.union_subset (Finset.union_subset hX hCR) hAR
    have hXC_subQ : X ∪ C ⊆ Q := by
      rw [hQ_def, hC_def]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hX' | hZr' | hY''
      · exact Or.inl (Or.inl (Or.inl hX'))
      · exact Or.inl (Or.inr hZr')
      · exact Or.inl (Or.inl (Or.inr (hY'Y hY'')))
    have hPND : X ∪ C ∪ A ⊆ G.nonDescendants n := by
      intro w hw
      rw [Finset.mem_union] at hw
      simp only [nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with hwXC | hwA
      · have hwQ : w ∈ Q := hXC_subQ hwXC
        refine ⟨hND_Q w hwQ, ?_⟩
        rintro rfl
        rw [Finset.mem_union, hC_def, Finset.mem_union] at hwXC
        rcases hwXC with h | h | h
        exacts [hnX h, hnZr h, hnY' h]
      · have hwPar : w ∈ G.parents n := (Finset.mem_inter.mp hwA).1
        have hedge : G.edge w n := G.mem_parents.mp hwPar
        refine ⟨fun hanc => ?_, fun hwn => G.irrefl n (hwn ▸ hedge)⟩
        exact G.isAncestor_irrefl n (G.isAncestor_trans hanc (isAncestor.edge hedge))
    have hPaR_sub : G.parents n ∩ R ⊆ X ∪ C ∪ A := by rw [← hA_def]; exact Finset.subset_union_right
    have hbasis := OrderedLocalSG.basis (G := G) (R := R) n (hY hnY) (X ∪ C ∪ A) hPR hPND hPaR_sub
    have hsdiff_eq : (X ∪ C ∪ A) \ (G.parents n ∩ R) = X ∪ (C \ A) := by
      rw [← hA_def]; ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(hX' | hC') | hA', hnA⟩
        · exact Or.inl hX'
        · exact Or.inr ⟨hC', hnA⟩
        · exact absurd hA' hnA
      · rintro (hX' | ⟨hC', hnA⟩)
        · exact ⟨Or.inl (Or.inl hX'), fun hA' => (Finset.disjoint_left.mp hAX hA') hX'⟩
        · exact ⟨Or.inl (Or.inr hC'), hnA⟩
    rw [hsdiff_eq, ← hA_def] at hbasis
    have hweak := OrderedLocalSG.weakUnion (W := C \ A) (Z := A) hbasis
    have hAC_eq : A ∪ (C \ A) = C ∪ A0 := by
      rw [hA0_def]; ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [hAC_eq] at hweak
    have hstep2 : G.OrderedLocalSG R {n} X C := by
      have h1 : G.OrderedLocalSG R X {n} (C ∪ A0) := hweak.symm
      have h2 : G.OrderedLocalSG R X A0 C := ihA0.symm
      have hc : G.OrderedLocalSG R X ({n} ∪ A0) C := OrderedLocalSG.contract h1 h2
      exact (OrderedLocalSG.decomp (W := A0) hc).symm
    have h1 : G.OrderedLocalSG R X {n} (Zr ∪ Y') := by rw [← hC_def]; exact hstep2.symm
    have h2 : G.OrderedLocalSG R X Y' Zr := ihY'.symm
    have hc : G.OrderedLocalSG R X ({n} ∪ Y') Zr := OrderedLocalSG.contract h1 h2
    rw [show ({n} : Finset V) ∪ Y' = Y by rw [hYins, Finset.insert_eq]] at hc
    exact hc.symm
  · -- ===== Case n ∈ Zr =====
    set Z' : Finset V := Zr.erase n with hZ'_def
    have hnZ' : n ∉ Z' := Finset.notMem_erase n Zr
    have hZrins : Zr = insert n Z' := (Finset.insert_erase hnZr).symm
    have hZ'R : Z' ⊆ R := (Finset.erase_subset _ _).trans hZr
    have hnX : n ∉ X := fun h => (Finset.disjoint_left.mp hXZ h) hnZr
    have hnY : n ∉ Y := fun h => (Finset.disjoint_left.mp hYZ h) hnZr
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hZr hnZr) h
    have hmax' : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hQ_def]; exact hmax
    -- IH1: drop `n` from the random condition.
    have hdSep1 : G.dSep X Y (Z' ∪ Zf) :=
      G.dSep_erase_maximal_random_condition hnZr hmax' hdSep
    have ih1 : G.OrderedLocalSG R X Y Z' :=
      orderedLocalSG_of_dSep_with_fixed R X Y Z' Zf hFixedRoots hFR hX hY hZ'R
        hdSep1
    -- Branch lemma: separate `n` from one side.
    have hmaxBr : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ insert n Z' ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hZrins, ← hQ_def]; exact hmax
    have hdSepBr : G.dSep X Y (insert n Z' ∪ Zf) := by rw [← hZrins]; exact hdSep
    -- Rewrite the goal's `Zr` as `Z' ∪ {n}`.
    rw [hZrins, Finset.insert_eq, Finset.union_comm {n} Z']
    rcases G.dSep_maximal_condition_branch hnZ' hnZf hmaxBr hdSepBr with hLeft | hRight
    · -- Left branch: `dSep X {n} ((Z'∪Y)∪Zf)`.
      have hP1 : G.OrderedLocalSG R X {n} (Z' ∪ Y) :=
        orderedLocalSG_of_dSep_with_fixed R X {n} (Z' ∪ Y) Zf hFixedRoots hFR hX
          (Finset.singleton_subset_iff.mpr (hZr hnZr)) (Finset.union_subset hZ'R hY)
          (by rw [show (Z' ∪ Y) ∪ Zf = (Z' ∪ Y) ∪ Zf from rfl]; exact hLeft)
      -- contraction(X; Ỹ={n}, W̃=Y, Z̃=Z') with ih1, then weak union.
      have hc : G.OrderedLocalSG R X ({n} ∪ Y) Z' := OrderedLocalSG.contract hP1 ih1
      rw [Finset.union_comm {n} Y] at hc
      exact OrderedLocalSG.weakUnion hc
    · -- Right branch: `dSep Y {n} ((Z'∪X)∪Zf)`.
      have hP1 : G.OrderedLocalSG R Y {n} (Z' ∪ X) :=
        orderedLocalSG_of_dSep_with_fixed R Y {n} (Z' ∪ X) Zf hFixedRoots hFR hY
          (Finset.singleton_subset_iff.mpr (hZr hnZr)) (Finset.union_subset hZ'R hX)
          hRight
      have hc : G.OrderedLocalSG R Y ({n} ∪ X) Z' := OrderedLocalSG.contract hP1 ih1.symm
      rw [Finset.union_comm {n} X] at hc
      exact (OrderedLocalSG.weakUnion hc).symm
  · -- ===== Case n ∈ Zf =====
    have hRoot : G.parents n = ∅ := hFixedRoots n hnZf
    have hmax' : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hQ_def]; exact hmax
    have hdSep' : G.dSep X Y (Zr ∪ Zf.erase n) :=
      G.dSep_erase_maximal_fixed_root hnZf hRoot hmax' hdSep
    exact orderedLocalSG_of_dSep_with_fixed R X Y Zr (Zf.erase n)
      (fun f hf => hFixedRoots f ((Finset.erase_subset _ _) hf))
      (hFR.mono_left (Finset.erase_subset _ _)) hX hY hZr
      hdSep'
  termination_by peelMeasure G X Y Zr Zf
  decreasing_by
    -- Six calls drop `card (ancestralSet ·)` (first lex component); the two branch
    -- calls keep it equal and drop the `topoOrder`-height (second lex component).
    -- `cardDrop` discharges the former given a subset/avoidance pair.
    all_goals simp only [peelMeasure]
    -- (1) n ∈ X, ihX' on (X.erase n, Y, Zr, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset
          ((Finset.erase_subset _ _).trans hXQ) hYQ) hZrQ) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨Finset.notMem_erase n X, hnY⟩, hnZr⟩, hnZf⟩
    -- (2) n ∈ X, ihA0 on (A0, Y, C, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ hYQ) ?_) hZfQ
        · exact (Finset.sdiff_subset.trans Finset.inter_subset_left).trans hParAnc
        · exact Finset.union_subset hZrQ ((Finset.erase_subset _ _).trans hXQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, hnY⟩, ?_⟩, hnZf⟩
        · exact fun h => G.isAncestor_irrefl n
            (isAncestor.edge (G.mem_parents.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1))
        · exact ⟨hnZr, Finset.notMem_erase n X⟩
    -- (3) n ∈ Y, ihY' on (Y.erase n, X, Zr, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset
          ((Finset.erase_subset _ _).trans hYQ) hXQ) hZrQ) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨Finset.notMem_erase n Y, hnX⟩, hnZr⟩, hnZf⟩
    -- (4) n ∈ Y, ihA0 on (A0, X, C, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ hXQ) ?_) hZfQ
        · exact (Finset.sdiff_subset.trans Finset.inter_subset_left).trans hParAnc
        · exact Finset.union_subset hZrQ ((Finset.erase_subset _ _).trans hYQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, hnX⟩, ?_⟩, hnZf⟩
        · exact fun h => G.isAncestor_irrefl n
            (isAncestor.edge (G.mem_parents.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1))
        · exact ⟨hnZr, Finset.notMem_erase n Y⟩
    -- (5) n ∈ Zr, ih1 on (X, Y, Zr.erase n, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hXQ hYQ)
          ((Finset.erase_subset _ _).trans hZrQ)) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨hnX, hnY⟩, Finset.notMem_erase n Zr⟩, hnZf⟩
    -- (6) n ∈ Zr, left branch P1 on (X, {n}, Z'∪Y, Zf): card EQUAL, height drops.
    · rw [branch_seed_eq (a := X) (b := Y) (c := Zf) hnZr]
      refine Prod.Lex.right _ ?_
      exact G.sup_topoOrder_lt_of_peel hmax hnZr
        (Finset.union_subset ((Finset.erase_subset _ _).trans hZrQ) hYQ)
        (by simp only [Finset.mem_union, not_or]; exact ⟨hnZ', hnY⟩)
    -- (7) n ∈ Zr, right branch P1 on (Y, {n}, Z'∪X, Zf): card EQUAL, height drops.
    · rw [branch_seed_eq (a := Y) (b := X) (c := Zf) hnZr,
        show X ∪ Y ∪ Zr ∪ Zf = Y ∪ X ∪ Zr ∪ Zf from by
          rw [Finset.union_comm X Y]]
      refine Prod.Lex.right _ ?_
      exact G.sup_topoOrder_lt_of_peel hmax hnZr
        (Finset.union_subset ((Finset.erase_subset _ _).trans hZrQ) hXQ)
        (by simp only [Finset.mem_union, not_or]; exact ⟨hnZ', hnX⟩)
    -- (8) n ∈ Zf, on (X, Y, Zr, Zf.erase n): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hXQ hYQ) hZrQ)
          ((Finset.erase_subset _ _).trans hZfQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Finset.notMem_erase n Zf⟩
        · exact fun h => (hnR_of_mem hX h) hnZf
        · exact fun h => (hnR_of_mem hY h) hnZf
        · exact fun h => (hnR_of_mem hZr h) hnZf

/-- Given [a directed acyclic graph, conditioning set, endpoints, and two
walks](hyp:V,G,Z,a,c,b,pa,q), if [the first walk has at least two
vertices](hyp:hpa_len), [begins at the first endpoint](hyp:hpa_head),
[ends at the seam vertex](hyp:hpa_last), and [is active](hyp:hpa_act), while [the second walk has
at least two vertices](hyp:hq_len), [begins at the seam](hyp:hq_head), [ends at the final
endpoint](hyp:hq_last), [follows directed edges](hyp:hq_edge), [has no conditioned interior
vertices](hyp:hq_int), and [the seam is not conditioned on](hyp:hcZ), then [the final
endpoint is Bayes-ball reachable from the first](goal).

    The directed arm leaves `c` (its first edge points out of `c`), so `c` is a
    chain/fork point — never a collider — at the seam, and the glued walk stays
    active.  Public wrapper around `chain_join_active`. -/
theorem bbReachable_extend_directed_arm
    {Z : Finset V} {a c b : V} {pa q : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some a)
    (hpa_last : pa.getLast? = some c) (hpa_act : G.IsActiveWalk Z pa)
    (hq_len : q.length ≥ 2) (hq_head : q.head? = some c) (hq_last : q.getLast? = some b)
    (hq_edge : ∀ (i : ℕ) (hi : i + 1 < q.length),
        G.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, hi⟩))
    (hq_int : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ Z)
    (hcZ : c ∉ Z) :
    b ∈ G.bbReachableVertices Z ({a} : Finset V) := by
  have hq_act : G.IsActiveWalk Z q := G.isActiveWalk_of_directed hq_edge hq_int
  have hqne : q ≠ [] := by intro h; rw [h] at hq_len; simp at hq_len
  -- First edge of `q` points out of `c`.
  have hq_head_eq : q.get ⟨0, by omega⟩ = c := by
    have h := List.head?_eq_some_head hqne
    rw [hq_head] at h
    rw [List.get_eq_getElem, List.getElem_zero]
    exact Option.some_inj.mp h.symm
  have hseam_out : G.edge c (q.get ⟨1, by omega⟩) := by
    have he := hq_edge 0 (by omega)
    rwa [hq_head_eq] at he
  obtain ⟨_, hjhead, hjlast, hjact⟩ :=
    G.chain_join_active hpa_len hpa_head hpa_last hpa_act hq_len hq_head hq_last hq_act
      hseam_out hcZ
  rw [G.bbReachableVertices_iff_activeWalk]
  exact ⟨a, Finset.mem_singleton_self a, pa ++ q.tail,
    by rw [List.length_append]; have := List.length_tail (l := q); omega,
    hjact, hjhead, hjlast⟩


end DAG

end Causalean.Graph

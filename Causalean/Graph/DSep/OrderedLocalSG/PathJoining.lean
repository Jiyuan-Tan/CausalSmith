/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DSep.Ancestral
public import Causalean.Graph.DSep.OrderedLocalSG.Defs
public import Causalean.Graph.DSep.OrderedLocalSG.PathSurgery

/-! # Joining active walks in the ordered-local peel

This file develops the walk-composition tools for the ordered-local induction. It
joins active walks across non-collider seams, relates forward directed walks to
ancestry, preserves activity under prefix extraction, and proves the survive-or-splice
alternative used when a maximal conditioning vertex is removed.
-/

public section

namespace Causalean.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a conditioning set,
joining vertex, endpoints, and two walks](hyp:Z,m,x,y,pa,pb). If [the first walk is active
from the first endpoint to the join](hyp:hpa_len,hpa_head,hpa_last,hpa_act), [the second
is active from the join to the second endpoint](hyp:hpb_len,hpb_head,hpb_last,hpb_act),
[its first edge points out of the join](hyp:hseam_out), and [the joining vertex is not
conditioned on](hyp:hmZ), then [concatenating the walks gives an active walk between the
endpoints](goal). -/
theorem chain_join_active
    {Z : Finset V} {m x y : V} {pa pb : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some x)
    (hpa_last : pa.getLast? = some m) (hpa_act : G.IsActiveWalk Z pa)
    (hpb_len : pb.length ≥ 2) (hpb_head : pb.head? = some m)
    (hpb_last : pb.getLast? = some y) (hpb_act : G.IsActiveWalk Z pb)
    (hseam_out : G.edge m (pb.get ⟨1, by omega⟩))
    (hmZ : m ∉ Z) :
    let p := pa ++ pb.tail
    p.length ≥ 2 ∧ p.head? = some x ∧ p.getLast? = some y ∧
      G.IsActiveWalk Z p := by
  have hpa_ne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
  have hpb_ne : pb ≠ [] := by intro h; rw [h] at hpb_len; simp at hpb_len
  -- pb.head = m
  have hpb_head_eq : pb.head hpb_ne = m := by
    have h := List.head?_eq_some_head hpb_ne; rw [hpb_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.getLast = m
  have hpa_last_eq : pa.getLast hpa_ne = m := by
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
  -- pb = m :: pb.tail
  have hpb_decomp : pb = m :: pb.tail := by
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
      have heq : pb = [m] ++ pb.tail := by simpa using hpb_decomp
      have := List.getLast?_append_of_ne_nil [m] hpb_tail_ne
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
    have : pb[j + 1] = (m :: pb.tail)[j + 1]'(by rw [← hpb_decomp]; exact hj2) := by congr 1
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
  -- pb[0] = m, pa[R-1] = m.
  have hpb_get_0 : pb.get ⟨0, by omega⟩ = m := by
    rw [List.get_eq_getElem, List.getElem_zero]; exact hpb_head_eq
  have hpa_get_last : pa.get ⟨R - 1, by omega⟩ = m := by
    rw [List.get_eq_getElem]
    have := List.getLast_eq_getElem hpa_ne
    rw [hpa_last_eq] at this
    rw [← this]
  refine ⟨?_, ?_⟩
  · -- Adjacency.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hA1 : i + 1 < R
    · have hiR : i < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hA1]
      exact hpa_act.1 i hA1
    · push_neg at hA1
      by_cases hA2 : i + 1 = R
      · have hi_eq : i = R - 1 := by omega
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
        exact Or.inl hseam_out
      · have hiL : R ≤ i := by omega
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
    · have hiR : i < R := by omega
      have hi1R : i + 1 < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hi1R, hp_L (i + 2) hC1]
      exact hpa_act.2 i hC1
    · push_neg at hC1
      by_cases hC2 : i + 2 = R
      · have hi_eq : i = R - 2 := by omega
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
        have hNotColl : ¬ G.IsCollider (pa.get ⟨R - 2, by omega⟩) m (pb.get ⟨1, by omega⟩) := by
          intro hColl
          exact (G.asymm hseam_out) hColl.2
        rw [if_neg hNotColl]
        exact hmZ
      · by_cases hC3 : i + 1 = R
        · have hi_eq : i = R - 1 := by omega
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
          have hpb0 := hpb_act.2 0 (by omega)
          rw [show (⟨0 + 1, by omega⟩ : Fin pb.length) = ⟨1, by omega⟩ from rfl,
              show (⟨0 + 2, by omega⟩ : Fin pb.length) = ⟨2, by omega⟩ from rfl] at hpb0
          rw [hpb_get_0] at hpb0
          exact hpb0
        · have hiL : R ≤ i := by omega
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

/-- In [a finite directed acyclic graph](hyp:V,G), consider [a walk, its endpoint,
and a selected position](hyp:q,w,j). If [the walk is nontrivial](hyp:hlen), [has the stated
endpoint](hyp:hlast), [follows forward directed edges](hyp:hedge), and [the position lies
on the walk](hyp:hj), then [the selected vertex is either the endpoint or its proper
ancestor](goal). -/
theorem node_isAncestor_last_of_directed {q : List V} {w : V}
    (hlen : q.length ≥ 2) (hlast : q.getLast? = some w)
    (hedge : ∀ (i : ℕ) (hi : i + 1 < q.length),
      G.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, hi⟩))
    (j : ℕ) (hj : j < q.length) :
    G.isAncestor (q.get ⟨j, hj⟩) w ∨ q.get ⟨j, hj⟩ = w := by
  by_cases hjlast : j = q.length - 1
  · right
    have hqne : q ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hh := List.getLast?_eq_some_getLast hqne
    rw [hlast] at hh
    have hw_eq : q.getLast hqne = w := Option.some_inj.mp hh.symm
    have hidx : (⟨j, hj⟩ : Fin q.length) = ⟨q.length - 1, by omega⟩ := Fin.ext (by omega)
    rw [hidx, List.get_eq_getElem, ← hw_eq, List.getLast_eq_getElem]
  · have hj1 : j + 1 < q.length := by omega
    have he := hedge j hj1
    rcases node_isAncestor_last_of_directed hlen hlast hedge (j + 1) hj1 with h | h
    · exact Or.inl (G.isAncestor_trans (isAncestor.edge he) h)
    · exact Or.inl (h ▸ isAncestor.edge he)
termination_by q.length - j
decreasing_by omega

/-- **A directed descent to a topological non-maximum is active given `insert n S`.**
    If `c` is an ancestor of `w` (with `w` strictly topologically below `n`, hence not
    reachable through `n`), and `c ∉ ancestralSet S`, then there is an active walk
    `c → w` given `insert n S`: take a directed path avoiding `S`; it cannot pass
    through `n` since `n` is not an ancestor of `w`, so it also avoids `insert n S`. -/
private theorem descent_active_insert {S : Finset V} {c w n : V}
    (hcw : G.isAncestor c w) (hcS : c ∉ G.ancestralSet S)
    (hwn : G.topoOrder w ≤ G.topoOrder n) :
    ∃ (q : List V) (hq2 : q.length ≥ 2), q.head? = some c ∧ q.getLast? = some w ∧
      G.IsActiveWalk (insert n S) q ∧ G.edge c (q.get ⟨1, by omega⟩) := by
  obtain ⟨q, hlen, hhead, hlast, hedge, hSavoid⟩ :=
    G.exists_directedPath_avoiding hcw hcS
  -- Interior nodes of `q` avoid `insert n S`: they avoid `S`, and are strict ancestors
  -- of `w` (topologically below `n`) hence never `n`.
  have hins : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ insert n S := by
    intro i hi
    rw [Finset.mem_insert, not_or]
    refine ⟨?_, hSavoid _ (List.get_mem q ⟨i + 1, by omega⟩)⟩
    -- An interior node is a strict ancestor of `w` (it is not the last node), so it is
    -- `≠ n`: `n = q[i+1]` would give `isAncestor n w`, `topoOrder n < topoOrder w ≤ n`.
    intro hmn
    have hnode := G.node_isAncestor_last_of_directed hlen hlast hedge (i + 1) (by omega)
    rcases hnode with h | h
    · rw [hmn] at h
      have h2 := G.isAncestor_topoOrder_lt h; omega
    · -- `q[i+1] = w`, but `q[i+1]` is interior (`i+1 < q.length - 1`), while `w` is the
      -- last node; the directed edge `q[i+1] → q[i+2]` then makes `w` a strict ancestor
      -- of `w`, contradiction.
      have he := hedge (i + 1) (by omega)
      rw [h] at he
      have hnode2 := G.node_isAncestor_last_of_directed hlen hlast hedge (i + 2) (by omega)
      rcases hnode2 with h2 | h2
      · exact G.isAncestor_irrefl w (G.isAncestor_trans (isAncestor.edge he) h2)
      · exact G.irrefl w (h2 ▸ he)
  -- First edge points out of `c`: `edge c q[1]` from the directed structure.
  have hfirst : G.edge c (q.get ⟨1, by omega⟩) := by
    have he0 := hedge 0 (by omega)
    have hq0 : q.get ⟨0, by omega⟩ = c := by
      have hqne : q ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      have hh := List.head?_eq_some_head hqne
      rw [hhead] at hh
      have : q.head hqne = c := Option.some_inj.mp hh.symm
      rw [List.get_eq_getElem, List.getElem_zero]; exact this
    rw [hq0] at he0
    exact he0
  exact ⟨q, hlen, hhead, hlast, G.isActiveWalk_of_directed hedge hins, hfirst⟩

/-- In [a finite directed acyclic graph](hyp:V,G), [a conditioning set, walk, and
prefix length](hyp:Z,p,k) with [an active full walk](hyp:hact) have [an active prefix](goal). -/
theorem isActiveWalk_take {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActiveWalk Z p) : G.IsActiveWalk Z (p.take k) := by
  obtain ⟨hadj, hcoll⟩ := hact
  have hle : (p.take k).length ≤ p.length := by
    rw [List.length_take]; exact min_le_right k p.length
  have hget : ∀ (j : ℕ) (hj : j < (p.take k).length),
      (p.take k).get ⟨j, hj⟩ = p.get ⟨j, by omega⟩ := by
    intro j hj
    simp only [List.get_eq_getElem, List.getElem_take]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hget i (by omega), hget (i + 1) hi]
    exact hadj i (by omega)
  · rw [hget i (by omega), hget (i + 1) (by omega), hget (i + 2) hi]
    exact hcoll i (by omega)

/-- For [a finite directed acyclic graph](hyp:V,G), [two endpoint sets, a conditioning set, an
auxiliary set, an ambient ancestral query set, a walk, and its endpoints](hyp:S,A,W,bigQ,p,a,n),
if [all relevant vertices lie in the ambient query set](hyp:hbigQ), [the terminal vertex is
topologically maximal in its ancestral closure](hyp:hmax), [the initial vertex belongs to its
endpoint set](hyp:haA), [the walk has at least two vertices](hyp:hlen), [the walk is active under
the cross-conditioning set](hyp:hact), [the walk begins at the stated initial vertex](hyp:hhead),
and [ends at the maximal vertex](hyp:hlast), then [either an active walk can be spliced to the
auxiliary endpoint set or an active walk survives to the maximal vertex with its last edge
directed inward](goal).

**Survive-or-splice for one side.** Given an active walk `p` from `a ∈ A` to the
    topological maximum `n` given the cross-condition `S ∪ W`, with all nodes in the
    query ancestral set `bigQ`: either (splice) there is an active `A → W` walk given
    `insert n S` — obtained by cutting at the closest-to-`a` `W`-only-activated
    collider and descending to `W` — or (survive) `p` itself lifts to an active
    `A → n` walk given `insert n S` whose last edge points into `n`. -/
theorem survive_or_splice {S A W bigQ : Finset V} {p : List V} {a n : V}
    (hbigQ : A ∪ {n} ∪ (S ∪ W) ⊆ bigQ)
    (hmax : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n)
    (haA : a ∈ A) (hlen : p.length ≥ 2) (hact : G.IsActiveWalk (S ∪ W) p)
    (hhead : p.head? = some a) (hlast : p.getLast? = some n) :
    (∃ (q : List V) (w : V), w ∈ W ∧ q.length ≥ 2 ∧ G.IsActiveWalk (insert n S) q ∧
        q.head? = some a ∧ q.getLast? = some w) ∨
    (∃ (q : List V) (hq2 : q.length ≥ 2), G.IsActiveWalk (insert n S) q ∧
        q.head? = some a ∧ q.getLast? = some n ∧
        G.edge (q.get ⟨q.length - 2, by omega⟩) n) := by
  -- Nodes of `p` lie in `ancestralSet bigQ`.
  have hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet bigQ := by
    intro v hv
    have := G.activeWalk_nodes_are_ancestors haA (Finset.mem_singleton_self n) hact hhead hlast v hv
    exact G.ancestralSet_mono hbigQ this
  -- `n` is never an interior non-collider on `p` (topological maximality).
  have hno_n : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hout := G.nonCollider_has_outgoing (hadj i (by omega)) (hadj (i + 1) (by omega)) hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge); omega
    · have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge); omega
  -- Bad indices: interior colliders whose middle is NOT activated by `S` alone.
  classical
  let P : ℕ → Prop := fun i => ∃ (hi : i + 2 < p.length),
    G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) ∧
    p.get ⟨i + 1, by omega⟩ ∉ G.ancestralSet S
  let Bad : Finset ℕ := (Finset.range p.length).filter P
  by_cases hBad : Bad.Nonempty
  · -- ===== SPLICE branch =====
    refine Or.inl ?_
    set i₀ := Bad.min' hBad with hi₀_def
    have hi₀_mem : i₀ ∈ Bad := Bad.min'_mem hBad
    have hi₀_range : i₀ ∈ Finset.range p.length ∧ P i₀ := by
      have := hi₀_mem; simp only [Bad, Finset.mem_filter] at this; exact this
    obtain ⟨hi₀, hC₀, hcS₀⟩ := hi₀_range.2
    set c := p.get ⟨i₀ + 1, by omega⟩ with hc_def
    -- Minimality: every interior collider strictly before `i₀` is `S`-activated.
    have hmin : ∀ (j : ℕ) (hj : j + 2 < p.length), j < i₀ →
        G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩) →
        p.get ⟨j + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro j hj hjlt hCj
      by_contra hnotanc
      have hjBad : j ∈ Bad := by
        simp only [Bad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj, hCj, hnotanc⟩
      have := Bad.min'_le j hjBad
      rw [← hi₀_def] at this; omega
    -- The collider middle `c` is activated by `S ∪ W`.
    have hc_act : c ∈ G.ancestralSet (S ∪ W) := by
      have h := hact.2 i₀ hi₀
      simp only at h
      rw [if_pos hC₀] at h
      exact h
    -- Prefix `q1 := p.take (i₀ + 2)`, ending at `c`, active given `insert n S`.
    set q1 := p.take (i₀ + 2) with hq1_def
    have hq1_len : q1.length = i₀ + 2 := by
      rw [hq1_def, List.length_take]; omega
    have hq1_get : ∀ (j : ℕ) (hj : j < q1.length),
        q1.get ⟨j, hj⟩ = p.get ⟨j, by rw [hq1_len] at hj; omega⟩ := by
      intro j hj; simp only [hq1_def, List.get_eq_getElem, List.getElem_take]
    have hq1_act_SW : G.IsActiveWalk (S ∪ W) q1 := G.isActiveWalk_take hact
    have hq1_head : q1.head? = some a := by
      have hq1ne : q1 ≠ [] := by intro h; rw [h] at hq1_len; simp at hq1_len
      rw [List.head?_eq_some_head hq1ne]
      have hh0 : q1.head hq1ne = q1.get ⟨0, by omega⟩ := by
        rw [List.get_eq_getElem, ← List.head_eq_getElem]
      rw [hh0, hq1_get 0 (by omega)]
      have hpne : p ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      have hh := List.head?_eq_some_head hpne; rw [hhead] at hh
      have hpa : p.head hpne = a := Option.some_inj.mp hh.symm
      rw [show p.get ⟨0, by omega⟩ = p.head hpne by
        rw [List.get_eq_getElem, ← List.head_eq_getElem], hpa]
    have hq1_last : q1.getLast? = some c := by
      have hq1ne : q1 ≠ [] := by intro h; rw [h] at hq1_len; simp at hq1_len
      rw [List.getLast?_eq_some_getLast hq1ne]
      have heq : q1.getLast hq1ne = q1.get ⟨q1.length - 1, by omega⟩ := by
        rw [List.get_eq_getElem, ← List.getLast_eq_getElem]
      rw [heq, hq1_get (q1.length - 1) (by omega)]
      have hidx : q1.length - 1 = i₀ + 1 := by omega
      simp only [hidx, hc_def]
    -- Lift `q1` to `insert n S`.
    have hq1_collS : ∀ (i : ℕ) (hi : i + 2 < q1.length),
        G.IsCollider (q1.get ⟨i, by omega⟩) (q1.get ⟨i + 1, by omega⟩) (q1.get ⟨i + 2, hi⟩) →
        q1.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro i hi hC
      simp only [hq1_get] at hC ⊢
      have hi_p : i + 2 < p.length := by rw [hq1_len] at hi; omega
      exact hmin i hi_p (by rw [hq1_len] at hi; omega) hC
    have hq1_no_n : ∀ (i : ℕ) (hi : i + 2 < q1.length),
        q1.get ⟨i + 1, by omega⟩ = n →
        G.IsCollider (q1.get ⟨i, by omega⟩) (q1.get ⟨i + 1, by omega⟩) (q1.get ⟨i + 2, hi⟩) := by
      intro i hi hmn
      simp only [hq1_get] at hmn ⊢
      exact hno_n i (by rw [hq1_len] at hi; omega) hmn
    have hq1_act : G.IsActiveWalk (insert n S) q1 :=
      G.lift_crosscond_to_insert hq1_act_SW hq1_collS hq1_no_n
    -- Peel `c`'s activation: `c ∈ W` or `c` is a strict ancestor of some `w0 ∈ W`.
    have hc_peel : c ∈ W ∨ ∃ w0 ∈ W, G.isAncestor c w0 := by
      simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc_act
      rcases hc_act with (hcS | hcW) | ⟨s, hsSW, hanc⟩
      · exact absurd (G.subset_ancestralSet S hcS) hcS₀
      · exact Or.inl hcW
      · rcases hsSW with hsS | hsW
        · exact absurd (G.mem_ancestralSet_of_isAncestor hsS hanc) hcS₀
        · exact Or.inr ⟨s, hsW, hanc⟩
    -- `c ∈ ancestralSet bigQ`, so `topoOrder c ≤ topoOrder n`; combined below.
    have hc_bigQ : c ∈ G.ancestralSet bigQ :=
      hpAnc c (List.get_mem p ⟨i₀ + 1, by omega⟩)
    rcases hc_peel with hcW | ⟨w0, hw0W, hcw0⟩
    · -- `c ∈ W`: the prefix `q1` already ends in `W`.
      exact ⟨q1, c, hcW, by rw [hq1_len]; omega, hq1_act, hq1_head, hq1_last⟩
    · -- Descend `c → w0 ∈ W` and splice.
      have hw0_bigQ : w0 ∈ G.ancestralSet bigQ :=
        G.subset_ancestralSet bigQ (hbigQ (by
          simp only [Finset.mem_union]; exact Or.inr (Or.inr hw0W)))
      have hw0n : G.topoOrder w0 ≤ G.topoOrder n := hmax w0 hw0_bigQ
      obtain ⟨dq, hdq2, hdq_head, hdq_last, hdq_act, hdq_first⟩ :=
        G.descent_active_insert hcw0 hcS₀ hw0n
      -- Splice `q1 ++ dq.tail` at the non-collider `c`.
      have hcne : c ∉ insert n S := by
        rw [Finset.mem_insert, not_or]
        refine ⟨?_, fun hcS => hcS₀ (G.subset_ancestralSet S hcS)⟩
        -- `c ≠ n`: `isAncestor c w0` with `topoOrder w0 ≤ topoOrder n` forces `c ≠ n`.
        intro hcn
        have h2 := G.isAncestor_topoOrder_lt hcw0
        rw [hcn] at h2; omega
      obtain ⟨_, hjoin_head, hjoin_last, hjoin_act⟩ :=
        G.chain_join_active (by rw [hq1_len]; omega) hq1_head hq1_last hq1_act
          hdq2 hdq_head hdq_last hdq_act hdq_first hcne
      refine ⟨q1 ++ dq.tail, w0, hw0W, ?_, hjoin_act, hjoin_head, hjoin_last⟩
      rw [List.length_append]; rw [hq1_len]; omega
  · -- ===== SURVIVE branch =====
    refine Or.inr ?_
    -- Every interior collider middle is `S`-activated (Bad empty).
    have hcollS : ∀ (i : ℕ) (hi : i + 2 < p.length),
        G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) →
        p.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro i hi hC
      by_contra hnotanc
      exact hBad ⟨i, by
        simp only [Bad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hi, hC, hnotanc⟩⟩
    have hact' : G.IsActiveWalk (insert n S) p :=
      G.lift_crosscond_to_insert hact hcollS hno_n
    have hedge_in : G.edge (p.get ⟨p.length - 2, by omega⟩) n :=
      G.last_edge_into_max hlen hact hlast hpAnc hmax
    exact ⟨p, hlen, hact', hhead, hlast, hedge_in⟩

end DAG

end Causalean.Graph

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.AcyclicConstruct
public import Causalean.Graph.MarkovEquiv.Defs
public import Causalean.Graph.MarkovEquiv.CoveredReversal.FlipEdge
public import Causalean.Graph.MarkovEquiv.CoveredReversal.ActivePathTransport

/-! # Active-walk surgery for covered-edge reversal

This file proves that the list operations from `ActivePathTransport` preserve active walks under
the required splice conditions. It also shows that `swapPath` preserves endpoints and yields an
active walk when no obstructing triple occurs. `MarkovEquivalence` uses these results to remove
obstructions and transport an arbitrary active walk across a covered-edge reversal.
-/

public section

namespace Causalean.Graph

open Causalean.Graph.MarkovEquiv

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)
variable {G}

/-- Given [a directed acyclic graph, conditioning set, walk, and index](hyp:V,G,Z,p,k), if [the
walk is active](hyp:hact), [the index is positive](hyp:hk0), [its successor lies inside the
walk](hyp:hk), [the vertices on either side are adjacent](hyp:hadj_splice), and [the newly formed
left](hyp:hleft) and [right](hyp:hright) triples satisfy the active-walk criterion, then [removing
the indexed vertex leaves an active walk](goal). -/
theorem isActiveWalk_skipOne {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActiveWalk Z p) (hk0 : 0 < k) (hk : k + 1 < p.length)
    (hadj_splice : G.UAdj (p.get ⟨k - 1, by omega⟩) (p.get ⟨k + 1, hk⟩))
    (hleft : ∀ (hk2 : 2 ≤ k),
      if G.IsCollider (p.get ⟨k - 2, by omega⟩) (p.get ⟨k - 1, by omega⟩)
          (p.get ⟨k + 1, hk⟩) then
        p.get ⟨k - 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k - 1, by omega⟩ ∉ Z)
    (hright : ∀ (hkR : k + 2 < p.length),
      if G.IsCollider (p.get ⟨k - 1, by omega⟩) (p.get ⟨k + 1, by omega⟩)
          (p.get ⟨k + 2, hkR⟩) then
        p.get ⟨k + 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k + 1, by omega⟩ ∉ Z) :
    G.IsActiveWalk Z (skipOne p k) := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [skipOne_length] at hi
    simp only [skipOne, List.get_ofFn]
    by_cases hi0 : i < k
    · by_cases hi1 : i + 1 < k
      · have h := hadj i (by omega)
        simpa [hi0, hi1] using h
      · have hik : i = k - 1 := by omega
        subst i
        have h0 : k - 1 < k := by omega
        have h1 : ¬ (k - 1 + 1 < k) := by omega
        simpa [h0, h1, show k - 1 + 1 + 1 = k + 1 by omega] using hadj_splice
    · have hi1 : ¬ (i + 1 < k) := by omega
      have h := hadj (i + 1) (by omega)
      simpa [hi0, hi1, Nat.add_assoc] using h
  · simp only [skipOne_length] at hi
    simp only [skipOne, List.get_ofFn]
    by_cases hi2 : i + 2 < k
    · have hi0 : i < k := by omega
      have hi1 : i + 1 < k := by omega
      have h := htri i (by omega)
      simpa [hi0, hi1, hi2] using h
    · by_cases hi1 : i + 1 < k
      · have hi0 : i < k := by omega
        have hik : i = k - 2 := by omega
        subst i
        have h0 : k - 2 < k := by omega
        have h1 : k - 2 + 1 < k := by omega
        have h2 : ¬ (k - 2 + 2 < k) := by omega
        have hmid : k - 1 < k := by omega
        simpa [h0, h1, h2, show k - 2 + 1 = k - 1 by omega,
          show k - 2 + 2 + 1 = k + 1 by omega, hmid] using hleft (by omega)
      · by_cases hi0 : i < k
        · have hik : i = k - 1 := by omega
          subst i
          have h0 : k - 1 < k := by omega
          have h1 : ¬ (k - 1 + 1 < k) := by omega
          have h2 : ¬ (k - 1 + 2 < k) := by omega
          have hrightNot : ¬ (k + 1 < k) := by omega
          simpa [h0, h1, h2, show k - 1 + 1 + 1 = k + 1 by omega,
            show k - 1 + 2 + 1 = k + 2 by omega, hrightNot] using hright (by omega)
        · have hi1' : ¬ (i + 1 < k) := by omega
          have hi2' : ¬ (i + 2 < k) := by omega
          have h := htri (i + 1) (by omega)
          simpa [hi0, hi1', hi2', Nat.add_assoc] using h

/-- Given [a directed acyclic graph, conditioning set, walk, and index](hyp:V,G,Z,p,k), if [the
walk is active](hyp:hact), [the index is positive](hyp:hk0), [its successor lies inside the
walk](hyp:hk), [the vertices immediately before and after it agree](hyp:hsame), and [the triple
created by deleting two entries satisfies the active-walk criterion](hyp:hsplice), then [the
shortened walk is active](goal). -/
theorem isActiveWalk_skipTwo {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActiveWalk Z p) (hk0 : 0 < k) (hk : k + 1 < p.length)
    (hsame : p.get ⟨k - 1, by omega⟩ = p.get ⟨k + 1, hk⟩)
    (hsplice : ∀ (hk2 : 2 ≤ k) (hkR : k + 2 < p.length),
      if G.IsCollider (p.get ⟨k - 2, by omega⟩) (p.get ⟨k - 1, by omega⟩)
          (p.get ⟨k + 2, hkR⟩) then
        p.get ⟨k - 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k - 1, by omega⟩ ∉ Z) :
    G.IsActiveWalk Z (skipTwo p k) := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [skipTwo_length] at hi
    simp only [skipTwo, List.get_ofFn]
    by_cases hi0 : i < k
    · by_cases hi1 : i + 1 < k
      · have h := hadj i (by omega)
        simpa [hi0, hi1] using h
      · have hik : i = k - 1 := by omega
        subst i
        have h0 : k - 1 < k := by omega
        have h1 : ¬ (k - 1 + 1 < k) := by omega
        have h := hadj (k + 1) (by omega)
        rw [← hsame] at h
        simpa [h0, h1, Nat.add_assoc, show k - 1 + 3 = k + 2 by omega] using h
    · have hi1 : ¬ (i + 1 < k) := by omega
      have h := hadj (i + 2) (by omega)
      simpa [hi0, hi1, Nat.add_assoc] using h
  · simp only [skipTwo_length] at hi
    simp only [skipTwo, List.get_ofFn]
    by_cases hi2 : i + 2 < k
    · have hi0 : i < k := by omega
      have hi1 : i + 1 < k := by omega
      have h := htri i (by omega)
      simpa [hi0, hi1, hi2] using h
    · by_cases hi1 : i + 1 < k
      · have hi0 : i < k := by omega
        have hik : i = k - 2 := by omega
        subst i
        have h0 : k - 2 < k := by omega
        have h1 : k - 2 + 1 < k := by omega
        have h2 : ¬ (k - 2 + 2 < k) := by omega
        have hmid : k - 1 < k := by omega
        simpa [h0, h1, h2, show k - 2 + 1 = k - 1 by omega,
          show k - 2 + 2 + 2 = k + 2 by omega, hmid] using hsplice (by omega) (by omega)
      · by_cases hi0 : i < k
        · have hik : i = k - 1 := by omega
          subst i
          have h0 : k - 1 < k := by omega
          have h1 : ¬ (k - 1 + 1 < k) := by omega
          have h2 : ¬ (k - 1 + 2 < k) := by omega
          have h := htri (k + 1) (by omega)
          rw [← hsame] at h
          simpa [h0, h1, h2, Nat.add_assoc, show k - 1 + 3 = k + 2 by omega,
            show k - 1 + 4 = k + 3 by omega] using h
        · have hi1' : ¬ (i + 1 < k) := by omega
          have hi2' : ¬ (i + 2 < k) := by omega
          have h := htri (i + 2) (by omega)
          simpa [hi0, hi1', hi2', Nat.add_assoc] using h

omit [DecidableEq V] [Fintype V] in
/-- If [a list of values has distinct first and last entries](hyp:V,p,hne), [an index has a
second successor in the list](hyp:j,hj), and [the entries at the index and second successor
agree](hyp:hback), then [the list has at least four entries](goal). -/
theorem four_le_length_of_backtrack_endpoints_ne {p : List V} {j : ℕ}
    (hne : p.head? ≠ p.getLast?) (hj : j + 2 < p.length)
    (hback : p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩) :
    4 ≤ p.length := by
  by_contra hlt
  have hlen : p.length = 3 := by omega
  have hj0 : j = 0 := by omega
  apply hne
  rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?]
  rw [List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega)]
  congr 1
  simpa [hj0, hlen] using hback

/-- For [a finite directed acyclic graph, the endpoints of a directed edge, a conditioning set,
and a walk](hyp:V,G,a,b,Z,p), if [the directed edge is covered](hyp:hcov), [the original walk is
active](hyp:hact), and [none of its consecutive interior triples obstructs the reversal](hyp:hfork),
then [replacing the affected collider occurrences yields an active walk after the covered-edge
reversal](goal).

When no interior triple of `p` is flip-obstructing, `swapPath` is `flipEdge`-active. The
swap repairs exactly the collider-`a` positions whose activation is lost; genuine
fork-traversals of the covered edge are kept and stay active because `a` (resp. `b`) remains a
non-collider after the flip. This generalises the no-traversal case: a walk with no `a — b`
adjacency at all trivially has no flip-obstructing triple. -/
theorem isActiveWalk_swapPath_of_no_obstruct {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActiveWalk Z p)
    (hfork : ∀ (j : ℕ) (hj : j + 2 < p.length),
      ¬ G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
        (p.get ⟨j + 2, hj⟩)) :
    (flipEdge hcov).IsActiveWalk Z (swapPath hcov Z p) := by
  obtain ⟨hadj, htri⟩ := hact
  constructor
  · -- adjacency
    intro i hi
    have hi1 : i + 1 < p.length := by simpa using hi
    have hi0 : i < p.length := by omega
    have hG : G.UAdj (p.get ⟨i, hi0⟩) (p.get ⟨i + 1, hi1⟩) := hadj i (by simpa using hi)
    rcases swapPath_get_eq hcov Z p i (by omega) hi0 with hvi | ⟨hvi, hai, _, _, hcoli, _⟩
    · rcases swapPath_get_eq hcov Z p (i + 1) (by omega) hi1 with
        hvi1 | ⟨hvi1, hai1, _, _, hcol1, _⟩
      · rw [hvi, hvi1]; exact (flipEdge_sameSkeleton hcov _ _).mp hG
      · -- i+1 swapped: its left collider arm gives `p i → a`, covered ⟹ `p i → b`
        rw [hvi, hvi1]
        have harm : G.edge (p.get ⟨i, hi0⟩) a := by
          have h := hcol1.1
          simp only [Nat.add_sub_cancel] at h
          rw [hai1] at h; exact h
        have hne : p.get ⟨i, hi0⟩ ≠ a := fun h => G.irrefl a (h ▸ harm)
        have hb : G.edge (p.get ⟨i, hi0⟩) b := (hcov.2 _ hne).mp harm
        exact Or.inl ((flipEdge_edge_iff_of_ne_a hcov hne hcov.ne.symm).mpr hb)
    · -- i swapped: its right collider arm gives `p (i+1) → a`, covered ⟹ `p (i+1) → b`
      have harm : G.edge (p.get ⟨i + 1, hi1⟩) a := by
        have h := hcoli.2; rw [hai] at h; exact h
      have hne1 : p.get ⟨i + 1, hi1⟩ ≠ a := fun h => G.irrefl a (h ▸ harm)
      have hb : G.edge (p.get ⟨i + 1, hi1⟩) b := (hcov.2 _ hne1).mp harm
      rcases swapPath_get_eq hcov Z p (i + 1) (by omega) hi1 with hvi1 | ⟨_, hai1, _, _, _⟩
      · rw [hvi, hvi1]
        exact Or.inr ((flipEdge_edge_iff_of_ne_a hcov hne1 hcov.ne.symm).mpr hb)
      · exact absurd hai1 hne1
  · -- collider / activation conditions
    intro j hj
    have hjl : j + 2 < p.length := by simpa using hj
    have hj0 : j < p.length := by omega
    have hj1 : j + 1 < p.length := by omega
    have hjtri := htri j (by simpa using hj)
    have hob := hfork j (by simpa using hj)
    rcases swapPath_get_eq hcov Z p (j + 1) (by omega) hj1 with
      hmid | ⟨hmidb, hmida, _, _, hmcol, hmanc⟩
    · -- middle kept
      by_cases hmida : p.get ⟨j + 1, hj1⟩ = a
      · -- A1: middle = a (kept). Under `hfork`, `a` is a flip-collider iff it is a G-collider,
        -- because a `b` neighbour of `a` would otherwise be a flip-obstructing triple.
        have hjne : p.get ⟨j, hj0⟩ ≠ a := by
          intro h
          have hu := hadj j (by omega); rw [h, hmida] at hu
          rcases hu with he | he <;> exact G.irrefl a he
        have hj2ne : p.get ⟨j + 2, hjl⟩ ≠ a := by
          intro h
          have hu := hadj (j + 1) (by omega); rw [hmida, h] at hu
          rcases hu with he | he <;> exact G.irrefl a he
        rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨_, haj, _⟩
        on_goal 2 => exact absurd haj hjne
        rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with hvj2 | ⟨_, haj2, _⟩
        on_goal 2 => exact absurd haj2 hj2ne
        have hcoll_iff : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩) ↔
            G.IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩) := by
          constructor
          · rintro ⟨hL, hR⟩
            rw [flipEdge_edge] at hL hR
            have hLa : G.edge (p.get ⟨j, hj0⟩) a := by
              rcases hL with ⟨he, _⟩ | ⟨hlb, _⟩
              · exact he
              · exact (hob (Or.inl ⟨hmida, hlb,
                  hR.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩)).elim
            have hRa : G.edge (p.get ⟨j + 2, hjl⟩) a := by
              rcases hR with ⟨he, _⟩ | ⟨hrb, _⟩
              · exact he
              · exact (hob (Or.inr (Or.inl ⟨hmida, hrb, Or.inl hLa⟩))).elim
            exact ⟨hLa, hRa⟩
          · rintro ⟨hL, hR⟩
            exact ⟨by rw [flipEdge_edge]; exact Or.inl ⟨hL, fun h => hjne h.1⟩,
              by rw [flipEdge_edge]; exact Or.inl ⟨hR, fun h => hj2ne h.1⟩⟩
        simp only [hvj, hvj2, hmid, hmida]
        by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩)
        · rw [if_pos (hcoll_iff.mpr hC)]
          by_contra hanc
          have hb : (swapPath hcov Z p).get ⟨j + 1, by simpa using hj1⟩ = b :=
            swapPath_get_b_of hcov Z p (j + 1) (by simpa using hj1) hj1 (by omega) (by omega) hmida
              hanc (by simpa only [Nat.add_sub_cancel, hmida] using hC)
          rw [hmid, hmida] at hb
          exact hcov.ne hb
        · rw [if_neg (fun h => hC (hcoll_iff.mp h))]
          have hcG : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
            rw [hmida]; exact hC
          have ht := hjtri; rw [if_neg hcG] at ht; rwa [hmida] at ht
      · -- A2: middle m = p[j+1] ≠ a (kept)
        rw [hmid]
        -- `m ∉ Z` from the original triple, used in every non-collider branch
        have hmnotZ_of : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) →
            p.get ⟨j + 1, hj1⟩ ∉ Z := fun hc => by
          have ht := hjtri; rw [if_neg hc] at ht; exact ht
        -- helper: a swapped side gives `m → a`, hence the side has no flip-edge into `m`,
        -- and the original triple is not a collider, so `m ∉ Z`.
        have swapped_side : G.edge (p.get ⟨j + 1, hj1⟩) a →
            ¬ (flipEdge hcov).edge b (p.get ⟨j + 1, hj1⟩) := by
          intro hma hbm
          have hmb : p.get ⟨j + 1, hj1⟩ ≠ b := by
            intro h; rw [h] at hma; exact G.asymm hcov.1 hma
          have hmne : p.get ⟨j + 1, hj1⟩ ≠ a := fun h => G.irrefl a (h ▸ hma)
          exact absurd ((flipEdge_edge_into_iff hcov hmida hmb b).mp hbm)
            (G.asymm ((hcov.2 (p.get ⟨j + 1, hj1⟩) hmne).mp hma))
        rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨hvjb, hvja, _, _, hvjcol, _⟩
        · rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with
            hvj2 | ⟨hvj2b, hvj2a, _, _, hvj2col, _⟩
          · -- both sides kept: collider status and activation transfer
            by_cases hmb : p.get ⟨j + 1, hj1⟩ = b
            · -- middle is `b`. Under `hfork`, flip-collider ↔ G-collider at `b`: an `a`
              -- neighbour would otherwise destroy the collider (a flip-obstructing triple).
              have hbiff : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩)
                  (p.get ⟨j + 2, hjl⟩) ↔
                  G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
                constructor
                · rintro ⟨hL, hR⟩
                  rw [flipEdge_edge, hmb] at hL hR
                  refine ⟨?_, ?_⟩
                  · rcases hL with ⟨he, _⟩ | ⟨_, hba⟩
                    · rw [hmb]; exact he
                    · exact absurd hba.symm hcov.ne
                  · rcases hR with ⟨he, _⟩ | ⟨_, hba⟩
                    · rw [hmb]; exact he
                    · exact absurd hba.symm hcov.ne
                · rintro ⟨hL, hR⟩
                  rw [hmb] at hL hR
                  have hjna : p.get ⟨j, hj0⟩ ≠ a := fun h =>
                    hob (Or.inr (Or.inr (Or.inl ⟨hmb, h, hR⟩)))
                  have hj2na : p.get ⟨j + 2, hjl⟩ ≠ a := fun h =>
                    hob (Or.inr (Or.inr (Or.inr ⟨hmb, h, hL⟩)))
                  exact ⟨by rw [flipEdge_edge, hmb]; exact Or.inl ⟨hL, fun h => hjna h.1⟩,
                    by rw [flipEdge_edge, hmb]; exact Or.inl ⟨hR, fun h => hj2na h.1⟩⟩
              rw [hvj, hvj2]
              by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩)
              · rw [if_pos (hbiff.mpr hC)]
                have hmG : p.get ⟨j + 1, hj1⟩ ∈ G.bbZAncestors Z := by
                  have ht := hjtri; rwa [if_pos hC] at ht
                rw [hmb]; exact bbZAncestors_flip_of_b hcov Z (by rw [← hmb]; exact hmG)
              · rw [if_neg (fun h => hC (hbiff.mp h))]
                exact hmnotZ_of hC
            · -- middle ∉ {a, b}: edges into it are flip-invariant
              have hiffL := flipEdge_edge_into_iff hcov hmida hmb (p.get ⟨j, hj0⟩)
              have hiffR := flipEdge_edge_into_iff hcov hmida hmb (p.get ⟨j + 2, hjl⟩)
              rw [hvj, hvj2]
              by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩)
              · rw [if_pos ⟨hiffL.mpr hC.1, hiffR.mpr hC.2⟩]
                have hmG : p.get ⟨j + 1, hj1⟩ ∈ G.bbZAncestors Z := by
                  have ht := hjtri; rwa [if_pos hC] at ht
                exact bbZAncestors_flip_of_ne hcov Z hmida hmG
              · rw [if_neg (fun h => hC ⟨hiffL.mp h.1, hiffR.mp h.2⟩)]
                exact hmnotZ_of hC
          · -- j+2 swapped: p[j+2]=a, collider at j+2 gives m → a
            have hma : G.edge (p.get ⟨j + 1, hj1⟩) a := by
              have h := hvj2col.1; rw [hvj2a] at h; exact h
            have hGc : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) :=
              fun h => G.asymm hma (hvj2a ▸ h.2)
            rw [hvj2b, if_neg (fun h => swapped_side hma h.2)]
            exact hmnotZ_of hGc
        · -- j swapped: p[j]=a, collider at j gives m → a
          have hma : G.edge (p.get ⟨j + 1, hj1⟩) a := by
            have h := hvjcol.2; rw [hvja] at h; exact h
          have hGc : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) :=
            fun h => G.asymm hma (hvja ▸ h.1)
          rw [hvjb, if_neg (fun h => swapped_side hma h.1)]
          exact hmnotZ_of hGc
    · -- middle swapped to b: p[j+1]=a, G-collider at j+1, a ∉ bbZAncestors_flip
      have harmL : G.edge (p.get ⟨j, hj0⟩) a := by
        have h := hmcol.1; simp only [Nat.add_sub_cancel] at h; rw [hmida] at h; exact h
      have harmR : G.edge (p.get ⟨j + 2, hjl⟩) a := by
        have h := hmcol.2; rw [hmida] at h; exact h
      have hjne : p.get ⟨j, hj0⟩ ≠ a := fun h => G.irrefl a (h ▸ harmL)
      have hj2ne : p.get ⟨j + 2, hjl⟩ ≠ a := fun h => G.irrefl a (h ▸ harmR)
      have hbL : G.edge (p.get ⟨j, hj0⟩) b := (hcov.2 _ hjne).mp harmL
      have hbR : G.edge (p.get ⟨j + 2, hjl⟩) b := (hcov.2 _ hj2ne).mp harmR
      rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨_, haj, _⟩
      · rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with hvj2 | ⟨_, haj2, _⟩
        · have hcolF : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) b (p.get ⟨j + 2, hjl⟩) :=
            ⟨(flipEdge_edge_iff_of_ne_a hcov hjne hcov.ne.symm).mpr hbL,
              (flipEdge_edge_iff_of_ne_a hcov hj2ne hcov.ne.symm).mpr hbR⟩
          have haG : a ∈ G.bbZAncestors Z := by
            have hc : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
              rw [hmida]; exact ⟨harmL, harmR⟩
            have ht := hjtri; rw [if_pos hc] at ht; rwa [hmida] at ht
          simp only [hmidb, hvj, hvj2]
          rw [if_pos hcolF]
          exact bbZAncestors_flip_of_lost hcov Z haG hmanc
        · exact absurd haj2 hj2ne
      · exact absurd haj hjne

/-- `swapPath` never touches the first vertex, so it preserves the head. -/
theorem swapPath_head? {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : (swapPath hcov Z p).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  rcases Nat.eq_zero_or_pos p.length with h | h
  · rw [List.getElem?_eq_none (by rw [swapPath_length]; omega), List.getElem?_eq_none (by omega)]
  · rw [List.getElem?_eq_getElem (by rw [swapPath_length]; exact h),
      List.getElem?_eq_getElem h]
    congr 1
    rcases swapPath_get_eq hcov Z p 0 (by rw [swapPath_length]; exact h) h with hh | ⟨_, _, h1, _⟩
    · simpa using hh
    · omega

/-- `swapPath` never touches the last vertex, so it preserves the last element. -/
theorem swapPath_getLast? {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : (swapPath hcov Z p).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, swapPath_length]
  rcases Nat.eq_zero_or_pos p.length with h | h
  · rw [List.getElem?_eq_none (by rw [swapPath_length]; omega), List.getElem?_eq_none (by omega)]
  · rw [List.getElem?_eq_getElem (by rw [swapPath_length]; omega),
      List.getElem?_eq_getElem (by omega)]
    congr 1
    rcases swapPath_get_eq hcov Z p (p.length - 1) (by rw [swapPath_length]; omega) (by omega)
      with hh | ⟨_, _, _, h2, _⟩
    · simpa using hh
    · omega


end DAG

end Causalean.Graph

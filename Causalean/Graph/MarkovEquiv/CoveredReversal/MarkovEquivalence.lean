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
public import Causalean.Graph.MarkovEquiv.CoveredReversal.PathSurgery

/-! # Markov equivalence under one covered-edge reversal

This file assembles the active-walk transport machinery into `markovEquiv_flipEdge`. Obstructing
triples are removed by strictly shortening the walk, while unobstructed walks are handled by
`swapPath`. Applying the argument in both directions shows that reversing one covered edge
preserves every d-separation statement. The finite-chain decomposition that uses this result is
in `Causalean.Graph.MarkovEquiv.Decompose`.
-/

public section

namespace Causalean.Graph

open Causalean.Graph.MarkovEquiv

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)
variable {G}

/-- **Reduction step.** If some interior triple of an active walk is flip-obstructing, then a
strictly shorter active walk with the *same endpoints* exists: a covered edge lets us drop the
obstructing middle vertex (reconnecting its neighbours through the shared parent) or, for an
`a — b — a` / `b — a — b` backtrack, excise the loop. The covered structure keeps every
neighbour's arrowhead orientation, so activity is preserved. The distinct-endpoint hypothesis
`hne` rules out the degenerate full-walk backtrack `[x, m, x]` (whose only excision `[x]` would
be too short); such a walk has equal endpoints and never arises between disjoint `X`, `Y`. -/
private theorem exists_shorter_active_of_obstruct {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActiveWalk Z p) (hne : p.head? ≠ p.getLast?)
    {j : ℕ} (hj : j + 2 < p.length)
    (hbad : G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
      (p.get ⟨j + 2, hj⟩)) :
    ∃ q, G.IsActiveWalk Z q ∧ q.head? = p.head? ∧ q.getLast? = p.getLast? ∧
      2 ≤ q.length ∧ q.length < p.length := by
  by_cases hlr : p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩
  · -- EXCISE the backtrack `[x, m, x]`
    have h4 : 4 ≤ p.length := four_le_length_of_backtrack_endpoints_ne hne hj hlr
    refine ⟨skipTwo p (j + 1), ?_, skipTwo_head? (by omega) (by omega),
      skipTwo_getLast? (by omega) (by omega) hlr, by rw [skipTwo_length]; omega,
      by rw [skipTwo_length]; omega⟩
    refine isActiveWalk_skipTwo hact (by omega) (by omega) hlr (fun hk2 hkR => ?_)
    change
      if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
          (p.get ⟨j + 3, hkR⟩) then
        p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨j, by omega⟩ ∉ Z
    have hjm : j - 1 + 1 = j := by omega
    have hjr : j - 1 + 2 = j + 1 := by omega
    by_cases hC :
        G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
          (p.get ⟨j + 3, hkR⟩)
    · rw [if_pos hC]
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hOld :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          refine ⟨hC.1, ?_⟩
          rw [hm, hl]
          exact hcov.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_pos hOld] at ht
        exact ht
      · have hx_b : p.get ⟨j, by omega⟩ = b := by
          calc
            p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩ := hlr
            _ = b := hr
        have hOld :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          refine ⟨hC.1, ?_⟩
          rw [hm, hx_b]
          exact hcov.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_pos hOld] at ht
        exact ht
      · have hcent :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          rw [hl, hm]
          exact ⟨hcov.1, hrb⟩
        have ht :
            if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) then
              p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 1, by omega⟩ ∉ Z := by
          simpa using hact.2 j (by omega)
        rw [if_pos hcent] at ht
        have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
        have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
        exact hl.symm ▸ haAnc
      · have hx_a : p.get ⟨j, by omega⟩ = a := by
          calc
            p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩ := hlr
            _ = a := hr
        have hcent :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          rw [hm, hr]
          exact ⟨hlb, hcov.1⟩
        have ht :
            if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) then
              p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 1, by omega⟩ ∉ Z := by
          simpa using hact.2 j (by omega)
        rw [if_pos hcent] at ht
        have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
        have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
        exact hx_a.symm ▸ haAnc
    · rw [if_neg hC]
      by_cases hL : G.edge (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
      · have hRmiss : ¬ G.edge (p.get ⟨j + 3, hkR⟩) (p.get ⟨j, by omega⟩) := by
          intro hR
          exact hC ⟨hL, hR⟩
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, hkR⟩) := by
          intro hc
          apply hRmiss
          exact hlr.symm ▸ hc.2
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, hkR⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa [show j + 1 + 1 = j + 2 by omega,
            show j + 1 + 2 = j + 3 by omega] using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        intro hxZ
        exact ht (hlr ▸ hxZ)
      · have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := fun hc => hL hc.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        exact ht
  · -- DROP the obstructing middle `m`
    refine ⟨skipOne p (j + 1), ?_, skipOne_head? (by omega) (by omega),
      skipOne_getLast? (by omega), by rw [skipOne_length]; omega,
      by rw [skipOne_length]; omega⟩
    refine isActiveWalk_skipOne hact (by omega) (by omega) ?adj (fun hk2 => ?left)
      (fun hkR => ?right)
    case adj =>
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        exact Or.inr (by
          change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
          have hl' : p.get ⟨j, by omega⟩ = b := by simpa using hl
          exact hl'.symm ▸ hrb')
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        exact Or.inl (by
          change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
          exact hr.symm ▸ hlb')
      · have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mpr hrb
        exact Or.inr (by
          change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
          have hl' : p.get ⟨j, by omega⟩ = a := by simpa using hl
          exact hl'.symm ▸ hra)
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        exact Or.inl (by
          change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
          exact hr.symm ▸ hla)
    case left =>
      change
        if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
            (p.get ⟨j + 2, hj⟩) then
          p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
        else
          p.get ⟨j, by omega⟩ ∉ Z
      have hjm : j - 1 + 1 = j := by omega
      have hjr : j - 1 + 2 = j + 1 := by omega
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        by_cases hL : G.edge (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
        · have hOld :
              G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := by
            refine ⟨hL, ?_⟩
            rw [hm, hl]
            exact hcov.1
          have hNew :
              G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            refine ⟨hL, ?_⟩
            change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
            have hl' : p.get ⟨j, by omega⟩ = b := by simpa using hl
            exact hl'.symm ▸ hrb'
          rw [if_pos hOld] at ht
          rw [if_pos hNew]
          exact ht
        · have hOld :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := fun hc => hL hc.1
          have hNew :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := fun hc => hL hc.1
          rw [if_neg hOld] at ht
          rw [if_neg hNew]
          exact ht
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          intro hc
          have hal : G.edge a (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hm] at h
            exact h
          exact G.asymm hla hal
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          intro hc
          have hbl : G.edge b (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hr] at h
            exact h
          exact G.asymm hlb' hbl
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · by_cases hC :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩)
        · rw [if_pos hC]
          have hcent :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            rw [hl, hm]
            exact ⟨hcov.1, hrb⟩
          have ht :
              if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                  (p.get ⟨j + 2, hj⟩) then
                p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 1, by omega⟩ ∉ Z := by
            simpa using hact.2 j (by omega)
          rw [if_pos hcent] at ht
          have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
          have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
          exact hl.symm ▸ haAnc
        · rw [if_neg hC]
          have hnotOld :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := by
            intro hc
            have hba : G.edge b a := by
              have h := hc.2
              rw [hm] at h
              rw [hl] at h
              exact h
            exact G.asymm hcov.1 hba
          have ht :
              if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                  (p.get ⟨j + 1, by omega⟩) then
                p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j, by omega⟩ ∉ Z := by
            simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
          rw [if_neg hnotOld] at ht
          exact ht
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          intro hc
          have hbl : G.edge b (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hm] at h
            exact h
          exact G.asymm hlb hbl
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          intro hc
          have hal : G.edge a (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hr] at h
            exact h
          exact G.asymm hla hal
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
    case right =>
      change
        if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
            (p.get ⟨j + 3, by omega⟩) then
          p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
        else
          p.get ⟨j + 2, hj⟩ ∉ Z
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have har : G.edge a (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hm] at h
            exact h
          exact G.asymm har hra
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have hbr : G.edge b (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hl] at h
            exact h
          exact G.asymm hrb' hbr
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        by_cases hR : G.edge (p.get ⟨j + 3, by omega⟩) (p.get ⟨j + 2, hj⟩)
        · have hOld :
              G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            refine ⟨?_, hR⟩
            rw [hm, hr]
            exact hcov.1
          have hNew :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            refine ⟨?_, hR⟩
            change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
            exact hr.symm ▸ hlb'
          rw [if_pos hOld] at ht
          rw [if_pos hNew]
          exact ht
        · have hOld :
              ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := fun hc => hR hc.2
          have hNew :
              ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := fun hc => hR hc.2
          rw [if_neg hOld] at ht
          rw [if_neg hNew]
          exact ht
      · have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mpr hrb
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have hbr : G.edge b (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hm] at h
            exact h
          exact G.asymm hrb hbr
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have har : G.edge a (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hl] at h
            exact h
          exact G.asymm hra har
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        by_cases hC :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩)
        · rw [if_pos hC]
          have hcent :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            rw [hm, hr]
            exact ⟨hlb, hcov.1⟩
          have ht :
              if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                  (p.get ⟨j + 2, hj⟩) then
                p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 1, by omega⟩ ∉ Z := by
            simpa using hact.2 j (by omega)
          rw [if_pos hcent] at ht
          have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
          have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
          exact hr.symm ▸ haAnc
        · rw [if_neg hC]
          have hnotOld :
              ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            intro hc
            have hba : G.edge b a := by
              have h := hc.1
              rw [hm] at h
              rw [hr] at h
              exact h
            exact G.asymm hcov.1 hba
          have ht :
              if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                  (p.get ⟨j + 3, by omega⟩) then
                p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 2, hj⟩ ∉ Z := by
            simpa using hact.2 (j + 1) (by omega)
          rw [if_neg hnotOld] at ht
          exact ht

/-- **Assembly.** Every active walk in `G` yields an active walk in `flipEdge` with the same
endpoints. By strong induction on length: if no interior triple is flip-obstructing, the swap
`swapPath` works directly; otherwise the reduction step shortens the walk and we recurse. -/
private theorem exists_flip_active_of_active {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) :
    ∀ (p : List V), G.IsActiveWalk Z p → p.head? ≠ p.getLast? → 2 ≤ p.length →
    ∃ q, (flipEdge hcov).IsActiveWalk Z q ∧ q.head? = p.head? ∧
      q.getLast? = p.getLast? ∧ 2 ≤ q.length := by
  have H : ∀ (n : ℕ) (p : List V), p.length = n → G.IsActiveWalk Z p →
      p.head? ≠ p.getLast? → 2 ≤ p.length →
      ∃ q, (flipEdge hcov).IsActiveWalk Z q ∧ q.head? = p.head? ∧
        q.getLast? = p.getLast? ∧ 2 ≤ q.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro p hpn hact hne hlen
      by_cases hbad : ∃ (j : ℕ) (hj : j + 2 < p.length),
          G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
      · obtain ⟨j, hj, hb⟩ := hbad
        obtain ⟨q, hqact, hqh, hql, hq2, hqlt⟩ :=
          exists_shorter_active_of_obstruct hcov hact hne hj hb
        obtain ⟨q', hq'a, hq'h, hq'l, hq'2⟩ :=
          IH q.length (by omega) q rfl hqact (by rw [hqh, hql]; exact hne) hq2
        exact ⟨q', hq'a, hq'h.trans hqh, hq'l.trans hql, hq'2⟩
      · push_neg at hbad
        refine ⟨swapPath hcov Z p,
          isActiveWalk_swapPath_of_no_obstruct hcov hact (fun j hj => hbad j hj),
          swapPath_head? hcov Z p, swapPath_getLast? hcov Z p, ?_⟩
        rw [swapPath_length]; exact hlen
  intro p hact hne hlen
  exact H p.length p rfl hact hne hlen

/-- Active-walk connectivity is transported across one covered-edge reversal: the AMP
covered-reversal walk-surgery step, assembled from the fork-tolerant swap and the
backtrack/drop reduction. -/
private theorem hasActiveWalk_flipEdge_of_isCoveredEdge {a b : V}
    (hcov : G.IsCoveredEdge a b) (X Y Z : Finset V)
    (hXY : Disjoint X Y) :
    G.HasActiveWalk X Y Z → (flipEdge hcov).HasActiveWalk X Y Z := by
  rintro ⟨p, hlen, hact, hhead, hlast⟩
  -- disjoint `X`, `Y` force distinct endpoints
  have hne : p.head? ≠ p.getLast? := by
    intro h
    rw [Finset.mem_image] at hhead hlast
    obtain ⟨x, hxX, hx⟩ := hhead
    obtain ⟨y, hyY, hy⟩ := hlast
    have hxy : y = x := (Option.some.inj (by rw [hx, h, ← hy] : some x = some y)).symm
    exact Finset.disjoint_left.mp hXY hxX (hxy ▸ hyY)
  obtain ⟨q, hqact, hqh, hql, hq2⟩ := exists_flip_active_of_active hcov Z p hact hne hlen
  refine ⟨q, hq2, hqact, ?_, ?_⟩
  · rw [hqh]; exact hhead
  · rw [hql]; exact hlast

/-- **The analytic core (AMP, per-step invariance).** In a DAG `G`, if [the edge `a → b` is
covered — every other parent of `b` is also a parent of `a`, and vice versa](hyp:hcov), then
[the DAG obtained by reversing that edge to `b → a` is Markov equivalent to `G`: the two graphs
license exactly the same d-separation statements](goal). This is the single-edge kernel used by
the covered-reversal proof of the Verma--Pearl hard direction.

By `not_dSep_iff_hasActiveWalk` this is equivalent to: a covered-edge reversal preserves
active-walk connectivity (`HasActiveWalk`). Since the reversed edge `b → a` is again covered
in `flipEdge` and flipping it back yields `G`, it suffices to transport an active walk one way.
The only edge whose orientation changes is `a — b`; a walk not traversing it keeps its
collider pattern, and one that does is rerouted through the shared parents of `a` and `b`
(`hcov.2`), whose collider-activation (an `bbZAncestors Z` membership) is preserved because
`a` and `b` reach `Z` through the same ancestors. -/
theorem markovEquiv_flipEdge {a b : V} (hcov : G.IsCoveredEdge a b) :
    MarkovEquiv G (flipEdge hcov) := by
  intro X Y Z
  by_cases hXY : Disjoint X Y
  · by_cases hXZ : Disjoint X Z
    · by_cases hYZ : Disjoint Y Z
      · have hAP : G.HasActiveWalk X Y Z ↔ (flipEdge hcov).HasActiveWalk X Y Z := by
          constructor
          · exact hasActiveWalk_flipEdge_of_isCoveredEdge hcov X Y Z hXY
          · intro hp
            have hp₂ : (flipEdge (flipEdge_isCoveredEdge_back hcov)).HasActiveWalk X Y Z :=
              @hasActiveWalk_flipEdge_of_isCoveredEdge V _ _ (flipEdge hcov) b a
                (flipEdge_isCoveredEdge_back hcov) X Y Z hXY hp
            exact (hasActiveWalk_edge_congr (flipEdge_flipEdge_edge hcov) X Y Z).mp hp₂
        apply not_iff_not.mp
        calc
          ¬ G.dSep X Y Z ↔ G.HasActiveWalk X Y Z :=
            not_dSep_iff_hasActiveWalk G X Y Z hXY hXZ hYZ
          _ ↔ (flipEdge hcov).HasActiveWalk X Y Z := hAP
          _ ↔ ¬ (flipEdge hcov).dSep X Y Z :=
            (not_dSep_iff_hasActiveWalk (flipEdge hcov) X Y Z hXY hXZ hYZ).symm
      · exact iff_of_false (fun h => hYZ h.2.2.1) (fun h => hYZ h.2.2.1)
    · exact iff_of_false (fun h => hXZ h.2.1) (fun h => hXZ h.2.1)
  · exact iff_of_false (fun h => hXY h.1) (fun h => hXY h.1)


end DAG

end Causalean.Graph

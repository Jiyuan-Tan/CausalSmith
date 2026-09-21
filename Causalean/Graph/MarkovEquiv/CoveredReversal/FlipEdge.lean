/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.AcyclicConstruct
public import Causalean.Graph.MarkovEquiv.Defs

/-! # Constructing a covered-edge reversal

This file defines covered edges and constructs `DAG.flipEdge` by reversing one of them. It proves
that the flipped relation is acyclic and that the resulting DAG has the same skeleton and
immoralities as the original graph. Active-walk transport across this construction is developed
in `ActivePathTransport` and `PathSurgery`; the resulting Markov-equivalence theorem is in
`MarkovEquivalence`.
-/

@[expose] public section

namespace Causalean.Graph

open Causalean.Graph.MarkovEquiv

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and
[two vertices](hyp:a,b), [the covered-edge condition](goal) holds exactly when there is a
directed edge from the first vertex to the second and, for every other vertex, that vertex has
an edge into the first if and only if it has an edge into the second.

Then the parent set of the first vertex equals the parent set of the second after removal of the
first vertex. Covered edges are exactly the reversible (unprotected) ones. -/
def IsCoveredEdge (a b : V) : Prop :=
  G.edge a b ∧ ∀ c, c ≠ a → (G.edge c a ↔ G.edge c b)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and
[two vertices](hyp:a,b), [the edge relation with one deletion](goal) holds for two queried
vertices exactly when the original graph has an edge from the first queried vertex to the second
and the queried edge is not the edge from the first specified vertex to the second. -/
def flipMinus (a b : V) : V → V → Prop :=
  fun u w => G.edge u w ∧ ¬ (u = a ∧ w = b)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and
[two vertices](hyp:a,b), [the edge relation with one reversal](goal) holds for two queried
vertices exactly when the original graph has the queried edge other than the edge from the first
specified vertex to the second, or the queried edge is the reversed edge from the second
specified vertex to the first. -/
def flipRel (a b : V) : V → V → Prop :=
  fun u w => G.flipMinus a b u w ∨ (u = b ∧ w = a)

variable {G}

/-- A `flipMinus`-edge is in particular a `G`-edge. -/
theorem flipMinus_le {a b u w : V} (h : G.flipMinus a b u w) : G.edge u w := h.1

/-- A directed `flipMinus`-path strictly increases the topological order. -/
theorem topoOrder_lt_of_flipMinus_transGen {a b u w : V}
    (h : Relation.TransGen (G.flipMinus a b) u w) : G.topoOrder u < G.topoOrder w := by
  induction h with
  | single he => exact G.topoOrder_lt _ _ he.1
  | tail _ he ih => exact lt_trans ih (G.topoOrder_lt _ _ he.1)

/-- A covered edge is genuinely an edge `a → b`, so `a ≠ b`. -/
theorem IsCoveredEdge.ne {a b : V} (h : G.IsCoveredEdge a b) : a ≠ b := by
  rintro rfl; exact G.irrefl _ h.1

/-- **Reversing a covered edge keeps the graph acyclic.** The transitive closure of the
flipped relation is irreflexive. Key step (AMP Lemma 3.1): a directed `G`-path `a ⇝ b` of
length ≥ 2 would end at a parent `c ≠ a` of `b`, hence (covered) a parent of `a`, closing a
`G`-cycle; so no such detour exists and the single reversal introduces no cycle. -/
theorem flipRel_acyclic {a b : V} (hcov : G.IsCoveredEdge a b) :
    ∀ v, ¬ Relation.TransGen (G.flipRel a b) v v := by
  -- last-step destructor for a transitive-closure path
  have transGen_last : ∀ {z : V}, Relation.TransGen (G.flipMinus a b) a z →
      G.flipMinus a b a z ∨
        ∃ c, Relation.TransGen (G.flipMinus a b) a c ∧ G.flipMinus a b c z := by
    intro z h
    induction h with
    | single h => exact Or.inl h
    | tail h1 h2 _ => exact Or.inr ⟨_, h1, h2⟩
  -- No `flipMinus`-detour from `a` to `b`: the last vertex `c` of such a path is a parent of
  -- `b` other than `a`, hence (covered) a parent of `a`, closing a `G`-cycle.
  have hnodetour : ¬ Relation.TransGen (G.flipMinus a b) a b := by
    intro h
    rcases transGen_last h with hab | ⟨c, hac, hcb⟩
    · exact hab.2 ⟨rfl, rfl⟩
    · have hca' : c ≠ a := fun hc => hcb.2 ⟨hc, rfl⟩
      have hca : G.edge c a := (hcov.2 c hca').mpr hcb.1
      have l1 : G.topoOrder a < G.topoOrder c := topoOrder_lt_of_flipMinus_transGen hac
      have l2 : G.topoOrder c < G.topoOrder a := G.topoOrder_lt _ _ hca
      omega
  -- Any flipped-walk either avoids `b → a` (so it is a `flipMinus`-walk) or it splits as
  -- `x ⇝ b` (before the first `b → a`) and `a ⇝ y` (after), both `flipMinus`-reachable.
  have hP : ∀ {x y}, Relation.TransGen (G.flipRel a b) x y →
      Relation.TransGen (G.flipMinus a b) x y ∨
        (Relation.ReflTransGen (G.flipMinus a b) x b ∧
          Relation.ReflTransGen (G.flipMinus a b) a y) := by
    intro x y h
    induction h with
    | single hxy =>
      rcases hxy with h0 | ⟨hxb, hya⟩
      · exact Or.inl (Relation.TransGen.single h0)
      · subst hxb; subst hya
        exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | @tail c y _ hcy ih =>
      rcases hcy with h0 | ⟨hcb, hya⟩
      · rcases ih with hl | ⟨hr1, hr2⟩
        · exact Or.inl (hl.tail h0)
        · exact Or.inr ⟨hr1, hr2.tail h0⟩
      · subst hcb; subst hya
        rcases ih with hl | ⟨hr1, _hr2⟩
        · exact Or.inr ⟨hl.to_reflTransGen, Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨hr1, Relation.ReflTransGen.refl⟩
  intro v hv
  rcases hP hv with hl | ⟨hr1, hr2⟩
  · exact absurd (topoOrder_lt_of_flipMinus_transGen hl) (lt_irrefl _)
  · have hab : Relation.ReflTransGen (G.flipMinus a b) a b := hr2.trans hr1
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with heq | htr
    · exact hcov.ne heq.symm
    · exact hnodetour htr

/-- For [a finite vertex population](hyp:V), [a directed acyclic graph](hyp:G),
[two vertices](hyp:a,b), and [evidence that their directed edge is covered](hyp:hcov),
[the covered-edge reversal graph](goal) is the directed acyclic graph obtained by replacing the
edge from the first vertex to the second with the edge from the second to the first. -/
noncomputable def flipEdge {a b : V} (hcov : G.IsCoveredEdge a b) : DAG V :=
  DAG.ofAcyclic (G.flipRel a b) (flipRel_acyclic hcov)

/-- In the graph obtained by reversing a covered edge, the edges are exactly the old edges
except for deleting `a → b` and adding `b → a`. -/
@[simp] theorem flipEdge_edge {a b : V} (hcov : G.IsCoveredEdge a b) (u w : V) :
    (flipEdge hcov).edge u w ↔ (G.edge u w ∧ ¬ (u = a ∧ w = b)) ∨ (u = b ∧ w = a) := by
  rfl

/-- **Reversing a covered edge preserves the skeleton.** The undirected adjacency is
unchanged: only the orientation of the single edge `a — b` flips. -/
theorem flipEdge_sameSkeleton {a b : V} (hcov : G.IsCoveredEdge a b) :
    SameSkeleton G (flipEdge hcov) := by
  intro u w
  simp only [DAG.UAdj, flipEdge_edge]
  constructor
  · rintro (h | h)
    · by_cases hab : u = a ∧ w = b
      · obtain ⟨rfl, rfl⟩ := hab; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨h, hab⟩)
    · by_cases hab : w = a ∧ u = b
      · obtain ⟨rfl, rfl⟩ := hab; exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, hab⟩)
  · rintro ((⟨h, _⟩ | ⟨rfl, rfl⟩) | (⟨h, _⟩ | ⟨rfl, rfl⟩))
    · exact Or.inl h
    · exact Or.inr hcov.1
    · exact Or.inr h
    · exact Or.inl hcov.1

/-- For [a finite directed acyclic graph and two vertices](hyp:V,G,a,b), if [the directed edge
between them is covered](hyp:hcov), then [reversing that edge preserves every unshielded
collider](goal).

**Reversing a covered edge preserves the immoralities.** Because `a` and `b` share all
other parents, no v-structure is created or destroyed by the single reversal. -/
theorem flipEdge_sameImmoralities {a b : V} (hcov : G.IsCoveredEdge a b) :
    SameImmoralities G (flipEdge hcov) := by
  have hU : ∀ x y, G.UAdj x y ↔ (flipEdge hcov).UAdj x y := flipEdge_sameSkeleton hcov
  intro p q r
  constructor
  · rintro ⟨hpq, hrq, hnadj, hpr⟩
    have hpq' : (flipEdge hcov).edge p q := by
      rw [flipEdge_edge]; left; refine ⟨hpq, ?_⟩
      rintro ⟨hpa, hqb⟩
      -- collider `a → b ← r`: covered forces `r → a`, contradicting non-adjacency
      rw [hpa] at hpr hnadj; rw [hqb] at hrq
      exact hnadj (Or.inr ((hcov.2 r (Ne.symm hpr)).mpr hrq))
    have hrq' : (flipEdge hcov).edge r q := by
      rw [flipEdge_edge]; left; refine ⟨hrq, ?_⟩
      rintro ⟨hra, hqb⟩
      -- collider `p → b ← a`: covered forces `p → a`, contradicting non-adjacency
      rw [hra] at hpr hnadj; rw [hqb] at hpq
      exact hnadj (Or.inl ((hcov.2 p hpr).mpr hpq))
    exact ⟨hpq', hrq', fun h => hnadj ((hU p r).mpr h), hpr⟩
  · rintro ⟨hpq, hrq, hnadj, hpr⟩
    rw [flipEdge_edge] at hpq hrq
    have hnadjG : ¬ G.UAdj p r := fun h => hnadj ((hU p r).mp h)
    have hpqG : G.edge p q := by
      rcases hpq with ⟨h, _⟩ | ⟨hpb, hqa⟩
      · exact h
      · exfalso
        rcases hrq with ⟨hra, _⟩ | ⟨hrb, _⟩
        · rw [hqa] at hra
          have hrne : r ≠ a := fun heq => G.irrefl _ (heq ▸ hra)
          apply hnadjG; rw [hpb]; exact Or.inr ((hcov.2 r hrne).mp hra)
        · exact hpr (hpb.trans hrb.symm)
    have hrqG : G.edge r q := by
      rcases hrq with ⟨h, _⟩ | ⟨hrb, hqa⟩
      · exact h
      · exfalso
        rcases hpq with ⟨hpa, _⟩ | ⟨hpb, _⟩
        · rw [hqa] at hpa
          have hpne : p ≠ a := fun heq => G.irrefl _ (heq ▸ hpa)
          apply hnadjG; rw [hrb]; exact Or.inl ((hcov.2 p hpne).mp hpa)
        · exact hpr (hpb.trans hrb.symm)
    exact ⟨hpqG, hrqG, hnadjG, hpr⟩

end DAG

end Causalean.Graph

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.PiUnion
import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec

/-! # Mass-level IDENTIFY functionals

This file contains the finite, mass-level coordinate operations used by the
recursive ID recovery.  The graph helpers `SWIGGraph.topoLinearOrder`,
`SWIGGraph.nodesAt`, `SWIGGraph.nodeIndex`, and `SWIGGraph.prefixIn` enumerate
selected SWIG nodes in topological order.  The mass operations
`SCM.marginalizeOn` and `SCM.extractDistrict` implement the coordinate
marginalization and district-ratio extraction steps.  The recursion
`SCM.identifyMassRec` then combines induced ancestral restriction, hedge
detection, and district extraction, with simp equations for its base, hedge, and
recursive branches.
-/

set_option linter.unusedFintypeInType false

namespace Causalean

open scoped BigOperators ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SWIGGraph

/-- For [a finite collection of distinguishable base-variable labels](hyp:N) and [a SWIG graph](hyp:G), the [topological linear order](goal) orders its nodes by their positions in the graph's topological ordering. -/
noncomputable def topoLinearOrder (G : SWIGGraph N) : LinearOrder (SWIGNode N) :=
  LinearOrder.lift' G.dag.topoOrder G.dag.topoOrder_injective

/-- For [a finite collection of distinguishable base-variable labels](hyp:N), [a SWIG graph](hyp:G), [a finite set of graph nodes](hyp:D), and [a position from zero through one less than the set's size](hyp:i), the [node-at-position selector](goal) returns the node occupying that position when the set is sorted in graph topological order. -/
noncomputable def nodesAt (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (i : Fin D.card) : {v // v ∈ D} := by
  classical
  letI := G.topoLinearOrder
  exact D.orderIsoOfFin rfl i

/-- For [a finite collection of distinguishable base-variable labels](hyp:N), [a SWIG graph](hyp:G), [a finite set of graph nodes](hyp:D), and [a node belonging to that set](hyp:v), the [node-position selector](goal) returns that node's position when the set is sorted in graph topological order. -/
noncomputable def nodeIndex (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (v : {v // v ∈ D}) : Fin D.card := by
  classical
  letI := G.topoLinearOrder
  exact (D.orderIsoOfFin rfl).symm v

/-- For [a finite collection of distinguishable base-variable labels](hyp:N), [a SWIG graph](hyp:G), [a finite set of graph nodes](hyp:D), and [a nonnegative integer](hyp:n), the [topological prefix](goal) consists of the nodes in that set whose topological positions are strictly less than $n$. -/
noncomputable def prefixIn (G : SWIGGraph N) (D : Finset (SWIGNode N)) (n : ℕ) :
    Finset (SWIGNode N) :=
  D.filter (fun v => if h : v ∈ D then (G.nodeIndex D ⟨v, h⟩).val < n else False)

/-- Every node in a topological prefix of a selected node set belongs to the selected node set. -/
lemma prefixIn_subset (G : SWIGGraph N) (D : Finset (SWIGNode N)) (n : ℕ) :
    G.prefixIn D n ⊆ D := by
  intro v hv
  exact (Finset.mem_filter.mp hv).1

end SWIGGraph

namespace SCM.ID

/-- The induced ancestral set lies inside the ambient observed node set. -/
theorem inducedAncestral_subset_left
    (G : SWIGGraph N) (T C : Finset (SWIGNode N)) :
    inducedAncestral G T C ⊆ T := by
  intro v hv
  unfold inducedAncestral at hv
  have hvObs : v ∈ (G.induce T).observed := (Finset.mem_inter.mp hv).2
  exact (Finset.mem_inter.mp (by simpa [SWIGGraph.induce] using hvObs)).1

/-- If `C` is observed and contained in `T`, then it is contained in its induced
ancestral set inside `T`. -/
theorem subset_inducedAncestral
    (G : SWIGGraph N) {T C : Finset (SWIGNode N)}
    (hCT : C ⊆ T) (hCobs : C ⊆ G.observed) :
    C ⊆ inducedAncestral G T C := by
  intro v hv
  unfold inducedAncestral
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact (G.induce T).dag.subset_ancestralSet C hv
  · simp [SWIGGraph.induce, hCT hv, hCobs hv]

/-- The containing c-component is always a set of observed nodes. -/
theorem containingCComponent_subset_observed
    (G : SWIGGraph N) (S : Finset (SWIGNode N)) :
    containingCComponent G S ⊆ G.observed := by
  classical
  by_cases hS : S.Nonempty
  · simpa [containingCComponent, hS] using G.cComponentOf_subset_observed hS.choose
  · simp [containingCComponent, hS]

/-- A containing c-component in an induced graph lies inside the inducing set. -/
theorem containingCComponent_induce_subset
    (G : SWIGGraph N) (A C : Finset (SWIGNode N)) :
    containingCComponent (G.induce A) C ⊆ A := by
  intro v hv
  have hvObs := containingCComponent_subset_observed (G.induce A) C hv
  exact (Finset.mem_inter.mp (by simpa [SWIGGraph.induce] using hvObs)).1

end SCM.ID

namespace SCM

/-- For [an ambient set of graph nodes](hyp:O), [a subset of coordinates to eliminate](hyp:W) that is [contained in the ambient set](hyp:hW), and [a nonnegative extended-real mass function on assignments to the ambient set](hyp:q), the [marginalized mass function](goal) maps each ambient assignment [to the sum of the mass function over all assignments on the eliminated coordinates, replacing those coordinates in the evaluation point](step:1). -/
noncomputable def marginalizeOn [∀ n, Fintype (Ω n)]
    (O W : Finset (SWIGNode N)) (hW : W ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x => ∑ y : ValuesOn W (swigΩ Ω), q (overrideOn x y)

/-- For [an ambient node set](hyp:O), [a SWIG graph](hyp:G'), [a node set](hyp:A), [a district node set](hyp:C'), [the condition that the node set is contained in the ambient set](hyp:hA), and [a nonnegative extended-real mass function on ambient assignments](hyp:q), the [district factor](goal) maps each ambient assignment [to the product, over the nodes of the district in graph topological order, of the ratio of the two adjacent prefix marginals obtained by summing out the remaining nodes of $A$](step:1). -/
noncomputable def extractDistrict [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin A.card => (G'.nodesAt A i).val ∈ C'),
      marginalizeOn O (A \ G'.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x /
        marginalizeOn O (A \ G'.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x

/-- For [an ambient node set](hyp:O) and [a SWIG graph](hyp:G), the [mass-level IDENTIFY recursion](goal) maps every target node set, district node set, proof that the target set is contained in the ambient set, and nonnegative extended-real mass function on ambient assignments to a mass function on ambient assignments. It [first forms the induced ancestral set and its containment proof](step:1), then returns the marginal eliminating the target coordinates outside the district when that ancestral set equals the district, returns the original mass function when it equals the target set, and otherwise recurses after extracting the containing district factor from the appropriate marginal.

The hedge branch returns the current mass function; successful reachability proofs never use that branch. -/
noncomputable def identifyMassRec [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G : SWIGGraph N) :
    (T C : Finset (SWIGNode N)) → (hT : T ⊆ O) →
      (q : ValuesOn O (swigΩ Ω) → ENNReal) →
        ValuesOn O (swigΩ Ω) → ENNReal
  | T, C, hT, q =>
    let A := ID.inducedAncestral G T C
    let hA : A ⊆ O := fun _ hv =>
      hT (ID.inducedAncestral_subset_left G T C hv)
    if _hAC : A = C then
      marginalizeOn O (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q
    else if _hAT : A = T then
      q
    else
      let C₁ := ID.containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ O := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C
          (ID.containingCComponent_induce_subset G A C hv))
      identifyMassRec O G C₁ C hC₁
        (extractDistrict O (G.induce A) A C₁ hA
          (marginalizeOn O (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q))
termination_by T _ _ _ => T.card
decreasing_by
  classical
  have hAsubT : A ⊆ T := ID.inducedAncestral_subset_left G T C
  have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, _hAT⟩
  have hC₁subA : C₁ ⊆ A := ID.containingCComponent_induce_subset G A C
  exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
    (Finset.card_lt_card hAssubT)

/-- For [a target set `T` contained in the observed coordinates](hyp:hT), if
[the graph-induced ancestral set of `T` relative to `C` already equals
`C`](hyp:hAC), then [the mass-level IDENTIFY recursion `identifyMassRec` on `T`
stops immediately and returns the marginal of the input mass function `q`
obtained by summing out the coordinates in `T \ C`](goal). -/
@[simp] theorem identifyMassRec_base [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C = C) :
    identifyMassRec M.observed G T C hT q =
      marginalizeOn M.observed (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q := by
  rw [identifyMassRec]
  simp [hAC]

/-- For [a target set `T` contained in the observed coordinates](hyp:hT), if
[the graph-induced ancestral set of `T` relative to `C` does not equal
`C`](hyp:hAC) but [it equals `T` itself](hyp:hAT) — the hedge case, reached only
after the base case has failed — then [the recursion `identifyMassRec` on `T`
returns the input mass function `q` unchanged](goal). -/
@[simp] theorem identifyMassRec_hedge [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C ≠ C)
    (hAT : ID.inducedAncestral G T C = T) :
    identifyMassRec M.observed G T C hT q = q := by
  have hTC : T ≠ C := by
    intro h
    exact hAC (hAT.trans h)
  rw [identifyMassRec]
  simp [hAT, hTC]

/-- For [a target set `T` contained in the observed coordinates](hyp:hT), if
[the graph-induced ancestral set of `T` relative to `C` does not equal
`C`](hyp:hAC) and [does not equal `T` either](hyp:hAT) — i.e. neither the base
nor the hedge case applies — then [the recursion `identifyMassRec` on `T`
unfolds one step: it extracts, from the mass function `q` marginalized onto
the induced ancestral set, the district factor of the c-component of `C`
inside that induced ancestral graph, and recurses on that district](goal). -/
@[simp] theorem identifyMassRec_step [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C ≠ C)
    (hAT : ID.inducedAncestral G T C ≠ T) :
    identifyMassRec M.observed G T C hT q =
      let A := ID.inducedAncestral G T C
      let hA : A ⊆ M.observed := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C hv)
      let C₁ := ID.containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ M.observed := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C
          (ID.containingCComponent_induce_subset G A C hv))
      identifyMassRec M.observed G C₁ C hC₁
        (extractDistrict M.observed (G.induce A) A C₁ hA
          (marginalizeOn M.observed (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q)) := by
  rw [identifyMassRec]
  simp [hAC, hAT]

end SCM
end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.MarkovEquiv.Defs
public import Causalean.Graph.MarkovEquiv.Readoff
public import Causalean.Graph.MarkovEquiv.Transfer
public import Causalean.Graph.MarkovEquiv.Moralization

/-!
# Markov equivalence of DAGs (Verma–Pearl)

The Verma–Pearl characterization of Markov equivalence (Verma & Pearl, *Equivalence and
synthesis of causal models*, 1990): two directed acyclic graphs on the same finite vertex set
imply exactly the same d-separation statements, and hence the same conditional-independence
constraints, if and only if they have the same skeleton (the same adjacent pairs) and the same
v-structures (colliders a → b ← c with a and c non-adjacent). The forward direction reads the
skeleton and v-structures off the d-separation relation; the converse shows that two such graphs
are linked by reversals of covered edges, each of which preserves every d-separation. The
development also proves the moralization criterion: for pairwise-disjoint sets, d-separation is
the same as separation in the moral graph of the ancestral set.

## Main results

* `MarkovEquiv` (`Defs.lean`) — two DAGs declare the same d-separations.
* `markovEquiv_iff_sameSkeleton_sameImmoralities` (this file) — **the flagship.** Two DAGs
  are Markov equivalent iff they have the same skeleton (`SameSkeleton`, undirected
  adjacency) and the same v-structures (`SameImmoralities`, colliders with non-adjacent
  parents). The constraint-based characterization underlying PC/FCI/GES and the CPDAG.
* `DAG.dSep_iff_moralSep` (`Moralization.lean`) — the Lauritzen moralization
  criterion: d-separation in a DAG is equivalent to graph separation in the
  moral graph of the ancestral closure.

## Supporting machinery

`Readoff.lean` (easy direction — skeleton and v-structures are read off the d-separation
relation), `Transfer.lean` (hard direction — same skeleton + v-structures transfer every
d-separation), and `Moralization.lean` (the ancestral moral graph criterion for
d-separation). The development reuses the existing d-separation engine
(`Causalean.Graph.DSep`).

The higher-layer companion `Causalean.SCM.Do.MarkovEquivDistributional` connects
this graph notion to distributions and proves `SCM.distMarkovEquiv_of_markovEquiv`;
it is not imported by this file.
-/

public section

namespace Causalean.Graph

open Causalean.Graph.MarkovEquiv

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Verma–Pearl (1990).** For [two DAGs `G₁`, `G₂` on the same vertex set](hyp:G₁,G₂),
[they are Markov equivalent — they declare exactly the same d-separations, hence impose the
same conditional-independence constraints — if and only if they have the same skeleton and
the same v-structures (immoralities)](goal).

The easy direction reads the skeleton and v-structures from d-separation. The hard
direction is supplied by the covered-edge reversal route: same-skeleton/same-immorality
DAGs are connected by covered edge reversals, each preserving every d-separation. -/
theorem markovEquiv_iff_sameSkeleton_sameImmoralities (G₁ G₂ : DAG V) :
    MarkovEquiv G₁ G₂ ↔ SameSkeleton G₁ G₂ ∧ SameImmoralities G₁ G₂ :=
  ⟨sameSkeleton_sameImmoralities_of_markovEquiv,
    fun ⟨hskel, himm⟩ => markovEquiv_of_sameSkeleton_sameImmoralities hskel himm⟩

end Causalean.Graph

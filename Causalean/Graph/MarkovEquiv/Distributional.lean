/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Defs
import Causalean.SCM.Do.GlobalMarkov

/-! # Markov equivalence — the distributional I-map layer

The graph-level `MarkovEquiv` (same d-separations) is connected here to *distributions*.
A distribution `μ` is a **global I-map** of a DAG `G` when every d-separation of `G` is a
conditional independence of `μ`; it is **faithful** to `G` when, conversely, every such
conditional independence reflects an actual d-separation. The global Markov property
(`full_globalMarkov`) says every structural causal model is a global I-map of its own DAG —
this is the bridge from graphs to distributions, restated here as `isGlobalIMap_dag_self`.

The theorem in this file proves the easy direction:

* `distMarkovEquiv_of_markovEquiv`: graph-level Markov equivalence implies
  distributional Markov equivalence (the two DAGs are I-maps of exactly the same
  distributions). This is immediate from the definitions: the I-map condition is the same
  predicate when the d-separations agree.

The d-separation triples handled here are pairwise disjoint, matching the global Markov
property; this is the standard setting for the I-map and faithfulness notions. The file
states the I-map direction needed by the public Markov-equivalence API and leaves
faithfulness-existence results outside this layer.
-/

namespace Causalean

open scoped MeasureTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

/-- For [a directed acyclic graph on the split nodes](hyp:G), [a structural causal model](hyp:M), and [a finite measure on that model's random-value space](hyp:μ), the [global I-map property](goal) means that, for every three finite sets of random nodes contained respectively in the model's random variables, d-separation of the first and second sets given the third in the graph implies their conditional independence under the measure.

The required pairwise disjointness is already part of d-separation. -/
def IsGlobalIMap (G : DAG (SWIGNode N)) (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ (X Y Z : Finset (SWIGNode N)) (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars),
    G.dSep X Y Z → FullCondIndep M X Y Z hX hY hZ μ

/-- For [a directed acyclic graph on the split nodes](hyp:G), [a structural causal model](hyp:M), and [a finite measure on that model's random-value space](hyp:μ), the [faithfulness property](goal) means that, for every three pairwise-disjoint finite sets of random nodes contained respectively in the model's random variables, their conditional independence under the measure implies that the graph d-separates the first and second sets given the third.

A measure that is both an I-map of and faithful to a graph has conditional independences exactly matching that graph's d-separations. -/
def IsFaithful (G : DAG (SWIGNode N)) (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ (X Y Z : Finset (SWIGNode N)) (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars),
    Disjoint X Y → Disjoint X Z → Disjoint Y Z →
    FullCondIndep M X Y Z hX hY hZ μ → G.dSep X Y Z

/-- For [a family of value spaces indexed by the base variables](hyp:Ω) and [two directed acyclic graphs on the same split-node set](hyp:G₁,G₂), [distributional Markov equivalence](goal) means that, for every structural causal model with those value spaces and every finite measure on its random-value space, the measure is a global I-map of the first graph if and only if it is a global I-map of the second.

The value-space family is explicit because the graphs do not determine it. -/
def DistMarkovEquiv (Ω : N → Type uΩ) [∀ n, MeasurableSpace (Ω n)]
    (G₁ G₂ : DAG (SWIGNode N)) : Prop :=
  ∀ (M : Causalean.SCM N Ω) [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ],
    IsGlobalIMap G₁ M μ ↔ IsGlobalIMap G₂ M μ

/-- **The bridge, restated.** For [any structural causal model `M`](hyp:M) and [any point `s`
of its fixed values](hyp:s), [the joint distribution of `M`'s random values under `s` is a
global I-map of `M`'s own DAG](goal) — this is exactly the global Markov property
`full_globalMarkov`. -/
theorem isGlobalIMap_dag_self (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (s : M.FixedValues) :
    IsGlobalIMap M.dag M (M.jointKernel s) := by
  intro X Y Z hX hY hZ hdsep
  exact full_globalMarkov M X Y Z hX hY hZ hdsep s

/-- **Easy half.** For [two DAGs `G₁`, `G₂` on the same node set](hyp:G₁,G₂), if
[they are Markov equivalent — they declare exactly the same d-separations](hyp:h), then
[they are distributionally Markov equivalent: a distribution is a global I-map of one exactly
when it is a global I-map of the other](goal). -/
theorem distMarkovEquiv_of_markovEquiv {G₁ G₂ : DAG (SWIGNode N)}
    (h : MarkovEquiv G₁ G₂) : DistMarkovEquiv Ω G₁ G₂ := by
  intro M _ μ _
  constructor
  · intro himap X Y Z hX hY hZ hdsep
    exact himap X Y Z hX hY hZ ((h X Y Z).mpr hdsep)
  · intro himap X Y Z hX hY hZ hdsep
    exact himap X Y Z hX hY hZ ((h X Y Z).mp hdsep)

end SCM

end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

-/

module
public import Causalean.Graph.CComponents
public import Causalean.SCM.Factored.ObsChainKernel
public import Causalean.SCM.ID.GraphicalThms.InducedSubgraph
public import Causalean.SCM.Model.Induced

/-! # Observational Chain-Rule Factorization

This file supplies an ordinary topological chain-rule factorization for an
SCM's observational kernel, plus a conditional-kernel construction for an
arbitrary observed vertex set. Neither declaration establishes a c-component
factorization: the construction is a conditional law given a chosen
predecessor-derived coordinate set, and the theorem is the per-node
observational chain rule.

For genuine Tian c-component content, see
`SCM/ID/Density/CComponentDensity.lean`, `SCM/ID/Density/MechCFactor/`, and
`SCM/ID/Density/QFactor/TianRecovery.lean`.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace Graph.SWIGGraph

variable (G : SWIGGraph N)

/-- For [a SWIG graph](hyp:G) and [a finite set of its vertices](hyp:C), the
    [conditioning-parent set](goal) is the union of the graph's observed
    predecessors of the vertices in that set, with the set itself removed.

    Its members are observed predecessors of a vertex in the set that are not
    themselves in the set. -/
noncomputable def qFactorParents (C : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  (C.biUnion G.observedPredecessors) \ C

/-- `qFactorParents C` consists of observed nodes outside `C`. -/
lemma qFactorParents_subset_observed (C : Finset (SWIGNode N)) :
    G.qFactorParents C ⊆ G.observed := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hw_union, _⟩
  rcases Finset.mem_biUnion.mp hw_union with ⟨v, _, hw_pred⟩
  exact G.observedPredecessors_subset_observed v hw_pred

end Graph.SWIGGraph

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- For [a structural causal model](hyp:M), [a finite set of observed SWIG
    vertices](hyp:C), and [a fixed-value assignment](hyp:s), provided
    [that the vertex set is contained in the observed-node set](hyp:hC) and
    that the value space of that vertex set is standard Borel and nonempty,
    every observational distribution at a fixed-value assignment is finite,
    and either the fixed-value space is countable or the conditioning-value
    space has a countably generated σ-algebra, the [conditional-kernel
    factor](goal) is the conditional law of the values on the
    vertex set given the values on its conditioning-parent set under the
    model's observational law at that fixed-value assignment.

    This construction is not, by definition, Tian's c-component factor. -/
noncomputable def condKernelFactor
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N))
    (hC : C ⊆ M.observed)
    [StandardBorelSpace (ValuesOn C (swigΩ Ω))]
    [Nonempty (ValuesOn C (swigΩ Ω))]
    (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues
      (ValuesOn (M.toSWIGGraph.qFactorParents C) (swigΩ Ω))] :
    ProbabilityTheory.Kernel
      (ValuesOn (M.toSWIGGraph.qFactorParents C) (swigΩ Ω))
      (ValuesOn C (swigΩ Ω)) :=
  (M.obsCondKernel C (M.toSWIGGraph.qFactorParents C) hC
    (M.toSWIGGraph.qFactorParents_subset_observed C)).comap
      (fun c => (s, c))
      (Measurable.prodMk measurable_const measurable_id)

/-- For [a structural causal model `M`](hyp:M) and [a fixed assignment `s`](hyp:s),
    [its observational kernel equals the full
    chain-rule product of one-node conditional kernels along the topological order of observed
    nodes](goal). This is the ordinary iterated-disintegration factorization;
    it does not use graphical Markov or do-calculus reasoning and does not
    group factors into c-components. -/
theorem obsKernel_eq_chainRuleProduct
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    M.obsKernel s = M.qFactorProduct s :=
  M.obsKernel_eq_qFactorProduct s

end SCM

end Causalean

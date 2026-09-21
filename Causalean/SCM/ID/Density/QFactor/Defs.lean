/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.MechCFactor
public import Causalean.Graph.DSep.InduceTransport

/-! # Definitions for Tian district-density factorization

This file introduces the conditional-independence and global-Markov predicates
used by the density proof, together with the finite-product regrouping of the
full prefix density into one `tianDistrictDensity` factor per c-component.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SWIGGraph

/-- Topological prefixes of an observed-parent-closed set remain
observed-parent-closed. -/
lemma prefixIn_obsParentClosed
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (k : ℕ) :
    (M.fixSet X hObs hFix).ObsParentClosed
      (((M.fixSet X hObs hFix).toSWIGGraph.induce
          (SCM.ID.fixAncestralSet M X hObs hFix Y)).prefixIn
        (SCM.ID.fixObservedAncestralSet M X hObs hFix Y) k) := by
  classical
  let M' := M.fixSet X hObs hFix
  let A := SCM.ID.fixAncestralSet M X hObs hFix Y
  let D := SCM.ID.fixObservedAncestralSet M X hObs hFix Y
  let H := M'.toSWIGGraph.induce A
  have hDclosed : M'.ObsParentClosed D := by
    simpa [M', D] using
      (SCM.ID.fixObservedAncestralSet_obsParent_closed M X hObs hFix Y)
  refine ⟨?_, ?_⟩
  · intro v hv
    exact hDclosed.1 (H.prefixIn_subset D k hv)
  · intro v hv w hwObs hEdge
    have hvD : v ∈ D := H.prefixIn_subset D k hv
    have hwD : w ∈ D := hDclosed.2 v hvD w hwObs hEdge
    rcases Finset.mem_filter.mp hv with ⟨hvD₀, hvIdxLt₀⟩
    have hvIdxLt : (H.nodeIndex D ⟨v, hvD⟩).val < k := by
      have hsub :
          (⟨v, hvD⟩ : {v // v ∈ D}) = ⟨v, hvD₀⟩ := Subtype.ext rfl
      simpa [SWIGGraph.prefixIn, hsub, hvD₀] using hvIdxLt₀
    have hEdgeH : H.dag.edge w v := by
      have hwA : w ∈ A := (Finset.mem_inter.mp hwD).1
      have hvA : v ∈ A := (Finset.mem_inter.mp hvD).1
      have hvObs : v ∈ M'.observed := hDclosed.1 hvD
      dsimp [H, M', A, SWIGGraph.induce, SWIGGraph.inducedDag,
        SWIGGraph.inducedEdge]
      refine ⟨hEdge, ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwA, hwObs⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvA, hvObs⟩))
    have hTopo : H.dag.topoOrder w < H.dag.topoOrder v :=
      H.dag.topoOrder_lt w v hEdgeH
    letI := H.topoLinearOrder
    have hSubtypeLt : (⟨w, hwD⟩ : {v // v ∈ D}) < ⟨v, hvD⟩ := by
      change H.dag.topoOrder w < H.dag.topoOrder v
      exact hTopo
    have hIndexLt :
        (H.nodeIndex D ⟨w, hwD⟩).val < (H.nodeIndex D ⟨v, hvD⟩).val := by
      have hIndexLtFin : H.nodeIndex D ⟨w, hwD⟩ < H.nodeIndex D ⟨v, hvD⟩ := by
        simpa [SWIGGraph.nodeIndex] using
          ((D.orderIsoOfFin rfl).symm.strictMono hSubtypeLt)
      simpa [SWIGGraph.nodeIndex] using
        hIndexLtFin
    change w ∈ D.filter
      (fun v => if h : v ∈ D then (H.nodeIndex D ⟨v, h⟩).val < k else False)
    exact Finset.mem_filter.mpr
      ⟨hwD, by simpa [hwD] using lt_trans hIndexLt hvIdxLt⟩

end SWIGGraph

namespace SCM.ID

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a finite coordinate set](hyp:D), [two coordinate blocks](hyp:X,Y), [a
    conditioning coordinate block](hyp:Z), [proofs that all three blocks are
    contained in the coordinate set](hyp:hX,hY,hZ), and [a finite measure on the
    values of that coordinate set](hyp:μ), [kernel observational conditional
    independence](goal) means that the first two blocks are conditionally
    independent given the third under that measure, provided the coordinate-value
    space is standard Borel.

It is the measure-level analogue of observational conditional independence, but
it is not tied to a particular structural causal model or induced model. -/
def KernelObsCondIndepOn
    (D X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ D) (hY : Y ⊆ D) (hZ : Z ⊆ D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
    (comap_valuesProjection_le hZ)
    (valuesProjection hX)
    (valuesProjection hY)
    μ

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a SWIG graph](hyp:H), [a finite coordinate set](hyp:D), and [a finite
    measure on its coordinate-value space](hyp:μ), [the kernel global Markov
    property](goal) means that every three pairwise disjoint coordinate blocks
    contained in that set which are d-separated in the graph are conditionally
    independent under the measure, provided the coordinate-value space is standard
    Borel.

It is the graph-to-measure interface needed for Tian's Lemma 1 and deliberately
does not mention an induced structural causal model. -/
def KernelGlobalMarkovOn
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ X Y Z : Finset (SWIGNode N),
    ∀ (hX : X ⊆ D) (hY : Y ⊆ D) (hZ : Z ⊆ D),
      Disjoint X Y → Disjoint X Z → Disjoint Y Z →
        H.dag.dSep X Y Z →
          KernelObsCondIndepOn D X Y Z hX hY hZ μ

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a SWIG graph](hyp:G), [a finite node set](hyp:D), [a finite measure on
    its value assignments](hyp:μ), [a family of reference measures](hyp:ref), and
    [a position in the graph's ordering of that set](hyp:i), [Tian's prefix-step
    density](goal) maps each assignment of the selected nodes to the
    Radon–Nikodym density of the selected node's conditional distribution given
    its preceding nodes, relative to its reference measure; the selected node's
    value space is required to be nonempty and standard Borel.

The conditioning set is the prefix inside the chosen finite node set, not graph
parents and not the full observed prefix of an ambient model. -/
noncomputable def tianPrefixStepDensity
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (i : Fin D.card)
    [MeasureTheory.IsFiniteMeasure μ]
    [StandardBorelSpace
      (ValuesOn ({(G.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(G.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x =>
    ((ProbabilityTheory.condDistrib
        (valuesProjection
          (show ({(G.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (G.nodesAt D i).property))
        (valuesProjection (G.prefixIn_subset D i.val))
        μ)
        (valuesProjection (G.prefixIn_subset D i.val) x)).rnDeriv
      (Causalean.SCM.jointRef ref ({(G.nodesAt D i).val} : Finset (SWIGNode N)))
      (valuesProjection
        (show ({(G.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (G.nodesAt D i).property) x)

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a SWIG graph](hyp:G), [a finite node set](hyp:D), [a finite measure on
    its value assignments](hyp:μ), [a family of reference measures](hyp:ref), and
    [a selected node set](hyp:S), [Tian's district density](goal) maps each node
    assignment to the product of the prefix-step densities for exactly those
    ordered nodes that lie in the selected set; every singleton node-value space
    in the ordering is required to be nonempty and standard Borel.

This is the induce-free district factor for a measure on the selected finite
node set. -/
noncomputable def tianDistrictDensity
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (S : Finset (SWIGNode N))
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter
        (fun i : Fin D.card => (G.nodesAt D i).val ∈ S),
      tianPrefixStepDensity G D μ ref i x

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a SWIG graph](hyp:G), [a finite node set](hyp:D), [a finite measure on
    its value assignments](hyp:μ), and [a family of reference measures](hyp:ref),
    [Tian's full prefix-chain density](goal) maps each node assignment to the
    product of the prefix-step densities for every node in the graph's ordering;
    every singleton node-value space in that ordering is required to be nonempty
    and standard Borel. -/
noncomputable def tianDensityProduct
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x => ∏ i : Fin D.card, tianPrefixStepDensity G D μ ref i x

/-- For [a finite acyclic graph with measurable node-value spaces](hyp:N,Ω,H), [a finite node
set](hyp:D), [evidence that it is exactly the observed set](hyp:hD), [a finite law on that
set](hyp:μ), and [coordinate reference measures](hyp:ref), [the full prefix-chain density
equals the product of Tian's district densities over all c-components](goal).

Tian's full prefix-chain density regroups exactly as the product of the
Tian district factors over the graph c-components.  This is pure finite-product
algebra: each prefix index maps to the c-component of its node, and the district
factor is precisely the product over the corresponding fiber. -/
theorem prod_tianDistrictDensity_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (hD : H.observed = D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    (fun x => ∏ S ∈ H.cComponentSet, tianDistrictDensity H D μ ref S x)
      = fun x => tianDensityProduct H D μ ref x := by
  classical
  funext x
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin D.card)),
      H.cComponentOf (H.nodesAt D i).val ∈ H.cComponentSet := by
    intro i _
    exact Finset.mem_image.mpr ⟨(H.nodesAt D i).val, hD.symm ▸ (H.nodesAt D i).property, rfl⟩
  unfold tianDensityProduct tianDistrictDensity
  rw [← Finset.prod_fiberwise_of_maps_to hmaps
    (fun i => tianPrefixStepDensity H D μ ref i x)]
  refine Finset.prod_congr rfl ?_
  intro S hS
  refine Finset.prod_congr ?_ (fun i _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_cComponent_iff_cComponentOf_eq H
    (hD.symm ▸ (H.nodesAt D i).property) hS

end SCM.ID
end Causalean

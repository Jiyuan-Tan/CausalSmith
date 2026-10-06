/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.QMass
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.FiniteReference


/-! # The mechanism c-factor and do-complement measure

This file defines the do-complement intervention and its marginal measure
`QmechMeasure`, relates singleton values of that measure to `qLocalMass`, and
proves the fixed-edge facts needed for valid interventions.  The density-level
invariance and observational comparison are developed in sibling files.
-/

@[expose] public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

/-- For a finite node set with measurable node-value spaces, [a structural causal model](hyp:M)
and [a set of SWIG nodes](hyp:S), [the mechanism-complement node set](goal) consists exactly of
the base nodes whose random copy is observed but absent from the given set and whose fixed copy
is not already fixed in the model.

Base-node names whose random copy lies in `M.observed \ S` and whose fixed
copy is **not already fixed** in `M` — the variables intervened on in Tian's
do-complement object `Q[S] = P_{v∖s}(s)`.  The "not already fixed" clause lets
this apply to non-standard models such as `M.fixSet X`. -/
noncomputable def mechComplementNames
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) : Finset N :=
  Finset.univ.filter fun n =>
    SWIGNode.random n ∈ M.observed \ S ∧ SWIGNode.fixed n ∉ M.fixed

/-- Every mechanism-complement variable has its random copy among the observed nodes. -/
lemma mechComplementNames_random_mem_observed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    ∀ n ∈ M.mechComplementNames S, SWIGNode.random n ∈ M.observed := by
  intro n hn
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).2.1).1

/-- Every mechanism-complement variable has a fixed copy that is not already fixed. -/
lemma mechComplementNames_fixed_not_mem
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    ∀ n ∈ M.mechComplementNames S, SWIGNode.fixed n ∉ M.fixed := by
  intro n hn
  exact (Finset.mem_filter.mp hn).2.2

/-- The random copies of the mechanism-complement variables form a subset of the observed nodes. -/
lemma mechComplementNames_image_random_subset_observed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    (M.mechComplementNames S).image SWIGNode.random ⊆ M.observed := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨n, hn, rfl⟩
  exact M.mechComplementNames_random_mem_observed S n hn

private lemma mechComplementNames_mem_of_random_observed_not_mem
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) {n : N}
    (hobs : SWIGNode.random n ∈ M.observed)
    (hnotS : SWIGNode.random n ∉ S)
    (hfix : SWIGNode.fixed n ∉ M.fixed) :
    n ∈ M.mechComplementNames S := by
  rw [mechComplementNames, Finset.mem_filter]
  exact ⟨Finset.mem_univ n, Finset.mem_sdiff.mpr ⟨hobs, hnotS⟩, hfix⟩

private lemma mechComplement_fixSet_obsParentClosed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v) :
    (M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).ObsParentClosed S := by
  classical
  refine ⟨by simpa [fixSet_observed] using hS, ?_⟩
  intro v hvS w hwObs hEdge
  by_contra hwNotS
  have hwObsM : w ∈ M.observed := by
    simpa [fixSet_observed] using hwObs
  rcases M.observed_is_random w hwObsM with ⟨n, rfl⟩
  by_cases hfix : SWIGNode.fixed n ∈ M.fixed
  · have hnW : n ∉ M.mechComplementNames S := by
      intro hn
      exact (M.mechComplementNames_fixed_not_mem S n hn) hfix
    have hEdgeRel :
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge
          (M.mechComplementNames S) (SWIGNode.random n) v := by
      simpa [fixSet, fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG] using hEdge
    have hEdgeM : M.dag.edge (SWIGNode.random n) v := by
      simpa [SWIGGraph.splitMonoEdgeRel, hnW] using hEdgeRel
    exact hfe n hfix v hEdgeM
  · have hnW : n ∈ M.mechComplementNames S :=
      mechComplementNames_mem_of_random_observed_not_mem M S hwObsM hwNotS hfix
    have hEdgeRel :
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge
          (M.mechComplementNames S) (SWIGNode.random n) v := by
      simpa [fixSet, fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG] using hEdge
    simp [SWIGGraph.splitMonoEdgeRel, hnW] at hEdgeRel

/-- For a finite node set with measurable node-value spaces, [a structural causal model](hyp:M),
[a set of SWIG nodes](hyp:S), [an assignment to the model's already fixed nodes](hyp:s), and [a
full assignment to its observed nodes](hyp:x), [the do-complement fixed-node assignment](goal)
extends the original fixed-node assignment by assigning each mechanism-complement node the value
of its random copy in the observed assignment.

Fixed-value slice for the do-complement SCM, read from a full observed
assignment: keep `M`'s existing fixed slice `s` and extend it on the
do-complement coordinates by projecting `x` to the random copies in `V∖S`. -/
noncomputable def mechDoValues
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N))
    (s : M.FixedValues) (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).FixedValues :=
  M.fixSetExtend (M.mechComplementNames S)
    (M.mechComplementNames_random_mem_observed S)
    (M.mechComplementNames_fixed_not_mem S) s
    (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x)

/-- For a finite node set with measurable node-value spaces, [a structural causal model](hyp:M),
[a set of SWIG nodes contained in its observed-node set](hyp:S,hS), and [an assignment to the
fixed nodes of the model obtained by intervening on its mechanism complement](hyp:sWn), [the
mechanism $Q[S]$ measure](goal) is the intervened model's observational law projected onto the
given SWIG-node set.

Tian's `Q[S]` measure (Eq. 36 / Eq. 55): the do(observed∖S) marginal on `S`.
Intervene on every not-already-fixed observed node outside `S`, then project the
intervened observational law to the coordinates in `S`. -/
noncomputable def QmechMeasure
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (sWn :
      (M.fixSet (M.mechComplementNames S)
        (M.mechComplementNames_random_mem_observed S)
        (M.mechComplementNames_fixed_not_mem S)).FixedValues) :
    MeasureTheory.Measure (ValuesOn S (swigΩ Ω)) :=
  ((M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).obsKernel sWn).map
    (valuesProjection
      (show S ⊆ (M.fixSet (M.mechComplementNames S)
          (M.mechComplementNames_random_mem_observed S)
          (M.mechComplementNames_fixed_not_mem S)).observed by
        simpa [fixSet_observed] using hS))

/-- For a finite node set with measurable node-value spaces, [a structural causal model](hyp:M),
[a family of reference measures](hyp:ref), [a set of SWIG nodes contained in the model's
observed-node set](hyp:S,hS), and [an assignment to the model's fixed nodes](hyp:s), [the
mechanism c-factor density](goal) maps every full observed-node assignment to the
Radon--Nikodym derivative of the corresponding mechanism $Q[S]$ measure with respect to the
product reference measure on the given node set, evaluated at that assignment's restriction to
the set.

The **mechanism c-factor density** `Q[S]` as a function of a full observed
assignment `x`: read the do-values for `V∖S` from `x` (keeping `M`'s fixed slice
`s`), form the do-complement marginal on `S`, and take its `rnDeriv` against the
product reference on `S`, evaluated at the `S`-projection of `x`. -/
noncomputable def mechCFactor
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (S : Finset (SWIGNode N))
    (hS : S ⊆ M.observed) (s : M.FixedValues) :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    (QmechMeasure M S hS (M.mechDoValues S s x)).rnDeriv
      (Causalean.SCM.jointRef ref S) (valuesProjection hS x)

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[an observed node set](hyp:S), [evidence that the set is observed](hyp:hS), [the condition that
fixed nodes have no outgoing random-copy edges](hyp:hfe), [a fixed-node assignment](hyp:s), and
[an observed realization](hyp:x), [the singleton mass under the complementary intervention
equals the local q-mass of that node set](goal). -/
theorem QmechMeasure_singleton_eq_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v)
    (s : M.FixedValues) (x : ValuesOn M.observed (swigΩ Ω)) :
    QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
      = M.qLocalMass s S hS x := by
  classical
  let W := M.mechComplementNames S
  let hWobs := M.mechComplementNames_random_mem_observed S
  let hWfix := M.mechComplementNames_fixed_not_mem S
  let M' := M.fixSet W hWobs hWfix
  let s' : M'.FixedValues := M.mechDoValues S s x
  have hclosed : M'.ObsParentClosed S := by
    simpa [M', W, hWobs, hWfix] using
      mechComplement_fixSet_obsParentClosed M S hS hfe
  let hS' : S ⊆ M'.observed := hclosed.1
  have hbridge := obsKernel_marginal_singleton_eq_latentProduct_agree M' s' hS' x
  have heval_local :
      {ℓ | ∀ v : {v // v ∈ S},
        M'.evalMap s' ℓ
            ⟨v.val, Finset.mem_union_left M'.unobserved (hS' v.property)⟩ =
          x ⟨v.val, hS' v.property⟩}
        = {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M'.evalMap_agree_iff_localConsistent s' S hclosed x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M'.evalMap_agree_iff_localConsistent s' S hclosed x ℓ).mpr
        hLocal v.val v.property
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      x ⟨w, by simpa [M', W, hWobs, hWfix, fixSet_observed] using hw⟩ = x ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hpin : ∀ D (hD : D ∈ W),
      x ⟨SWIGNode.random D, hWobs D hD⟩ =
        s' ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ := by
    intro D hD
    have hnew := M.fixSetExtend_apply_new_fixed W hWobs hWfix s
      (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x) hD
    simp only [s', mechDoValues]
    exact hnew.symm
  have hproj : M.fixSetProj W hWobs hWfix s' = s := by
    simpa [s', W, hWobs, hWfix, mechDoValues] using
      (M.fixSetProj_fixSetExtend W hWobs hWfix s
        (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x))
  have hset_do :
      {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ}
        = {ℓ | ∀ v (hv : v ∈ S), M.localConsistent s x v (hS hv) ℓ} := by
    ext ℓ
    constructor
    · intro hLocal v hv
      have hnot : v ∉ W.image SWIGNode.random := by
        intro hvW
        rcases Finset.mem_image.mp hvW with ⟨D, hD, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hD).2.1).2 hv
      exact (localConsistent_fixSet_iff M W hWobs hWfix s' s x x v (hS' hv) (hS hv)
        hnot hobsAgree hpin hproj ℓ).mp (hLocal v hv)
    · intro hLocal v hv
      have hnot : v ∉ W.image SWIGNode.random := by
        intro hvW
        rcases Finset.mem_image.mp hvW with ⟨D, hD, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hD).2.1).2 hv
      exact (localConsistent_fixSet_iff M W hWobs hWfix s' s x x v (hS' hv) (hS hv)
        hnot hobsAgree hpin hproj ℓ).mpr (hLocal v hv)
  calc
    QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
        = ((M'.obsKernel s').map (valuesProjection hS')) {valuesProjection hS' x} := by
            rfl
    _ = M'.latentProduct
          {ℓ | ∀ v : {v // v ∈ S},
            M'.evalMap s' ℓ
                ⟨v.val, Finset.mem_union_left M'.unobserved (hS' v.property)⟩ =
              x ⟨v.val, hS' v.property⟩} := hbridge
    _ = M'.latentProduct
          {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ} := by
            rw [heval_local]
    _ = M.latentProduct
          {ℓ | ∀ v (hv : v ∈ S), M.localConsistent s x v (hS hv) ℓ} := by
            rw [hset_do]
            rfl
    _ = M.qLocalMass s S hS x := by
            rfl

/-- [A standard structural causal model has no fixed nodes](hyp:M,hStd), so
[the implication from fixed-copy membership to absence of outgoing random-copy edges holds
vacuously](goal). -/
lemma standard_fixed_random_edgeless
    (M : Causalean.SCM N Ω) (hStd : M.isStandard) :
    ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v := by
  intro n hn
  rw [SCM.isStandard] at hStd
  rw [hStd] at hn
  simp at hn

/-- Given [a finite structural causal model and an intervention set](hyp:N,Ω,M,X), if [every
intervened random copy is observed](hyp:hObs), [no corresponding fixed copy is already fixed](hyp:hFix),
and [the model is standard](hyp:hStd), then for [a node whose fixed copy is fixed after the
intervention](hyp:n) and [any target node](hyp:v), [the intervened random copy has no outgoing
edge to that target](goal). -/
lemma fixSet_fixed_random_edgeless
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hStd : M.isStandard) :
    ∀ n : N, SWIGNode.fixed n ∈ (M.fixSet X hObs hFix).fixed →
      ∀ v : SWIGNode N, ¬ (M.fixSet X hObs hFix).dag.edge (SWIGNode.random n) v := by
  classical
  intro n hn v
  have hnX : n ∈ X := by
    rw [SCM.fixSet_fixed] at hn
    rcases Finset.mem_union.mp hn with hnM | hnX
    · exfalso
      rw [SCM.isStandard] at hStd
      rw [hStd] at hnM
      simp at hnM
    · rcases Finset.mem_image.mp hnX with ⟨D, hD, hDfix⟩
      cases hDfix
      exact hD
  intro hEdge
  have hEdgeRel :
      SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X
        (SWIGNode.random n) v := by
    simpa [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
      using hEdge
  simp [SWIGGraph.splitMonoEdgeRel, hnX] at hEdgeRel


end SCM
end Causalean

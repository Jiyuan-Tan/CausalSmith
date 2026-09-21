/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Graph.DSep.InduceTransport
public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.MechCFactor
public import Causalean.SCM.ID.Density.QFactor.RatioProduct
public import Causalean.SCM.ID.GraphicalThms.DoGFormula

/-! # Point-mass lemmas for Tian density recovery

This file relates prefix singleton masses, reference atoms, local q-masses, and
Tian prefix-step densities.  These lemmas supply the pointwise calculations
used by the district-recovery theorems in `TianRecovery`.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- For a subset of an ordered finite graph set, the product of coordinate reference-measure
masses at selected values equals the reference measure's mass at their joint singleton outcome. -/
lemma component_ref_atom_product_eq_jointRef_prefixIn
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N)) (ref : ReferenceMeasures Ω)
    (S : Finset (SWIGNode N)) (hSD : S ⊆ D)
    (xD : ValuesOn D (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      ref.μ (H.nodesAt D i).val
        ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)))
      =
    jointRef ref S ({valuesProjection hSD xD} :
      Set (ValuesOn S (swigΩ Ω))) := by
  classical
  have hprod :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        ref.μ (H.nodesAt D i).val
          ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)))
        =
      ∏ v : {v // v ∈ S},
        ref.μ v.val ({(valuesProjection hSD xD) v} :
          Set (swigΩ Ω v.val)) := by
    refine Finset.prod_bij
      (fun i hi => ⟨(H.nodesAt D i).val, (Finset.mem_filter.mp hi).2⟩)
      ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro i _hi j _hj hij
      have hval : (H.nodesAt D i).val = (H.nodesAt D j).val :=
        congrArg (fun v : {v // v ∈ S} => v.val) hij
      have hsub : H.nodesAt D i = H.nodesAt D j :=
        Subtype.ext hval
      calc
        i = H.nodeIndex D (H.nodesAt D i) := by
              simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        _ = H.nodeIndex D (H.nodesAt D j) := by rw [hsub]
        _ = j := by
              simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
    · intro v _hv
      let i : Fin D.card := H.nodeIndex D ⟨v.val, hSD v.property⟩
      have hnode : (H.nodesAt D i).val = v.val := by
        have hround : H.nodesAt D (H.nodeIndex D ⟨v.val, hSD v.property⟩) =
            ⟨v.val, hSD v.property⟩ := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        exact congrArg Subtype.val hround
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simp [hnode, v.property]⟩
      · exact Subtype.ext hnode
    · intro i hi
      simp [valuesProjection]
  rw [jointRef_singleton_eq_prod]
  exact hprod

/-- The mass of a realized prefix together with its next coordinate equals the mass of the
same realization of the successor prefix under any measure on the ordered graph values. -/
lemma prefix_pair_singleton_mass_eq_succ_prefix_mass
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (i : Fin D.card) (x : ValuesOn D (swigΩ Ω)) :
    (μ.map
        (fun ω : ValuesOn D (swigΩ Ω) =>
          (valuesProjection (H.prefixIn_subset D i.val) ω,
            valuesProjection
              (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D i).property) ω)))
        ({(valuesProjection (H.prefixIn_subset D i.val) x,
            valuesProjection
              (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D i).property) x)} :
          Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
            ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
      (μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
        ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
          Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) := by
  classical
  let hNodeD : ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    exact hv ▸ (H.nodesAt D i).property
  let pairMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun ω => (valuesProjection (H.prefixIn_subset D i.val) ω,
      valuesProjection hNodeD ω)
  let succMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω) :=
    valuesProjection (H.prefixIn_subset D (i.val + 1))
  have hsets :
      pairMap ⁻¹'
          ({(valuesProjection (H.prefixIn_subset D i.val) x,
              valuesProjection hNodeD x)} :
            Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
              ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
        succMap ⁻¹'
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) := by
    ext ω
    constructor
    · intro hω
      have hpre :
          valuesProjection (H.prefixIn_subset D i.val) ω =
            valuesProjection (H.prefixIn_subset D i.val) x :=
        congrArg Prod.fst hω
      have hnode :
          valuesProjection hNodeD ω = valuesProjection hNodeD x :=
        congrArg Prod.snd hω
      ext v
      by_cases hvpre : v.val ∈ H.prefixIn D i.val
      · have h := congrFun hpre ⟨v.val, hvpre⟩
        simpa [succMap, valuesProjection] using h
      · have hvnode : v.val = (H.nodesAt D i).val := by
          have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) := v.property
          have hvsucc' : v.val ∈
              H.prefixIn D i.val ∪ {(H.nodesAt D i).val} := by
            simpa [prefixIn_succ H D i.isLt] using hvsucc
          rcases Finset.mem_union.mp hvsucc' with hvold | hvnew
          · exact False.elim (hvpre hvold)
          · simpa using hvnew
        have h := congrFun hnode
          ⟨v.val, by simpa [hvnode] using Finset.mem_singleton_self (H.nodesAt D i).val⟩
        simpa [succMap, valuesProjection, hvnode] using h
    · intro hω
      have hsucc :
          valuesProjection (H.prefixIn_subset D (i.val + 1)) ω =
            valuesProjection (H.prefixIn_subset D (i.val + 1)) x := hω
      apply Prod.ext
      · ext v
        have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) :=
          prefixIn_mono H D (Nat.le_succ i.val) v.property
        have h := congrFun hsucc ⟨v.val, hvsucc⟩
        simpa [pairMap, valuesProjection] using h
      · ext v
        have hvnode : v.val = (H.nodesAt D i).val := by
          exact Finset.mem_singleton.mp v.property
        have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) := by
          rw [hvnode, nodesAt_mem_prefixIn_iff H D (i.val + 1) i]
          exact Nat.lt_succ_self i.val
        have h := congrFun hsucc ⟨v.val, hvsucc⟩
        simpa [pairMap, valuesProjection] using h
  rw [MeasureTheory.Measure.map_apply
      ((measurable_valuesProjection (H.prefixIn_subset D i.val)).prod
        (measurable_valuesProjection hNodeD))
      (MeasurableSet.singleton _),
    MeasureTheory.Measure.map_apply
      (measurable_valuesProjection (H.prefixIn_subset D (i.val + 1)))
      (MeasurableSet.singleton _),
    hsets]

/-- When the preceding prefix has nonzero singleton mass, the one-step Tian density is
the ratio of the successive prefix singleton masses, divided by the singleton reference mass
of the added variable. -/
lemma tianPrefixStepDensity_eq_prefix_mass_ratio
    [∀ n, Fintype (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (i : Fin D.card) (x : ValuesOn D (swigΩ Ω))
    (hprefix0 :
      (μ.map (valuesProjection (H.prefixIn_subset D i.val)))
        ({valuesProjection (H.prefixIn_subset D i.val) x} :
          Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω))) ≠ 0) :
    tianPrefixStepDensity H D μ ref i x =
      ((μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) /
        (μ.map (valuesProjection (H.prefixIn_subset D i.val)))
          ({valuesProjection (H.prefixIn_subset D i.val) x} :
            Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω)))) /
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D i).property) x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
  classical
  let hNodeD : ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    exact hv ▸ (H.nodesAt D i).property
  let nodeMap : ValuesOn D (swigΩ Ω) →
      ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    valuesProjection hNodeD
  let prefixMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D i.val) (swigΩ Ω) :=
    valuesProjection (H.prefixIn_subset D i.val)
  have hden0 :
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href _ (nodeMap x)
  have hdentop :
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hcond :
      (ProbabilityTheory.condDistrib nodeMap prefixMap μ (prefixMap x))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
        (μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) /
          (μ.map prefixMap)
            ({prefixMap x} : Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω))) := by
    rw [condDistrib_singleton_mass_of_ne_zero (μ := μ)
        (Y := nodeMap) (Z := prefixMap)
        (measurable_valuesProjection hNodeD) (prefixMap x) (nodeMap x) hprefix0]
    rw [prefix_pair_singleton_mass_eq_succ_prefix_mass H D μ i x]
  unfold tianPrefixStepDensity
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href
        ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        (ProbabilityTheory.condDistrib nodeMap prefixMap μ (prefixMap x)))
      (nodeMap x) hden0 hdentop]
  simpa [nodeMap, prefixMap, hNodeD] using congrArg
    (fun a => a / jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))))
    hcond

/-- Given [a finite structural causal model and intervention set](hyp:N,Ω,M,X), if [the intervened
random copies are observed](hyp:hObs), [their fixed copies are not already fixed](hyp:hFix), [the
model is standard](hyp:hStd), and [the reference measures are faithful](hyp:ref,href), then for
[an intervention assignment, observed set, and observed value](hyp:sDo,S,hSobs,x), [the intervened
mechanism factor is the local mass divided by the joint reference mass](goal). -/
lemma doModel_mechCFactor_eq_qLocalMass_div_jointRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hStd : M.isStandard)
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hSobs : S ⊆ (M.fixSet X hObs hFix).observed)
    (x : ValuesOn (M.fixSet X hObs hFix).observed (swigΩ Ω)) :
    (M.fixSet X hObs hFix).mechCFactor ref S hSobs sDo x =
      (M.fixSet X hObs hFix).qLocalMass sDo S hSobs x /
        jointRef ref S ({valuesProjection hSobs x} :
          Set (ValuesOn S (swigΩ Ω))) := by
  exact mechCFactor_eq_qLocalMass_div_jointRef
    (M.fixSet X hObs hFix) ref sDo S hSobs href
    (fixSet_fixed_random_edgeless M X hObs hFix hStd) x

/-- If an extension preserves all values on a larger observed set, then restricting the
extension to any subset gives the same values as restricting the original assignment directly. -/
lemma valuesProjection_extend_eq_of_subset
    (M : Causalean.SCM N Ω)
    {D S : Finset (SWIGNode N)}
    (hDobs : D ⊆ M.observed) (hSD : S ⊆ D) (hSobs : S ⊆ M.observed)
    (extend : ValuesOn D (swigΩ Ω) → ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection hDobs (extend xD) = xD)
    (xD : ValuesOn D (swigΩ Ω)) :
    valuesProjection hSobs (extend xD) = valuesProjection hSD xD := by
  ext v
  have h := congrFun (hExtend xD) ⟨v.val, hSD v.property⟩
  simpa [valuesProjection] using h

private lemma obsKernel_marginal_singleton_eq_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection hP.1))
        ({valuesProjection hP.1 x} : Set (ValuesOn P (swigΩ Ω))) =
      M.qLocalMass s P hP.1 x := by
  classical
  rw [obsKernel_marginal_singleton_eq_latentProduct_agree M s hP.1 x]
  have hset :
      {ℓ | ∀ v : {v // v ∈ P},
        M.evalMap s ℓ
            ⟨v.val, Finset.mem_union_left M.unobserved (hP.1 v.property)⟩ =
          x ⟨v.val, hP.1 v.property⟩}
        =
      {ℓ | ∀ v (hv : v ∈ P), M.localConsistent s x v (hP.1 hv) ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M.evalMap_agree_iff_localConsistent s P hP x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M.evalMap_agree_iff_localConsistent s P hP x ℓ).mpr
        hLocal v.val v.property
  unfold qLocalMass
  rw [hset]

private lemma doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    {P : Finset (SWIGNode N)}
    (hPD : P ⊆ fixObservedAncestralSet M X hObs hFix Y) :
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD)) =
      (((M.fixSet X hObs hFix).obsKernel sDo).map
        (valuesProjection
          (show P ⊆ (M.fixSet X hObs hFix).observed from
            fun _ hv => Finset.inter_subset_right (hPD hv)))) := by
  classical
  let D := fixObservedAncestralSet M X hObs hFix Y
  let hDobs : D ⊆ (M.fixSet X hObs hFix).observed := Finset.inter_subset_right
  let hPobs : P ⊆ (M.fixSet X hObs hFix).observed := fun _ hv => hDobs (hPD hv)
  have hcomp :
      valuesProjection (Ω := swigΩ Ω) hPobs =
        valuesProjection hPD ∘ valuesProjection hDobs :=
    valuesProjection_comp (Ω' := swigΩ Ω) hPD hDobs
  unfold doObsKernelAncestralMarginal
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection hDobs)]
  rw [MeasureTheory.Measure.map_map (measurable_valuesProjection hPD)
    (measurable_valuesProjection hDobs)]
  rw [← hcomp]

/-- Given [a finite structural causal model, intervention set, target set, intervention assignment,
and extension map](hyp:N,Ω,M,X,Y,sDo,extend), if [the intervened random copies are observed](hyp:hObs),
[their fixed copies are not already fixed](hyp:hFix), and [the extension map preserves ancestral
coordinates](hyp:hExtend), then for [a prefix length and ancestral assignment](hyp:k,xD), [the
singleton mass of the corresponding interventional marginal equals the product of district-local
masses over that prefix](goal). -/
lemma doObsKernelAncestralMarginal_prefix_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (k : ℕ)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection (H.prefixIn_subset D k)))
      ({valuesProjection (H.prefixIn_subset D k) xD} :
        Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
      ∏ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ H.prefixIn D k)
          (fun _ hv => (SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k).1
            (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let P := H.prefixIn D k
  let hPD : P ⊆ D := H.prefixIn_subset D k
  let hPclosed : MX.ObsParentClosed P := by
    simpa [MX, D, H, P] using SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k
  let hPobsMX : P ⊆ MX.observed := hPclosed.1
  let hPobsM : P ⊆ M.observed := fun _ hv => Finset.inter_subset_right (hPD hv)
  have hpointM :
      valuesProjection hPobsM (extend xD) = valuesProjection hPD xD :=
    valuesProjection_extend_eq_of_subset M
      (show D ⊆ M.observed from Finset.inter_subset_right)
      hPD hPobsM extend hExtend xD
  have hpointMX :
      valuesProjection hPobsMX (extend xD) = valuesProjection hPD xD := by
    simpa [MX, SCM.fixSet_observed, hPobsMX, hPobsM] using hpointM
  have hmap :=
    doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
      M X hObs hFix Y sDo hPD
  have hengine :=
    MX.obsKernel_marginal_singleton_eq_prod_qLocalMass sDo P hPclosed (extend xD)
  calc
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD))
      ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))
        =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω))) := by
          simpa [MX, D, H, P, hPobsMX] using congrArg
            (fun μ : MeasureTheory.Measure (ValuesOn P (swigΩ Ω)) =>
              μ ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))) hmap
    _ =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) := by
          rw [hpointMX]
    _ = ∏ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ P)
          (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
          exact hengine

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[an intervention set](hyp:X), [evidence that its random copies are observed](hyp:hObs), [evidence
that its fixed copies are not already fixed](hyp:hFix), [an outcome set](hyp:Y), [a fixed-node
assignment after intervention](hyp:sDo), [an extension from the ancestral observed margin to
the original observed space](hyp:extend), [proof that extension preserves that margin](hyp:hExtend),
[a prefix length](hyp:k), and [a realization on the ancestral margin](hyp:xD), [the intervened
observational law's singleton mass on that prefix equals the product of the induced graph's
local q-masses over its c-components](goal). -/
lemma doObsKernelAncestralMarginal_prefix_singleton_eq_prod_H_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (k : ℕ)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection (H.prefixIn_subset D k)))
      ({valuesProjection (H.prefixIn_subset D k) xD} :
        Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
      ∏ C ∈ H.cComponentSet,
        MX.qLocalMass sDo (C ∩ H.prefixIn D k)
          (fun _ hv => (SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k).1
            (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let A := fixAncestralSet M X hObs hFix Y
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce A
  let P := H.prefixIn D k
  let hPD : P ⊆ D := H.prefixIn_subset D k
  let hPclosed : MX.ObsParentClosed P := by
    simpa [MX, D, H, P] using SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k
  let hPobsMX : P ⊆ MX.observed := hPclosed.1
  let hPobsM : P ⊆ M.observed := fun _ hv => Finset.inter_subset_right (hPD hv)
  have hpointM :
      valuesProjection hPobsM (extend xD) = valuesProjection hPD xD :=
    valuesProjection_extend_eq_of_subset M
      (show D ⊆ M.observed from Finset.inter_subset_right)
      hPD hPobsM extend hExtend xD
  have hpointMX :
      valuesProjection hPobsMX (extend xD) = valuesProjection hPD xD := by
    simpa [MX, SCM.fixSet_observed, hPobsMX, hPobsM] using hpointM
  have hmap :=
    doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
      M X hObs hFix Y sDo hPD
  have hHobs : H.observed = D := by
    simp [H, D, A, MX, SWIGGraph.induce, fixObservedAncestralSet, SCM.fixSet_observed]
  have h𝒞obs : ∀ U ∈ H.cComponentSet, U ⊆ MX.observed := by
    intro U hU v hv
    have hvHobs : v ∈ H.observed := H.cComponentSet_subset_observed U hU hv
    have hvD : v ∈ D := by simpa [hHobs] using hvHobs
    exact Finset.mem_inter.mp hvD |>.2
  have hcover : P ⊆ H.cComponentSet.sup id := by
    intro v hv
    have hvObs : v ∈ H.observed := by
      rw [hHobs]
      exact H.prefixIn_subset D k hv
    rw [Finset.mem_sup]
    exact ⟨H.cComponentOf v,
      (by
        rw [SWIGGraph.cComponentSet, Finset.mem_image]
        exact ⟨v, hvObs, rfl⟩),
      H.mem_cComponentOf_self hvObs⟩
  have hblock :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (MX.latentBlock U) (MX.latentBlock U')) := by
    intro U hU V hV hne
    exact latentBlock_pairwise_disjoint_induce_components MX A hU hV hne
  have hfac :=
    MX.qLocalMass_prod_inter_of_latentBlock_disjoint sDo
      P hPobsMX H.cComponentSet h𝒞obs hcover hblock (extend xD)
  have hq :
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) =
        MX.qLocalMass sDo P hPobsMX (extend xD) :=
    obsKernel_marginal_singleton_eq_qLocalMass MX sDo P hPclosed (extend xD)
  calc
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD))
      ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))
        =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω))) := by
          simpa [MX, D, H, P, hPobsMX] using congrArg
            (fun μ : MeasureTheory.Measure (ValuesOn P (swigΩ Ω)) =>
              μ ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))) hmap
    _ =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) := by
          rw [hpointMX]
    _ = MX.qLocalMass sDo P hPobsMX (extend xD) := hq
    _ = ∏ C ∈ H.cComponentSet,
        MX.qLocalMass sDo (C ∩ P)
          (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
          calc
            MX.qLocalMass sDo P hPobsMX (extend xD) =
              ∏ U ∈ H.cComponentSet,
                if hU : U ∈ H.cComponentSet then
                  MX.qLocalMass sDo (U ∩ P)
                    (fun _ hv => h𝒞obs U hU (Finset.mem_of_mem_inter_left hv))
                    (extend xD)
                else 1 := by
                  simpa [P] using hfac
            _ = ∏ C ∈ H.cComponentSet,
                MX.qLocalMass sDo (C ∩ P)
                  (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv))
                  (extend xD) := by
                  refine Finset.prod_congr rfl ?_
                  intro C hC
                  simp [hC]


end SCM.ID
end Causalean

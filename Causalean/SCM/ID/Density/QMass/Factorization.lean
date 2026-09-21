/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.LatentBlocks
public import Causalean.SCM.ID.Density.IdentifyMass
public import Causalean.SCM.ID.Density.MassBridge
public import Causalean.SCM.ID.DiscreteID.Positive
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Mathlib.Probability.Independence.InfinitePi
public import Causalean.Tactic.Attr
public import Causalean.SCM.ID.Density.QMass.LatentBlocks

/-! # C-component factorization of local q-masses

This file splits local-consistency events and their latent-product masses over
disjoint latent blocks.  Its main result expresses an observational marginal
atom as the product of the local q-masses of the graph's c-components.
-/

public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For an observed-parent-closed node set, local consistency at all of its nodes is equivalent to
local consistency within each of its confounded components. -/
lemma localConsistent_event_eq_component_biInter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ P),
      M.localConsistent s x v (hP.1 hv) ℓ} =
      ⋂ C ∈ M.toSWIGGraph.cComponentSet,
        {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
          M.localConsistent s x v
            (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ} := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    rw [Set.mem_iInter]
    intro C
    rw [Set.mem_iInter]
    intro _hC v hv
    exact hℓ v (Finset.mem_of_mem_inter_right hv)
  · intro hℓ v hvP
    rw [Set.mem_iInter] at hℓ
    have hC : M.toSWIGGraph.cComponentOf v ∈ M.toSWIGGraph.cComponentSet := by
      rw [SWIGGraph.cComponentSet, Finset.mem_image]
      exact ⟨v, hP.1 hvP, rfl⟩
    have hvC : v ∈ M.toSWIGGraph.cComponentOf v :=
      M.toSWIGGraph.mem_cComponentOf_self (hP.1 hvP)
    have hℓC := hℓ (M.toSWIGGraph.cComponentOf v)
    rw [Set.mem_iInter] at hℓC
    exact hℓC hC v
      (Finset.mem_inter.mpr ⟨hvC, hvP⟩)

/-- For a finite family of observed node sets, local consistency over their union is equivalent to
local consistency over every member of the family. -/
lemma localConsistent_event_eq_family_biInter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hSup : 𝒞.sup id ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ 𝒞.sup id),
      M.localConsistent s x v (hSup hv) ℓ} =
      ⋂ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then
          {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
            M.localConsistent s x v (h𝒞obs U hU hv) ℓ}
        else Set.univ := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    rw [Set.mem_iInter]
    intro U
    rw [Set.mem_iInter]
    intro hU
    simp [hU]
    intro v hv
    have hvSup : v ∈ 𝒞.sup id := by
      rw [Finset.mem_sup]
      exact ⟨U, hU, hv⟩
    convert hℓ v hvSup using 1
  · intro hℓ v hvSup
    rw [Set.mem_iInter] at hℓ
    rw [Finset.mem_sup] at hvSup
    rcases hvSup with ⟨U, hU, hvU⟩
    have hℓU := hℓ U
    rw [Set.mem_iInter] at hℓU
    have hUevent :
        ℓ ∈ {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
          M.localConsistent s x v (h𝒞obs U hU hv) ℓ} := by
      simpa [hU] using hℓU hU
    convert hUevent v hvU using 1

private lemma latentProduct_localConsistent_factorization
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.latentProduct {ℓ | ∀ v (hv : v ∈ P),
      M.localConsistent s x v (hP.1 hv) ℓ} =
      ∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ P)
          (fun _ hv => hP.1 (Finset.mem_of_mem_inter_right hv)) x := by
  rw [localConsistent_event_eq_component_biInter M s P hP x]
  classical
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun C =>
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
      M.localConsistent s x v
        (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ}
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)),
        S ⊆ M.toSWIGGraph.cComponentSet →
          M.latentProduct (⋂ C ∈ S, E C) =
            ∏ C ∈ S, M.latentProduct (E C) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro C S hCnot ih hSinsert
      have hS : S ⊆ M.toSWIGGraph.cComponentSet := by
        intro D hD
        exact hSinsert (Finset.mem_insert_of_mem hD)
      have hC : C ∈ M.toSWIGGraph.cComponentSet :=
        hSinsert (Finset.mem_insert_self C S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) :=
        latentBlockIndex_biUnion_disjoint M hS hC hCnot
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M C => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M C) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ D ∈ S, E D) := by
        simpa [E] using
          localConsistent_biInter_event_measurable_comap_latentBlockIndex
            M s P hP x hS
      have hmeasC :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M C => ℓ u)
              inferInstance]
            (E C) := by
        simpa [E] using
          localConsistent_event_measurable_comap_latentBlockIndex
            M s P hP x hC
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasC
      calc
        M.latentProduct (⋂ D ∈ insert C S, E D)
            = M.latentProduct ((⋂ D ∈ S, E D) ∩ E C) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ D ∈ S, E D) * M.latentProduct (E C) := by
              exact hinter
        _ = (∏ D ∈ S, M.latentProduct (E D)) * M.latentProduct (E C) := by
              rw [ih hS]
        _ = ∏ D ∈ insert C S, M.latentProduct (E D) := by
              rw [Finset.prod_insert hCnot]
              rw [mul_comm]
  have hfull := hfactor M.toSWIGGraph.cComponentSet (fun _ h => h)
  simpa [E, qLocalMass] using hfull

/-- For [a finite family `𝒞` of observed node sets](hyp:h𝒞obs) whose [latent parent blocks are
pairwise disjoint](hyp:hblock), [the local q-mass on the union of the family equals the
product, over the members `U` of `𝒞`, of the local q-mass on `U`](goal). -/
lemma qLocalMass_prod_of_latentBlock_disjoint
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s (𝒞.sup id)
        (fun v hv => by
          rw [Finset.mem_sup] at hv
          rcases hv with ⟨U, hU, hvU⟩
          exact h𝒞obs U hU hvU) x =
      ∏ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then M.qLocalMass s U (h𝒞obs U hU) x else 1 := by
  classical
  let hSup : 𝒞.sup id ⊆ M.observed := fun v hv => by
    rw [Finset.mem_sup] at hv
    rcases hv with ⟨U, hU, hvU⟩
    exact h𝒞obs U hU hvU
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun U =>
    if hU : U ∈ 𝒞 then
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (h𝒞obs U hU hv) ℓ}
    else Set.univ
  have hevent :
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ 𝒞.sup id),
        M.localConsistent s x v (hSup hv) ℓ} =
        ⋂ U ∈ 𝒞, E U := by
    simpa [E, hSup] using
      localConsistent_event_eq_family_biInter M s 𝒞 h𝒞obs hSup x
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)), S ⊆ 𝒞 →
        M.latentProduct (⋂ U ∈ S, E U) =
          ∏ U ∈ S, M.latentProduct (E U) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro U S hUnot ih hSinsert
      have hS : S ⊆ 𝒞 := by
        intro V hV
        exact hSinsert (Finset.mem_insert_of_mem hV)
      have hU : U ∈ 𝒞 := hSinsert (Finset.mem_insert_self U S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M U) :=
        latentBlockIndex_biUnion_disjoint_of_pairwise M hS hU hUnot hblock
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M U => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M U) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ V ∈ S, E V) := by
        have hbase :=
          localConsistent_biInter_event_measurable_comap_latentBlockIndex_of_family
            M s 𝒞 S hS h𝒞obs x
        convert hbase using 1
        ext ℓ
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · intro h V hVS
          have hEV := h V hVS
          simpa [E, hS hVS] using hEV
        · intro h V hVS
          have hEV := h V hVS
          simpa [E, hS hVS] using hEV
      have hmeasU :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M U => ℓ u)
              inferInstance]
            (E U) := by
        simpa [E, hU] using
          localConsistent_event_measurable_comap_latentBlockIndex_of_family
            M s U (h𝒞obs U hU) x
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasU
      calc
        M.latentProduct (⋂ V ∈ insert U S, E V)
            = M.latentProduct ((⋂ V ∈ S, E V) ∩ E U) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ V ∈ S, E V) * M.latentProduct (E U) := by
              exact hinter
        _ = (∏ V ∈ S, M.latentProduct (E V)) * M.latentProduct (E U) := by
              rw [ih hS]
        _ = ∏ V ∈ insert U S, M.latentProduct (E V) := by
              rw [Finset.prod_insert hUnot]
              rw [mul_comm]
  have hfull := hfactor 𝒞 (fun _ h => h)
  simp only [causal_defs_simps]
  rw [hevent]
  rw [hfull]
  refine Finset.prod_congr rfl ?_
  intro U hU
  simp [E, hU]

set_option maxHeartbeats 800000 in
-- This proof repeats the latent-block independence argument with an extra
-- intersection parameter, which gives Lean a large dependent event expression.
/-- Local q-mass on a covered set factors over an abstract family after
intersecting each family member with the covered set. -/
lemma qLocalMass_prod_inter_of_latentBlock_disjoint
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hPobs : P ⊆ M.observed)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hcover : P ⊆ 𝒞.sup id)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s P hPobs x =
      ∏ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then
          M.qLocalMass s (U ∩ P)
            (fun _ hv => h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) x
        else 1 := by
  classical
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun U =>
    if hU : U ∈ 𝒞 then
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U ∩ P),
        M.localConsistent s x v
          (h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) ℓ}
    else Set.univ
  have hevent :
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ P),
        M.localConsistent s x v (hPobs hv) ℓ} =
        ⋂ U ∈ 𝒞, E U := by
    ext ℓ
    constructor
    · intro hℓ
      rw [Set.mem_iInter]
      intro U
      rw [Set.mem_iInter]
      intro hU
      simp [E, hU]
      intro v _hvU hvP
      exact hℓ v hvP
    · intro hℓ v hvP
      rw [Set.mem_iInter] at hℓ
      have hvSup : v ∈ 𝒞.sup id := hcover hvP
      rw [Finset.mem_sup] at hvSup
      rcases hvSup with ⟨U, hU, hvU⟩
      have hℓU := hℓ U
      rw [Set.mem_iInter] at hℓU
      have hUevent :
          ℓ ∈ {ℓ : M.LatentValues | ∀ v (hv : v ∈ U ∩ P),
            M.localConsistent s x v
              (h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) ℓ} := by
        simpa [E, hU] using hℓU hU
      have hvUP : v ∈ U ∩ P := Finset.mem_inter.mpr ⟨hvU, hvP⟩
      convert hUevent v hvUP using 1
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)), S ⊆ 𝒞 →
        M.latentProduct (⋂ U ∈ S, E U) =
          ∏ U ∈ S, M.latentProduct (E U) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro U S hUnot ih hSinsert
      have hS : S ⊆ 𝒞 := by
        intro V hV
        exact hSinsert (Finset.mem_insert_of_mem hV)
      have hU : U ∈ 𝒞 := hSinsert (Finset.mem_insert_self U S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M U) :=
        latentBlockIndex_biUnion_disjoint_of_pairwise M hS hU hUnot hblock
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M U => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M U) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ V ∈ S, E V) := by
        refine measurableSet_comap_piFinset_of_depends
          (S := S.biUnion (latentBlockIndex M)) _ ?_
        intro ℓ ℓ' hagree
        constructor
        · intro hℓ
          rw [Set.mem_iInter] at hℓ
          rw [Set.mem_iInter]
          intro V
          have hℓV := hℓ V
          rw [Set.mem_iInter] at hℓV
          rw [Set.mem_iInter]
          intro hVS
          have hV𝒞 : V ∈ 𝒞 := hS hVS
          simp [E, hV𝒞]
          intro v hvV hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs V hV𝒞 hvV) ℓ := by
            have hEV : ℓ ∈ E V := hℓV hVS
            have hEV' :
                ∀ v (hv : v ∈ V ∩ P),
                  M.localConsistent s x v
                    (h𝒞obs V hV𝒞 (Finset.mem_of_mem_inter_left hv)) ℓ := by
              simpa [E, hV𝒞] using hEV
            exact hEV' v (Finset.mem_inter.mpr ⟨hvV, hvP⟩)
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvV (h𝒞obs V hV𝒞 hvV) ℓ ℓ' (by
              intro u hu
              have hmemBlock :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M V :=
                (mem_latentBlockIndex_iff M V _).mpr hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ S.biUnion (latentBlockIndex M) := by
                rw [Finset.mem_biUnion]
                exact ⟨V, hVS, hmemBlock⟩
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord)).mp hlocal
        · intro hℓ'
          rw [Set.mem_iInter] at hℓ'
          rw [Set.mem_iInter]
          intro V
          have hℓ'V := hℓ' V
          rw [Set.mem_iInter] at hℓ'V
          rw [Set.mem_iInter]
          intro hVS
          have hV𝒞 : V ∈ 𝒞 := hS hVS
          simp [E, hV𝒞]
          intro v hvV hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs V hV𝒞 hvV) ℓ' := by
            have hEV : ℓ' ∈ E V := hℓ'V hVS
            have hEV' :
                ∀ v (hv : v ∈ V ∩ P),
                  M.localConsistent s x v
                    (h𝒞obs V hV𝒞 (Finset.mem_of_mem_inter_left hv)) ℓ' := by
              simpa [E, hV𝒞] using hEV
            exact hEV' v (Finset.mem_inter.mpr ⟨hvV, hvP⟩)
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvV (h𝒞obs V hV𝒞 hvV) ℓ' ℓ (by
              intro u hu
              have hmemBlock :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M V :=
                (mem_latentBlockIndex_iff M V _).mpr hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ S.biUnion (latentBlockIndex M) := by
                rw [Finset.mem_biUnion]
                exact ⟨V, hVS, hmemBlock⟩
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord.symm)).mp hlocal
      have hmeasU :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M U => ℓ u)
              inferInstance]
            (E U) := by
        refine measurableSet_comap_piFinset_of_depends
          (S := latentBlockIndex M U) _ ?_
        intro ℓ ℓ' hagree
        constructor
        · intro hℓ
          simp [E, hU] at hℓ ⊢
          intro v hvU hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs U hU hvU) ℓ := hℓ v hvU hvP
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvU (h𝒞obs U hU hvU) ℓ ℓ' (by
              intro u hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M U :=
                (mem_latentBlockIndex_iff M U _).mpr hu
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord)).mp hlocal
        · intro hℓ'
          simp [E, hU] at hℓ' ⊢
          intro v hvU hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs U hU hvU) ℓ' := hℓ' v hvU hvP
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvU (h𝒞obs U hU hvU) ℓ' ℓ (by
              intro u hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M U :=
                (mem_latentBlockIndex_iff M U _).mpr hu
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord.symm)).mp hlocal
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasU
      calc
        M.latentProduct (⋂ V ∈ insert U S, E V)
            = M.latentProduct ((⋂ V ∈ S, E V) ∩ E U) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ V ∈ S, E V) * M.latentProduct (E U) := by
              exact hinter
        _ = (∏ V ∈ S, M.latentProduct (E V)) * M.latentProduct (E U) := by
              rw [ih hS]
        _ = ∏ V ∈ insert U S, M.latentProduct (E V) := by
              rw [Finset.prod_insert hUnot]
              rw [mul_comm]
  have hfull := hfactor 𝒞 (fun _ h => h)
  simp only [causal_defs_simps]
  rw [hevent]
  rw [hfull]
  refine Finset.prod_congr rfl ?_
  intro U hU
  simp [E, hU]

/-- For [a set of observed nodes `P` that is closed under observed parents](hyp:hP), [the
singleton mass of the projection of the observational law onto `P` equals the product, over
the full c-components `C` of the graph, of the local q-mass on `C ∩ P`](goal). -/
theorem obsKernel_marginal_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection hP.1)) {valuesProjection hP.1 x}
      = ∏ C ∈ M.toSWIGGraph.cComponentSet,
          M.qLocalMass s (C ∩ P)
            (fun _ hv => hP.1 (Finset.mem_of_mem_inter_right hv)) x := by
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
  rw [hset]
  exact latentProduct_localConsistent_factorization M s P hP x

/-- Positive observational mass implies nonzero local q-mass. -/
lemma qLocalMass_pos_of_positiveObs
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [MeasurableSingletonClass (ValuesOn M.observed (swigΩ Ω))]
    (hpos : ID.DiscreteID.PositiveMass (M.obsKernel s)) :
    ∀ T hT x, M.qLocalMass s T hT x ≠ 0 := by
  classical
  intro T hT x
  have hobs : M.observed ⊆ M.observed := fun ⦃_⦄ hv => hv
  have hclosed : M.ObsParentClosed M.observed := by
    refine ⟨hobs, ?_⟩
    intro _v _hv _w hw _hedge
    exact hw
  have hmass := obsKernel_marginal_singleton_eq_latentProduct_agree
    M s (P := M.observed) hobs x
  have hset :
      {ℓ : M.LatentValues | ∀ v : {v // v ∈ M.observed},
        M.evalMap s ℓ
            ⟨v.val, Finset.mem_union_left M.unobserved v.property⟩ =
          x ⟨v.val, v.property⟩}
        =
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ M.observed),
        M.localConsistent s x v hv ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M.evalMap_agree_iff_localConsistent s M.observed hclosed x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M.evalMap_agree_iff_localConsistent s M.observed hclosed x ℓ).mpr
        hLocal v.val v.property
  rw [hset] at hmass
  have hproj_id :
      (valuesProjection (Ω := swigΩ Ω)
        hobs
        : ValuesOn M.observed (swigΩ Ω) → ValuesOn M.observed (swigΩ Ω)) = id := by
    funext ξ
    rfl
  rw [hproj_id, Measure.map_id] at hmass
  have hfull : M.qLocalMass s M.observed hobs x ≠ 0 := by
    have hx :
        (M.obsKernel s) ({x} : Set (ValuesOn M.observed (swigΩ Ω))) ≠ 0 := by
      simpa [ID.DiscreteID.singletonMass_apply] using hpos x
    simpa [qLocalMass] using (hmass ▸ hx)
  have hle :
      M.qLocalMass s M.observed hobs x ≤ M.qLocalMass s T hT x :=
    M.qLocalMass_anti s (T := T) (T' := M.observed) hT hT hobs x
  intro hzero
  exact hfull (le_antisymm (by simpa [hzero] using hle) zero_le)


end Causalean.SCM

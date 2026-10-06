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
public import Causalean.SCM.ID.Density.QFactor.TianRecoveryLemmas

/-! # Tian district-density recovery

This file identifies a district density of the post-intervention ancestral law
with a mechanism c-factor and, for a full c-component, with the corresponding
observational c-component density.  It contains the terminal recovery results
assembled from the prefix-mass lemmas and mechanism invariance.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- **(B) Tian Lemma 1 for the do-model ancestral marginal.** Consider a structural causal
model `M` with [an intervention set `X` whose random copies are observed and whose fixed
copies are not already frozen](hyp:hObs,hFix), [an outcome set `Y` disjoint from the random
copies of `X`](hyp:hYX), under [a faithful reference-measure family](hyp:href), [a positive
observational kernel at every fixed-value assignment](hyp:hpos), and [the standing assumption
that `M` is a standard model](hyp:hStd). For [a set `S` that is simultaneously a district of
the post-intervention ancestral graph and a full c-component of `M`](hyp:hS,hSfull), and [an
extension map that inverts the projection onto the ancestral observed
coordinates](hyp:hExtend), [the Tian district density read off the do(X)-law ancestral
marginal at `S` agrees with the mechanism c-factor of the post-intervention model at the
extended point](goal). -/
theorem tianDistrictDensity_eq_mechCFactor_doModel
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (hStd : M.isStandard)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    tianDistrictDensity
        ((M.fixSet X hObs hFix).toSWIGGraph.induce
          (fixAncestralSet M X hObs hFix Y))
        (fixObservedAncestralSet M X hObs hFix Y)
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
      = (M.fixSet X hObs hFix).mechCFactor ref S
          (by
            have hSobs : S ⊆ M.observed :=
              M.toSWIGGraph.cComponentSet_subset_observed S hSfull
            simpa [SCM.fixSet_observed] using hSobs)
          sDo (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) :=
    doObsKernelAncestralMarginal M X hObs hFix Y sDo
  have hDobs : D ⊆ MX.observed := Finset.inter_subset_right
  have hSdoComp : S ∈ MX.toSWIGGraph.cComponentSet := by
    exact (fixSet_cComponentSet_mem M X hObs hFix S).mpr hSfull
  have hSobsMX : S ⊆ MX.observed :=
    MX.toSWIGGraph.cComponentSet_subset_observed S hSdoComp
  have hSobsM : S ⊆ M.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed S hSfull
  have hSD : S ⊆ D := by
    have hSHobs : S ⊆ H.observed := by
      exact H.cComponentSet_subset_observed S (by
        simpa [H, MX, fixTruncCComponentSet] using hS)
    exact hSHobs
  have hμpos : DiscreteID.PositiveMass μ := by
    simpa [μ] using
      doObsKernelAncestralMarginal_positiveMass M X hObs hFix Y hpos hYX sDo
  have hprefixMass_ne0 : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) ≠ 0 := by
    intro k
    have hmapPos :=
      DiscreteID.PositiveMass.map_valuesProjection (Ω' := swigΩ Ω)
        hμpos (H.prefixIn_subset D k)
    simpa [DiscreteID.singletonMass_apply] using
      hmapPos (valuesProjection (H.prefixIn_subset D k) xD)
  have hprefixProd_eq : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
        ∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD) := by
    intro k
    simpa [MX, D, H, μ, hDobs] using
      doObsKernelAncestralMarginal_prefix_singleton_eq_prod_qLocalMass
        M X hObs hFix Y sDo extend hExtend k xD
  have hprefixProd_ne0 : ∀ k,
      (∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
    intro k hzero
    exact hprefixMass_ne0 k (by rw [hprefixProd_eq k, hzero])
  have hfactor_ne0 : ∀ k C, C ∈ MX.toSWIGGraph.cComponentSet →
      MX.qLocalMass sDo (C ∩ H.prefixIn D k)
        (fun _ hv => hDobs (H.prefixIn_subset D k
          (Finset.mem_of_mem_inter_right hv))) (extend xD) ≠ 0 := by
    intro k C hC
    exact (Finset.prod_ne_zero_iff.mp (hprefixProd_ne0 k)) C hC
  have hS_q_ne0 : ∀ k ≤ D.card,
      MX.qLocalMass sDo (S ∩ H.prefixIn D k)
        (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) ≠ 0 := by
    intro k _hk
    simpa [hDobs, hSobsMX] using hfactor_ne0 k S hSdoComp
  have hpointS :
      valuesProjection hSobsMX (extend xD) = valuesProjection hSD xD := by
    have h :=
      valuesProjection_extend_eq_of_subset M
        (show D ⊆ M.observed from Finset.inter_subset_right)
        hSD hSobsM extend hExtend xD
    simpa [MX, SCM.fixSet_observed, hSobsMX, hSobsM] using h
  have hstep : ∀ i ∈ Finset.univ.filter
      (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      tianPrefixStepDensity H D μ ref i xD =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
    intro i hi
    have hiS : (H.nodesAt D i).val ∈ S := (Finset.mem_filter.mp hi).2
    have hmass :=
      tianPrefixStepDensity_eq_prefix_mass_ratio H D μ ref href i xD
        (hprefixMass_ne0 i.val)
    have hrest0 :
        (∏ C ∈ MX.toSWIGGraph.cComponentSet \ {S},
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (by
        intro C hC
        exact hfactor_ne0 i.val C (Finset.mem_sdiff.mp hC).1)
    have hcancel :=
      prefixIn_qProduct_ratio_eq_component_ratio_of_ne_zero
        MX H D sDo S hSdoComp i hDobs hiS (extend xD) hrest0
    calc
      tianPrefixStepDensity H D μ ref i xD
          =
        (((∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) /
          (∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD))) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))) := by
            rw [hmass, hprefixProd_eq (i.val + 1), hprefixProd_eq i.val]
      _ =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
            rw [hcancel]
  let idxS := Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S)
  let qratio : Fin D.card → ENNReal := fun i =>
    MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
    MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)
  let den : Fin D.card → ENNReal := fun i =>
    jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
      ({valuesProjection
        (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (H.nodesAt D i).property) xD} :
        Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))
  have hden0 : ∀ i ∈ idxS, den i ≠ 0 := by
    intro i _hi
    exact jointRef_singleton_ne_zero ref href _ _
  have hdentop : ∀ i ∈ idxS, den i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hqprod :
      (∏ i ∈ idxS, qratio i) =
        MX.qLocalMass sDo S hSobsMX (extend xD) := by
    simpa [idxS, qratio] using
      component_qLocalMass_ratio_product_prefixIn_of_ne_zero
        MX H D sDo S hSobsMX hSD (extend xD) hS_q_ne0
  have hdenprod :
      (∏ i ∈ idxS, den i) =
        jointRef ref S ({valuesProjection hSD xD} :
          Set (ValuesOn S (swigΩ Ω))) := by
    have hden_atom :
        (∏ i ∈ idxS, den i) =
          ∏ i ∈ idxS,
            ref.μ (H.nodesAt D i).val
              ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      dsimp [den]
      rw [jointRef_singleton_eq_prod]
      simp [valuesProjection]
    rw [hden_atom]
    simpa [idxS] using component_ref_atom_product_eq_jointRef_prefixIn H D ref S hSD xD
  have htian :
      tianDistrictDensity H D μ ref S xD =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
    unfold tianDistrictDensity
    calc
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        tianPrefixStepDensity H D μ ref i xD)
          = ∏ i ∈ idxS, qratio i / den i := by
            refine Finset.prod_congr ?_ ?_
            · simp [idxS]
            · intro i hi
              simpa [idxS, qratio, den] using hstep i (by simpa [idxS] using hi)
      _ = (∏ i ∈ idxS, qratio i) / (∏ i ∈ idxS, den i) := by
            exact ENNReal.prod_div_prod idxS qratio den hden0 hdentop
      _ = MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
            rw [hqprod, hdenprod]
  have hmech :
      MX.mechCFactor ref S hSobsMX sDo (extend xD) =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSobsMX (extend xD)} :
            Set (ValuesOn S (swigΩ Ω))) := by
    simpa [MX] using
      doModel_mechCFactor_eq_qLocalMass_div_jointRef
        M X hObs hFix hStd ref href sDo S hSobsMX (extend xD)
  rw [show
      tianDistrictDensity
          ((M.fixSet X hObs hFix).toSWIGGraph.induce
            (fixAncestralSet M X hObs hFix Y))
          (fixObservedAncestralSet M X hObs hFix Y)
          (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD =
        tianDistrictDensity H D μ ref S xD by rfl]
  rw [htian, hmech, hpointS]

/-- Consider [an intervention set `X` whose random copies are observed and whose fixed copies
are not already frozen](hyp:hObs,hFix) together with [an outcome set `Y` disjoint from the
random copies of `X`](hyp:hYX), under [a faithful reference-measure family](hyp:href) and [a
positive observational kernel at every fixed-value assignment](hyp:hpos). For [any district `S`
of the post-intervention ancestral graph](hyp:hS) and [an extension map inverting the
projection onto the ancestral observed coordinates](hyp:hExtend), [the Tian district density
read off the do(X)-law ancestral marginal at `S` equals the do-model local q-mass on `S`
divided by the reference atom mass of `S`](goal).

Unlike `tianDistrictDensity_eq_mechCFactor_doModel`, this statement does not require
the district to be a full c-component of the original graph. -/
theorem tianDistrictDensity_eq_qLocalMass_div_jointRef_district
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
      =
      MX.qLocalMass sDo S
          (show S ⊆ MX.observed from by
            intro v hv
            have hSHobs : S ⊆ H.observed :=
              H.cComponentSet_subset_observed S
                (by simpa [H, MX, fixTruncCComponentSet] using hS)
            have hvD : v ∈ D := by
              dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
              exact hSHobs hv
            exact (Finset.mem_inter.mp hvD).2)
          (extend xD) /
        jointRef ref S
          ({valuesProjection
            (show S ⊆ D from by
              intro v hv
              have hSHobs : S ⊆ H.observed :=
                H.cComponentSet_subset_observed S
                  (by simpa [H, MX, fixTruncCComponentSet] using hS)
              dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
              exact hSHobs hv) xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) :=
    doObsKernelAncestralMarginal M X hObs hFix Y sDo
  have hDobs : D ⊆ MX.observed := Finset.inter_subset_right
  have hScomp : S ∈ H.cComponentSet := by
    simpa [H, MX, fixTruncCComponentSet] using hS
  have hSobsMX : S ⊆ MX.observed := by
    intro v hv
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    have hvD : v ∈ D := by
      dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
      exact hSHobs hv
    exact (Finset.mem_inter.mp hvD).2
  have hSD : S ⊆ D := by
    intro v hv
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
    exact hSHobs hv
  have hdisj :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hμpos : DiscreteID.PositiveMass μ := by
    simpa [μ] using
      doObsKernelAncestralMarginal_positiveMass M X hObs hFix Y hpos hYX sDo
  have hprefixMass_ne0 : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) ≠ 0 := by
    intro k
    have hmapPos :=
      DiscreteID.PositiveMass.map_valuesProjection (Ω' := swigΩ Ω)
        hμpos (H.prefixIn_subset D k)
    simpa [DiscreteID.singletonMass_apply] using
      hmapPos (valuesProjection (H.prefixIn_subset D k) xD)
  have hprefixProd_eq : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
        ∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD) := by
    intro k
    simpa [MX, D, H, μ, hDobs] using
      doObsKernelAncestralMarginal_prefix_singleton_eq_prod_H_qLocalMass
        M X hObs hFix Y sDo extend hExtend k xD
  have hprefixProd_ne0 : ∀ k,
      (∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
    intro k hzero
    exact hprefixMass_ne0 k (by rw [hprefixProd_eq k, hzero])
  have hfactor_ne0 : ∀ k C, C ∈ H.cComponentSet →
      MX.qLocalMass sDo (C ∩ H.prefixIn D k)
        (fun _ hv => hDobs (H.prefixIn_subset D k
          (Finset.mem_of_mem_inter_right hv))) (extend xD) ≠ 0 := by
    intro k C hC
    exact (Finset.prod_ne_zero_iff.mp (hprefixProd_ne0 k)) C hC
  have hS_q_ne0 : ∀ k ≤ D.card,
      MX.qLocalMass sDo (S ∩ H.prefixIn D k)
        (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) ≠ 0 := by
    intro k _hk
    simpa [hDobs, hSobsMX] using hfactor_ne0 k S hScomp
  have hstep : ∀ i ∈ Finset.univ.filter
      (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      tianPrefixStepDensity H D μ ref i xD =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
    intro i hi
    have hiS : (H.nodesAt D i).val ∈ S := (Finset.mem_filter.mp hi).2
    have hmass :=
      tianPrefixStepDensity_eq_prefix_mass_ratio H D μ ref href i xD
        (hprefixMass_ne0 i.val)
    have hrest0 :
        (∏ C ∈ H.cComponentSet \ {S},
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (by
        intro C hC
        exact hfactor_ne0 i.val C (Finset.mem_sdiff.mp hC).1)
    have hcancel :=
      prefixIn_qProduct_ratio_eq_component_ratio_of_family_of_ne_zero
        MX H D sDo H.cComponentSet S hScomp
          (fun C hC hne => hdisj hC hScomp hne)
          i hDobs hiS (extend xD) hrest0
    calc
      tianPrefixStepDensity H D μ ref i xD
          =
        (((∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) /
          (∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD))) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))) := by
            rw [hmass, hprefixProd_eq (i.val + 1), hprefixProd_eq i.val]
      _ =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
            rw [hcancel]
  let idxS := Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S)
  let qratio : Fin D.card → ENNReal := fun i =>
    MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
    MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)
  let den : Fin D.card → ENNReal := fun i =>
    jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
      ({valuesProjection
        (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (H.nodesAt D i).property) xD} :
        Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))
  have hden0 : ∀ i ∈ idxS, den i ≠ 0 := by
    intro i _hi
    exact jointRef_singleton_ne_zero ref href _ _
  have hdentop : ∀ i ∈ idxS, den i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hqprod :
      (∏ i ∈ idxS, qratio i) =
        MX.qLocalMass sDo S hSobsMX (extend xD) := by
    simpa [idxS, qratio] using
      component_qLocalMass_ratio_product_prefixIn_of_ne_zero
        MX H D sDo S hSobsMX hSD (extend xD) hS_q_ne0
  have hdenprod :
      (∏ i ∈ idxS, den i) =
        jointRef ref S ({valuesProjection hSD xD} :
          Set (ValuesOn S (swigΩ Ω))) := by
    have hden_atom :
        (∏ i ∈ idxS, den i) =
          ∏ i ∈ idxS,
            ref.μ (H.nodesAt D i).val
              ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      dsimp [den]
      rw [jointRef_singleton_eq_prod]
      simp [valuesProjection]
    rw [hden_atom]
    simpa [idxS] using component_ref_atom_product_eq_jointRef_prefixIn H D ref S hSD xD
  have htian :
      tianDistrictDensity H D μ ref S xD =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
    unfold tianDistrictDensity
    calc
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        tianPrefixStepDensity H D μ ref i xD)
          = ∏ i ∈ idxS, qratio i / den i := by
            refine Finset.prod_congr ?_ ?_
            · simp [idxS]
            · intro i hi
              simpa [idxS, qratio, den] using hstep i (by simpa [idxS] using hi)
      _ = (∏ i ∈ idxS, qratio i) / (∏ i ∈ idxS, den i) := by
            exact ENNReal.prod_div_prod idxS qratio den hden0 hdentop
      _ = MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
            rw [hqprod, hdenprod]
  simpa [MX, D, H, μ] using htian

/-- **District recovery by c-factor projection consistency.** Consider [a standard
structural causal model `M`](hyp:hStd) with [an intervention set `X` whose random copies are
observed and whose fixed copies are not already frozen](hyp:hObs,hFix), under [a faithful
reference-measure family](hyp:href) and [a positive observational kernel at every fixed-value
assignment](hyp:hpos), for [an outcome set `Y` disjoint from the random copies of
`X`](hyp:hYX). For [a set `S` that is simultaneously a district of the post-intervention
ancestral graph and a full c-component of `M`](hyp:hS,hSfull), and [an extension map that
inverts the projection onto the ancestral observed coordinates and reproduces the intervention
values `sDo` on the intervened coordinates](hyp:hExtend,hExtendX), [the Tian district density
read off the do(X)-law ancestral marginal at `S` agrees, almost everywhere with respect to the
product reference measure on the ancestral observed coordinates, with the observational
c-component density factor at `S` pulled back through the extension](goal).

For a district `S` of the post-intervention ancestral graph `H = G_X[D]`
(`D := fixObservedAncestralSet`) that is also a full c-component of `M`, the
`S`-district factor extracted from the do-law ancestral marginal
`ν_M = (M.fixSet X).obsKernel.map π_D` equals, almost everywhere, the full
observational c-component factor `Q_M[S]` pulled back along any extension
`extend` that is the identity on the ancestral observed coordinates `D`.

Both sides are the same c-factor `Q[S]`: the left reads it from the do(X)-law
ancestral marginal, while the right reads it from the observational law.  They
agree because Tian's c-factor invariance leaves a full c-component avoiding the
intervention set unchanged under `do(X)`.  This theorem packages the final
projection-consistency step used by the density-level ID assembly.  It is a
library-specific recovery consequence, not Tian–Pearl Lemma 4; that numbered
result is the generalized Q-decomposition into c-components with prefix-ratio
recovery. -/
lemma tian_full_cComponent_density_recovery_core_direct
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
  classical
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
    (fixAncestralSet M X hObs hFix Y)
  have hSobs : S ⊆ M.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed S hSfull
  have hSD : S ⊆ D := by
    have hSHobs : S ⊆ H.observed := by
      exact H.cComponentSet_subset_observed S (by
        simpa [H, fixTruncCComponentSet] using hS)
    exact hSHobs
  have hSX : ∀ n ∈ X, SWIGNode.random n ∉ S := by
    intro n hn hnS
    have hnD : SWIGNode.random n ∈ D := hSD hnS
    have hnA : SWIGNode.random n ∈ fixAncestralSet M X hObs hFix Y := by
      simpa [D, fixObservedAncestralSet] using (Finset.mem_inter.mp hnD).1
    exact hYX n hn
      ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hn).mp hnA)
  filter_upwards with xD
  have hB :
      tianDistrictDensity H D
          (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
        = (M.fixSet X hObs hFix).mechCFactor ref S
            (by simpa [SCM.fixSet_observed] using hSobs)
            sDo (extend xD) := by
    simpa [H, D] using
      tianDistrictDensity_eq_mechCFactor_doModel
        M X hObs hFix Y ref href sDo hpos hYX hStd S hS hSfull
        extend hExtend xD
  have hC :
      (M.fixSet X hObs hFix).mechCFactor ref S
          (by simpa [SCM.fixSet_observed] using hSobs)
          sDo (extend xD)
        = M.mechCFactor ref S hSobs
            (M.fixSetProj X hObs hFix sDo) (extend xD) := by
    simpa using
      Causalean.SCM.ID.mechCFactor_fixSet_invariant
        M ref X href hStd hObs hFix S hSobs hSX sDo (extend xD)
        (fun D hD => hExtendX xD D hD)
  have hA :
      M.mechCFactor ref S hSobs
          (M.fixSetProj X hObs hFix sDo) (extend xD)
        = M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
    exact
      (Causalean.SCM.ID.cComponentDensityFactor_eq_mechCFactor
        M ref (M.fixSetProj X hObs hFix sDo) hStd S hSobs hSfull
        href (hpos (M.fixSetProj X hObs hFix sDo)) (extend xD)).symm
  exact hB.trans (hC.trans hA)

end SCM.ID
end Causalean

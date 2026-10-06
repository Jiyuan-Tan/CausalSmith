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

public import Causalean.SCM.ID.Density.MechCFactor.Ratios

/-! # Observational equality and intervention invariance of mechanism c-factors

This file identifies the observational c-component density with the mechanism
c-factor and proves that the latter is unchanged by interventions outside the
component.  These are the two mechanism-level equalities used by Tian district
recovery.
-/

public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- A finite product of quotients is the quotient of the finite products when denominators are nonzero and finite. -/
lemma ENNReal.prod_div_prod {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f g : ι → ENNReal)
    (hg0 : ∀ i ∈ t, g i ≠ 0) (hgtop : ∀ i ∈ t, g i ≠ ∞) :
    (∏ i ∈ t, f i / g i) = (∏ i ∈ t, f i) / (∏ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have ih' :
          (∏ i ∈ t, f i / g i) = (∏ i ∈ t, f i) / (∏ i ∈ t, g i) :=
        ih (by intro i hi; exact hg0 i (Finset.mem_insert_of_mem hi))
          (by intro i hi; exact hgtop i (Finset.mem_insert_of_mem hi))
      have hprod0 : (∏ i ∈ t, g i) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (by
          intro i hi
          exact hg0 i (Finset.mem_insert_of_mem hi))
      have hprodtop : (∏ i ∈ t, g i) ≠ ∞ := by
        exact Finset.prod_ne_top_of_ne_top _ g (by
          intro i hi
          exact hgtop i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih']
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      rw [ENNReal.mul_inv]
      · ac_rfl
      · exact Or.inr hprodtop
      · exact Or.inr hprod0

private lemma ENNReal.prod_div_prod₂ {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f g h : ι → ENNReal)
    (hh0 : ∀ i ∈ t, h i ≠ 0) (hhtop : ∀ i ∈ t, h i ≠ ∞) :
    (∏ i ∈ t, (f i / g i) / h i) =
      (∏ i ∈ t, f i / g i) / (∏ i ∈ t, h i) := by
  exact ENNReal.prod_div_prod t (fun i => f i / g i) h hh0 hhtop

/-- For [a structural causal model and fixed assignment](hyp:M,s),
[an observed node block](hyp:S,hS), [faithful reference measures](hyp:ref,href), and
[an observed assignment](hyp:x), if [each fixed variable's random copy has no outgoing
edge](hyp:hfe), then [the mechanism c-factor equals the local q-mass divided by the block's
reference singleton mass](goal). -/
lemma mechCFactor_eq_qLocalMass_div_jointRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.mechCFactor ref S hS s x =
      M.qLocalMass s S hS x /
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by
  have hnum :
      QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
        = M.qLocalMass s S hS x :=
    QmechMeasure_singleton_eq_qLocalMass M S hS hfe s x
  have hden0 :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hS x)
  have hdenTop :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hS x} : Set (ValuesOn S (swigΩ Ω))))
  unfold mechCFactor
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure M S hS (M.mechDoValues S s x)))
      (valuesProjection hS x) hden0 hdenTop]
  rw [hnum]

private lemma component_qLocalMass_ratio_product
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  let T : Finset ℕ := (Finset.range M.observed.card).filter fun k =>
    if hk : k < M.observed.card then
      M.toSWIGGraph.cComponentOf (M.observedAt ⟨k, hk⟩).val = S
    else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < M.observed.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range M.observed.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne : ∀ k ≤ M.observed.card, a k ≠ 0 := by
    intro k hk
    exact M.qLocalMass_pos_of_positiveObs s hpos (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  have hfin : ∀ k ≤ M.observed.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top M s (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  have hconst : ∀ k < M.observed.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_ne :
        M.toSWIGGraph.cComponentOf (M.observedAt ⟨k, hk⟩).val ≠ S := by
      intro hnode
      exact hnot (by
        simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ M.prefixNodes (k + 1) = S ∩ M.prefixNodes k :=
      cComponent_inter_prefix_succ_eq_of_node_ne M hScomp hnode_ne
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ M.prefixNodes (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ M.prefixNodes k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a M.observed.card / a 0 :=
    prod_filter_div_telescope a M.observed.card T hTsubset hne hfin hconst
  have htop : S ∩ M.prefixNodes M.observed.card = S := by
    rw [M.prefixNodes_card M.observed.card (le_refl _)]
    exact Finset.inter_eq_left.mpr hS
  have hzero : S ∩ M.prefixNodes 0 = ∅ := by
    rw [M.prefixNodes_zero, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x)
        = ∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a M.observed.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

/-- Multiplying the singleton reference masses for all observed variables in one c-component
equals the singleton mass of their joint reference measure. -/
lemma component_ref_atom_product_eq_jointRef
    [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
      =
    jointRef ref S ({valuesProjection hS x} :
      Set (ValuesOn S (swigΩ Ω))) := by
  classical
  have hprod :
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
        ref.μ (M.observedAt i).val
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
        =
      ∏ v : {v // v ∈ S},
        ref.μ v.val ({(valuesProjection hS x) v} :
          Set (swigΩ Ω v.val)) := by
    refine Finset.prod_bij
      (fun i hi =>
        ⟨(M.observedAt i).val,
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (M.observedAt i).property hScomp).mpr
            (Finset.mem_filter.mp hi).2⟩)
      ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro i _hi j _hj hij
      have hval : (M.observedAt i).val = (M.observedAt j).val :=
        congrArg (fun v : {v // v ∈ S} => v.val) hij
      have hsub : M.observedAt i = M.observedAt j :=
        Subtype.ext hval
      calc
        i = M.observedIndex (M.observedAt i) := (M.observedIndex_observedAt i).symm
        _ = M.observedIndex (M.observedAt j) := by rw [hsub]
        _ = j := M.observedIndex_observedAt j
    · intro v _hv
      let i : Fin M.observed.card := M.observedIndex ⟨v.val, hS v.property⟩
      have hnode : (M.observedAt i).val = v.val :=
        M.observedAt_observedIndex ⟨v.val, hS v.property⟩
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hvcomp :
            M.toSWIGGraph.cComponentOf v.val = S :=
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (hS v.property) hScomp).mp v.property
        simpa [hnode] using hvcomp
      · exact Subtype.ext hnode
    · intro i hi
      simp [valuesProjection]
  rw [jointRef_singleton_eq_prod]
  exact hprod

/-- **(A) Tian Lemma 1 (Eq. 37 = Eq. 36).** For [a standard causal model `M`,
i.e. one with no fixed nodes](hyp:hStd), a reference family that is
[faithful — every coordinate value has nonzero reference mass](hyp:href), and
an observational kernel at a fixed-value slice `s` with [full point-mass
support (every observed assignment has nonzero probability)](hyp:hpos), fix
[a node set `S` contained in the observed coordinates](hyp:hS) that is [a full
c-component of the model's SWIG graph](hyp:hScomp). Then [the observational
full-prefix c-component density `cComponentDensityFactor` on `S` equals the
mechanism c-factor `Q[S]` (`mechCFactor`) — the do-complement marginal density
of `S`](goal).

The prefix-conditional product `cComponentDensityFactor` telescopes to the
do(observed∖S) marginal.  The equality is a statement about the whole
telescoped product, not about matching each one-node conditional factor
separately. -/
lemma cComponentDensityFactor_eq_mechCFactor
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (hStd : M.isStandard)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.cComponentDensityFactor ref s S x = M.mechCFactor ref S hS s x := by
  classical
  let I : Finset (Fin M.observed.card) :=
    Finset.univ.filter
      (fun i : Fin M.observed.card =>
        M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
  let num : Fin M.observed.card → ENNReal := fun i =>
    M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
      (fun _ hv =>
        M.prefixNodes_subset_observed (i.val + 1)
          (Finset.mem_of_mem_inter_right hv)) x
  let den : Fin M.observed.card → ENNReal := fun i =>
    M.qLocalMass s (S ∩ M.prefixNodes i.val)
      (fun _ hv =>
        M.prefixNodes_subset_observed i.val
          (Finset.mem_of_mem_inter_right hv)) x
  let atom : Fin M.observed.card → ENNReal := fun i =>
    ref.μ (M.observedAt i).val
      ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
  have hsteps :
      M.cComponentDensityFactor ref s S x =
        ∏ i ∈ I, (num i / den i) / atom i := by
    unfold cComponentDensityFactor
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S :=
      (Finset.mem_filter.mp hi).2
    exact obsStepCondDensity_eq_component_ratio_div_ref
      M ref s S hScomp i hiS href hpos x
  have hatom0 : ∀ i ∈ I, atom i ≠ 0 := by
    intro i _hi
    exact href (M.observedAt i).val (x (M.observedAt i))
  have hatomtop : ∀ i ∈ I, atom i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt
      (MeasureTheory.measure_lt_top (ref.μ (M.observedAt i).val)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
  have hsplit :
      (∏ i ∈ I, (num i / den i) / atom i) =
        (∏ i ∈ I, num i / den i) / (∏ i ∈ I, atom i) :=
    ENNReal.prod_div_prod₂ I num den atom hatom0 hatomtop
  have hnum :
      (∏ i ∈ I, num i / den i) = M.qLocalMass s S hS x := by
    simpa [I, num, den] using
      component_qLocalMass_ratio_product M s S hS hScomp hpos x
  have hrefprod :
      (∏ i ∈ I, atom i) =
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by
    simpa [I, atom] using
      component_ref_atom_product_eq_jointRef M ref S hS hScomp x
  have hanchor :
      M.mechCFactor ref S hS s x =
        M.qLocalMass s S hS x /
          jointRef ref S ({valuesProjection hS x} :
            Set (ValuesOn S (swigΩ Ω))) :=
    mechCFactor_eq_qLocalMass_div_jointRef M ref s S hS href
      (standard_fixed_random_edgeless M hStd) x
  calc
    M.cComponentDensityFactor ref s S x
        = ∏ i ∈ I, (num i / den i) / atom i := hsteps
    _ = (∏ i ∈ I, num i / den i) / (∏ i ∈ I, atom i) := hsplit
    _ = M.qLocalMass s S hS x /
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by rw [hnum, hrefprod]
    _ = M.mechCFactor ref S hS s x := hanchor.symm

/-- Local q-mass is invariant under a `fixSet` intervention when no coordinate
in `S` is one of the intervened random nodes and the full assignment pins each
intervened random node to the corresponding fixed value. -/
lemma qLocalMass_fixSet_invariant
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hSX : ∀ n ∈ X, SWIGNode.random n ∉ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hpin : ∀ D (hD : D ∈ X),
      x ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    (M.fixSet X hObs hFix).qLocalMass sDo S
        (by simpa [fixSet_observed] using hS) x =
      M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x := by
  classical
  let MX := M.fixSet X hObs hFix
  let hSXobs : S ⊆ MX.observed := by
    simpa [MX, fixSet_observed] using hS
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      x ⟨w, by simpa [MX, fixSet_observed] using hw⟩ = x ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hproj : M.fixSetProj X hObs hFix sDo =
      M.fixSetProj X hObs hFix sDo := rfl
  unfold qLocalMass
  congr 1
  ext ℓ
  constructor
  · intro hLocal v hv
    have hnot : v ∉ X.image SWIGNode.random := by
      intro hvX
      rcases Finset.mem_image.mp hvX with ⟨D, hD, rfl⟩
      exact hSX D hD hv
    exact (localConsistent_fixSet_iff M X hObs hFix sDo
      (M.fixSetProj X hObs hFix sDo) x x v (hSXobs hv) (hS hv)
      hnot hobsAgree hpin hproj ℓ).mp (hLocal v hv)
  · intro hLocal v hv
    have hnot : v ∉ X.image SWIGNode.random := by
      intro hvX
      rcases Finset.mem_image.mp hvX with ⟨D, hD, rfl⟩
      exact hSX D hD hv
    exact (localConsistent_fixSet_iff M X hObs hFix sDo
      (M.fixSetProj X hObs hFix sDo) x x v (hSXobs hv) (hS hv)
      hnot hobsAgree hpin hproj ℓ).mpr (hLocal v hv)

/-- **Do(X)-invariance of the c-factor `Q[S]`.** Let an
intervention set `X` have [random copies that are all observed](hyp:hObs) and
[fixed copies that are not already fixed in the base model](hyp:hFix), giving
the intervened model `M.fixSet X`. For [a standard base model
`M`](hyp:hStd), a reference family that is [faithful](hyp:href), and
[a node set `S` contained in the observed coordinates](hyp:hS) whose [random
copies avoid every intervened node in `X`](hyp:hSX), if [the base assignment
`x` records, at each intervened node, the same value that the intervened
model's fixed values `sDo` assign to the corresponding fixed
coordinate](hyp:hpin), then [the `S`-c-factor `Q[S]` of the intervened model
`M.fixSet X` at `sDo`, `x` equals the `S`-c-factor of the base model `M` at
the projected fixed values `M.fixSetProj X sDo`, `x`](goal).

The `S`-c-factor of the do-model `M.fixSet X` equals the `S`-c-factor of the
original model at the projected fixed-value slice.  The proof reduces both
mechanism c-factors to the same local q-mass and the same reference atom: the
intervention changes coordinates outside `S`, while the supplied pinning
hypothesis makes the full observed assignment agree with the intervention
values on the treated random copies.  This is a library-specific invariance
lemma used in formalizing consequences of Tian's c-factor construction; it is
not Tian–Pearl Lemma 4, which states generalized Q-decomposition. -/
lemma mechCFactor_fixSet_invariant
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (X : Finset N)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hSX : ∀ n ∈ X, SWIGNode.random n ∉ S)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hpin : ∀ D (hD : D ∈ X),
      x ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    (M.fixSet X hObs hFix).mechCFactor ref S
        (by simpa [fixSet_observed] using hS) sDo x
      = M.mechCFactor ref S hS (M.fixSetProj X hObs hFix sDo) x := by
  classical
  let MX := M.fixSet X hObs hFix
  let hSXobs : S ⊆ MX.observed := by
    simpa [MX, fixSet_observed] using hS
  have hfeX :
      ∀ n : N, SWIGNode.fixed n ∈ MX.fixed →
        ∀ v : SWIGNode N, ¬ MX.dag.edge (SWIGNode.random n) v := by
    simpa [MX] using fixSet_fixed_random_edgeless M X hObs hFix hStd
  have hfeM :
      ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
        ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v :=
    standard_fixed_random_edgeless M hStd
  have hq :
      MX.qLocalMass sDo S hSXobs x =
        M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x :=
    qLocalMass_fixSet_invariant M X hObs hFix sDo S hS hSX x hpin
  have hnumX :
      QmechMeasure MX S hSXobs (MX.mechDoValues S sDo x)
          {valuesProjection hSXobs x}
        = MX.qLocalMass sDo S hSXobs x :=
    QmechMeasure_singleton_eq_qLocalMass MX S hSXobs hfeX sDo x
  have hnumM :
      QmechMeasure M S hS
          (M.mechDoValues S (M.fixSetProj X hObs hFix sDo) x)
          {valuesProjection hS x}
        = M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x :=
    QmechMeasure_singleton_eq_qLocalMass M S hS hfeM
      (M.fixSetProj X hObs hFix sDo) x
  have hprojPoint : valuesProjection hSXobs x = valuesProjection hS x := by
    ext v
    rfl
  have hden0X :
      jointRef ref S ({valuesProjection hSXobs x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hSXobs x)
  have hdenTopX :
      jointRef ref S ({valuesProjection hSXobs x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hSXobs x} : Set (ValuesOn S (swigΩ Ω))))
  have hden0M :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hS x)
  have hdenTopM :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hS x} : Set (ValuesOn S (swigΩ Ω))))
  unfold mechCFactor
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure MX S hSXobs (MX.mechDoValues S sDo x)))
      (valuesProjection hSXobs x) hden0X hdenTopX]
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure M S hS
          (M.mechDoValues S (M.fixSetProj X hObs hFix sDo) x)))
      (valuesProjection hS x) hden0M hdenTopM]
  rw [hnumX, hnumM, hq, hprojPoint]


end SCM.ID
end Causalean

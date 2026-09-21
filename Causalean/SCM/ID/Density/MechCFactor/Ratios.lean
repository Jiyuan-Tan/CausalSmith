/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.FiniteReference
public import Causalean.SCM.ID.Density.QMass
public import Causalean.SCM.ID.GraphicalThms.DoGFormula

public import Causalean.SCM.ID.Density.MechCFactor.Basic

/-! # Prefix ratios for mechanism c-factors

This file computes each observational step density as a ratio of component
q-masses and reference atoms.  Its component-intersection and cancellation
lemmas provide the algebraic bridge from the observational prefix product to a
single mechanism c-factor.
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

/-- The first k observed nodes in a structural causal model's topological order form a set closed
under observed parents. -/
lemma prefixNodes_obsParentClosed
    (M : Causalean.SCM N Ω) (k : ℕ) :
    M.ObsParentClosed (M.prefixNodes k) := by
  classical
  refine ⟨M.prefixNodes_subset_observed k, ?_⟩
  intro v hv w hwObs hEdge
  rcases (M.mem_prefixNodes_iff k v).mp hv with ⟨hvObs, hvlt⟩
  let i : Fin M.observed.card := M.observedIndex ⟨v, hvObs⟩
  have hi_eq : (M.observedAt i).val = v := by
    exact M.observedAt_observedIndex ⟨v, hvObs⟩
  have hwPred :
      w ∈ M.toSWIGGraph.observedPredecessors (M.observedAt i).val := by
    rw [hi_eq]
    exact Finset.mem_filter.mpr
      ⟨hwObs, M.dag.topoOrder_lt w v hEdge⟩
  have hwPrefixI : w ∈ M.prefixNodes i.val := by
    simpa using
      ((M.observedPredecessors_observedAt i.isLt).symm ▸ hwPred)
  exact M.prefixNodes_mono (show i.val ≤ k from Nat.le_of_lt hvlt) hwPrefixI

/-- For an observed node and a listed c-component, membership in that component
is equivalent to the computed c-component being the listed set. -/
lemma mem_cComponent_iff_cComponentOf_eq
    (G : SWIGGraph N) {v : SWIGNode N} {S : Finset (SWIGNode N)}
    (hv : v ∈ G.observed) (hS : S ∈ G.cComponentSet) :
    v ∈ S ↔ G.cComponentOf v = S := by
  constructor
  · intro hvS
    rw [SWIGGraph.cComponentSet, Finset.mem_image] at hS
    obtain ⟨w, hw, rfl⟩ := hS
    have hwv : G.bidirectedReachable w v :=
      (G.mem_cComponentOf_iff_reachable hw).mp hvS
    exact (G.cComponentOf_eq_of_reachable hwv).symm
  · intro hcomp
    exact hcomp ▸ G.mem_cComponentOf_self hv

/-- Given [a finite single-world intervention graph, an observed node, and a district](hyp:N,G,v,S),
if [the node is observed](hyp:hv) and [the set is a district](hyp:hS), then [the node belongs to
that district exactly when its assigned district is that set](goal). -/
@[deprecated mem_cComponent_iff_cComponentOf_eq (since := "2026-09-19")]
lemma mem_cComponent_iff_cComponentOf_eq_mech
    (G : SWIGGraph N) {v : SWIGNode N} {S : Finset (SWIGNode N)}
    (hv : v ∈ G.observed) (hS : S ∈ G.cComponentSet) :
    v ∈ S ↔ G.cComponentOf v = S :=
  mem_cComponent_iff_cComponentOf_eq G hv hS

private lemma obsKernel_prefix_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues) (k : ℕ)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection (M.prefixNodes_subset_observed k)))
        ({valuesProjection (M.prefixNodes_subset_observed k) x} :
          Set (ValuesOn (M.prefixNodes k) (swigΩ Ω)))
      =
    ∏ C ∈ M.toSWIGGraph.cComponentSet,
      M.qLocalMass s (C ∩ M.prefixNodes k)
        (fun _ hv =>
          M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x := by
  simpa using
    (M.obsKernel_marginal_singleton_eq_prod_qLocalMass s
      (M.prefixNodes k) (prefixNodes_obsParentClosed M k) x)

/-- Every local q-mass associated with fixed values, an observed node set, and
an observed assignment is finite. -/
lemma qLocalMass_ne_top
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x ≠ ∞ := by
  exact ne_of_lt (MeasureTheory.measure_lt_top M.latentProduct _)

/-- Cancelling a common nonzero finite factor preserves a quotient of extended nonnegative reals. -/
lemma ENNReal.div_mul_common
    {a b r : ENNReal} (hr0 : r ≠ 0) (hrtop : r ≠ ∞) :
    (a * r) / (b * r) = a / b := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv]
  · rw [show b⁻¹ * r⁻¹ * (a * r) = (r⁻¹ * r) * (b⁻¹ * a) by ac_rfl]
    rw [ENNReal.inv_mul_cancel hr0 hrtop]
    simp [mul_comm]
  · exact Or.inr hrtop
  · exact Or.inr hr0

/-- A finite product of finite extended nonnegative reals is finite. -/
lemma Finset.prod_ne_top_of_ne_top {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ENNReal) (hf : ∀ i ∈ s, f i ≠ ∞) :
    (∏ i ∈ s, f i) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ENNReal.mul_ne_top (hf a (Finset.mem_insert_self a s))
        (ih (by intro i hi; exact hf i (Finset.mem_insert_of_mem hi)))

private lemma cComponent_inter_prefix_succ_eq_of_ne
    (M : Causalean.SCM N Ω) {S C : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hCcomp : C ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin M.observed.card}
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (hCS : C ≠ S) :
    C ∩ M.prefixNodes (i.val + 1) = C ∩ M.prefixNodes i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [M.prefixNodes_succ i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (M.observedAt i).val := by simpa using hvnew
      subst hvnode
      have hnodeS : (M.observedAt i).val ∈ S := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hScomp).mpr hiS
      have hnodeC : (M.observedAt i).val ∈ C := hvC
      have hSC : S = C := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hCcomp).mp hnodeC ▸ hiS.symm
      exact False.elim (hCS hSC.symm)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, M.prefixNodes_mono (Nat.le_succ i.val) hvpre⟩

/-- Given [a finite structural causal model, a district, and a valid observed-node index](hyp:N,Ω,M,S,i),
if [the set is a district](hyp:hScomp) and [the indexed node's district differs from it](hyp:hiS),
then [the district's intersection with the observed prefix is unchanged at that step](goal). -/
lemma cComponent_inter_prefix_succ_eq_of_node_ne
    (M : Causalean.SCM N Ω) {S : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin M.observed.card}
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val ≠ S) :
    S ∩ M.prefixNodes (i.val + 1) = S ∩ M.prefixNodes i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    rw [M.prefixNodes_succ i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvS, hvold⟩
    · have hvnode : v = (M.observedAt i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (hiS
        ((mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hScomp).mp hvS))
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvS, M.prefixNodes_mono (Nat.le_succ i.val) hvpre⟩

private lemma prefix_qProduct_ratio_eq_component_ratio
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin M.observed.card)
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ M.prefixNodes (i.val + 1))
          (fun _ hv =>
            M.prefixNodes_subset_observed (i.val + 1)
              (Finset.mem_of_mem_inter_right hv)) x) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ M.prefixNodes i.val)
          (fun _ hv =>
            M.prefixNodes_subset_observed i.val
              (Finset.mem_of_mem_inter_right hv)) x)
      =
    M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ M.prefixNodes (i.val + 1))
      (fun _ hv => M.prefixNodes_subset_observed (i.val + 1)
        (Finset.mem_of_mem_inter_right hv)) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ M.prefixNodes i.val)
      (fun _ hv => M.prefixNodes_subset_observed i.val
        (Finset.mem_of_mem_inter_right hv)) x
  have hrest :
      ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C =
        ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hCcomp : C ∈ M.toSWIGGraph.cComponentSet := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀, cComponent_inter_prefix_succ_eq_of_ne M hScomp hCcomp hiS hCne]
  have hsplit₁ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) =
      f₁ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hScomp))
  have hsplit₀ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) =
      f₀ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hScomp))
  have hr0 : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  have hrtop : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top M s (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  change (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common hr0 hrtop

private lemma obsStepCondKernel_singleton_eq_obsCondKernel_singleton
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
      =
    M.obsCondKernel ({(M.observedAt i).val} : Finset (SWIGNode N))
        (M.prefixNodes i.val)
        (by
          intro v hv
          have hv_eq : v = (M.observedAt i).val := by simpa using hv
          simp [hv_eq, (M.observedAt i).property])
        (M.prefixNodes_subset_observed i.val)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({valuesProjection
          (by
            intro v hv
            have hv_eq : v = (M.observedAt i).val := by simpa using hv
            simp [hv_eq, (M.observedAt i).property])
          x} :
          Set (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
  unfold obsStepCondKernel
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValue (α := swigΩ Ω))]
  rw [MeasureTheory.Measure.map_apply
    (measurable_singletonValue (α := swigΩ Ω)) (MeasurableSet.singleton _)]
  congr 1
  ext y
  constructor
  · intro hy
    ext a
    obtain ⟨a, ha⟩ := a
    have ha' : a = (M.observedAt i).val := by simpa using ha
    subst a
    simpa [singletonValue, valuesProjection] using hy
  · intro hy
    have h := congrFun hy ⟨(M.observedAt i).val, by simp⟩
    simpa [singletonValue, valuesProjection] using h

private lemma obsStepCondKernel_singleton_eq_prefix_ratio
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
      =
    ((M.obsKernel s).map
        (valuesProjection (M.prefixNodes_subset_observed (i.val + 1))))
        ({valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x} :
          Set (ValuesOn (M.prefixNodes (i.val + 1)) (swigΩ Ω))) /
    ((M.obsKernel s).map
        (valuesProjection (M.prefixNodes_subset_observed i.val)))
        ({valuesProjection (M.prefixNodes_subset_observed i.val) x} :
          Set (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))) := by
  rw [obsStepCondKernel_singleton_eq_obsCondKernel_singleton]
  let hY : ({(M.observedAt i).val} : Finset (SWIGNode N)) ⊆ M.observed := by
    intro v hv
    have hv_eq : v = (M.observedAt i).val := by simpa using hv
    simp [hv_eq, (M.observedAt i).property]
  let hCC : M.prefixNodes i.val ⊆ M.observed := M.prefixNodes_subset_observed i.val
  have hc0 : ((M.obsKernel s).map (valuesProjection hCC))
        ({valuesProjection hCC x} :
          Set (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))) ≠ 0 := by
    rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  rw [obsCondKernel_singleton_mass_of_ne_zero M
    ({(M.observedAt i).val} : Finset (SWIGNode N)) (M.prefixNodes i.val)
    hY hCC s (valuesProjection hCC x) (valuesProjection hY x) hc0]
  congr 1
  let e : ValuesOn (M.prefixNodes (i.val + 1)) (swigΩ Ω) ≃ᵐ
      ValuesOn (M.prefixNodes i.val) (swigΩ Ω) ×
        ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ i.isLt)).trans
      (valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next i.isLt))
  have hfun :
      (fun ω : M.ObservedValues => (valuesProjection hCC ω, valuesProjection hY ω)) =
        e ∘ valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) := by
    exact (M.prefixSucc_projection_pair i.isLt).symm
  rw [hfun]
  rw [← MeasureTheory.Measure.map_map e.measurable
    (measurable_valuesProjection (M.prefixNodes_subset_observed (i.val + 1)))]
  rw [MeasureTheory.Measure.map_apply e.measurable (MeasurableSet.singleton _)]
  congr 1
  ext z
  have hxpair :
      e (valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x) =
        (valuesProjection hCC x, valuesProjection hY x) := by
    have h := congrFun (M.prefixSucc_projection_pair i.isLt) x
    simpa [e, hY, hCC, Function.comp_def] using h
  constructor
  · intro hz
    exact e.injective (by simpa [hxpair] using hz)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change e (valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x) =
      (valuesProjection hCC x, valuesProjection hY x)
    exact hxpair

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[coordinate reference measures and a fixed-node assignment](hyp:ref,s), [an observed
c-component](hyp:S), [evidence that it is a listed component](hyp:hScomp), [a position in the
observed topological order](hyp:i), [evidence that the node at that position belongs to the
component](hyp:hiS), [faithfulness of the reference measures](hyp:href), [positive
observational atom masses](hyp:hpos), and [an observed realization](hyp:x), [the one-step
observational conditional density equals the component's successive local-mass ratio divided
by the next coordinate's reference mass](goal). -/
lemma obsStepCondDensity_eq_component_ratio_div_ref
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin M.observed.card)
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.obsStepCondDensity ref s i x =
      (M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
          (fun _ hv =>
            M.prefixNodes_subset_observed (i.val + 1)
              (Finset.mem_of_mem_inter_right hv)) x /
        M.qLocalMass s (S ∩ M.prefixNodes i.val)
          (fun _ hv =>
            M.prefixNodes_subset_observed i.val
              (Finset.mem_of_mem_inter_right hv)) x) /
      ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) := by
  have hac : (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x) ≪
      ref.μ (M.observedAt i).val := by
    exact absolutelyContinuous_of_singleton_ne_zero _ _ (href (M.observedAt i).val)
  have href0 : ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ 0 :=
    href (M.observedAt i).val (x (M.observedAt i))
  have hreftop : ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (ref.μ (M.observedAt i).val) _)
  rw [obsStepCondDensity_eq_mass_ratio M ref s i x hac href0 hreftop]
  rw [obsStepCondKernel_singleton_eq_prefix_ratio M s i hpos x]
  rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
  rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
  rw [prefix_qProduct_ratio_eq_component_ratio M s S hScomp i hiS hpos x]


end SCM.ID
end Causalean

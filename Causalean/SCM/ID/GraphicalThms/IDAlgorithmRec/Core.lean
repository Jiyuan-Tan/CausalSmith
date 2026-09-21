/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.IDSoundDiscrete
public import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec

/-! # Density recovery for recursive IDENTIFY certificates

This file connects the mass-level recursive IDENTIFY functional to local
q-masses, proves its invariance under observational-kernel equivalence, and
recovers a reachable post-intervention district density from observational
data.  The full marginal and model-level soundness assembly is in `Soundness`.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

-- Match the finite-reference ID API in `IDAlgorithm.lean`: these statements keep
-- `Fintype` assumptions even when Lean can elaborate a particular wrapper
-- without using them syntactically.
set_option linter.unusedFintypeInType false

/-- For [a population of variables](hyp:N) with [finite value spaces](hyp:Ω),
[an observed-node set](hyp:O), [a node subset to be marginalized](hyp:W) [contained
in that observed set](hyp:hW), and [a nonnegative mass function on observed assignments](hyp:q),
[the observed-set marginalization functional](goal) assigns to each observed assignment
the sum of that mass function over all replacements on the specified subset.

Observed-set form of `SCM.marginalizeOn`, used only to expose that the
recursive mass functional is independent of the rest of the SCM record. -/
noncomputable def marginalizeOnObserved [∀ n, Fintype (Ω n)]
    (O W : Finset (SWIGNode N)) (hW : W ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x => ∑ y : ValuesOn W (swigΩ Ω), q (overrideOn x y)

/-- For [a population of variables](hyp:N) with [finite value spaces](hyp:Ω),
[an observed-node set](hyp:O), [a SWIG graph](hyp:G'), [an ancestral node set](hyp:A),
[a target district](hyp:C') [contained in the observed set](hyp:hA), and [a nonnegative
mass function on observed assignments](hyp:q), [the observed-set district-extraction
functional](goal) is the product of the successive marginal-ratio factors indexed by
the graph order of nodes in the target district.

Observed-set form of `SCM.extractDistrict`. -/
noncomputable def extractDistrictObserved [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin A.card => (G'.nodesAt A i).val ∈ C'),
      marginalizeOnObserved O (A \ G'.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x /
        marginalizeOnObserved O (A \ G'.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x

/-- For [a population of variables](hyp:N) with [finite value spaces](hyp:Ω),
[an observed-node set](hyp:O), [a SWIG graph](hyp:G), [a containing node set](hyp:T),
[a target district](hyp:C) [contained in the observed set](hyp:hT), and [a nonnegative
mass function on observed assignments](hyp:q), [the recursive observed-set mass
identification functional](goal) first [forms the induced ancestral set and records that
it is observed](step:1,step:2), then returns the appropriate marginal, original mass,
or recursively extracted district mass according to its ancestral-set cases.

Observed-set form of `SCM.identifyMassRec`. -/
noncomputable def identifyMassRecObserved [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G : SWIGGraph N) :
    (T C : Finset (SWIGNode N)) → (hT : T ⊆ O) →
      (q : ValuesOn O (swigΩ Ω) → ENNReal) →
        ValuesOn O (swigΩ Ω) → ENNReal
  | T, C, hT, q =>
    let A := inducedAncestral G T C
    let hA : A ⊆ O := fun _ hv =>
      hT (inducedAncestral_subset_left G T C hv)
    if _hAC : A = C then
      marginalizeOnObserved O (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q
    else if _hAT : A = T then
      q
    else
      let C₁ := containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ O := fun _ hv =>
        hT (inducedAncestral_subset_left G T C
          (containingCComponent_induce_subset G A C hv))
      identifyMassRecObserved O G C₁ C hC₁
        (extractDistrictObserved O (G.induce A) A C₁ hA
          (marginalizeOnObserved O (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q))
termination_by T _ _ _ => T.card
decreasing_by
  classical
  have hAsubT : A ⊆ T := inducedAncestral_subset_left G T C
  have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, _hAT⟩
  have hC₁subA : C₁ ⊆ A := containingCComponent_induce_subset G A C
  exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
    (Finset.card_lt_card hAssubT)

/-- [Marginalizing a full observational mass function](hyp:q) over
[an observed coordinate block](hyp:W,hW) in [a structural causal model](hyp:M)
[agrees exactly with the general finite-coordinate marginalization operation](goal). -/
@[simp] lemma marginalizeOnObserved_eq_marginalizeOn [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (W : Finset (SWIGNode N)) (hW : W ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    marginalizeOnObserved M.observed W hW q = SCM.marginalizeOn M.observed W hW q := by
  rfl

/-- For [a structural causal model](hyp:M), [the observed-only district extractor built from a
graph, ancestral block, target district, and mass function](hyp:G',A,C',q), where
[the ancestral block is observed](hyp:hA), [agrees pointwise with the general district
extractor](goal). -/
@[simp] lemma extractDistrictObserved_eq_extractDistrict [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    extractDistrictObserved M.observed G' A C' hA q =
      SCM.extractDistrict M.observed G' A C' hA q := by
  funext x
  unfold extractDistrictObserved SCM.extractDistrict
  rfl

/-- For [a structural causal model](hyp:M), [the observed-only recursive ID mass functional for a
graph, containing block, target district, and mass function](hyp:G,T,C,q), where
[the containing block is observed](hyp:hT), [agrees with the general recursive ID mass
functional](goal). -/
lemma identifyMassRecObserved_eq_identifyMassRec [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    identifyMassRecObserved M.observed G T C hT q =
      SCM.identifyMassRec M.observed G T C hT q := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
      (q : ValuesOn M.observed (swigΩ Ω) → ENNReal),
      T.card = n →
        identifyMassRecObserved M.observed G T C hT q =
          SCM.identifyMassRec M.observed G T C hT q
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
    intro T C hT q hcard
    rw [identifyMassRecObserved, SCM.identifyMassRec]
    by_cases hAC : inducedAncestral G T C = C
    · simp [hAC]
    · by_cases hAT : inducedAncestral G T C = T
      · simp [hAT]
      · simp only [hAC, hAT, marginalizeOnObserved_eq_marginalizeOn,
          extractDistrictObserved_eq_extractDistrict, dite_eq_ite]
        let A := inducedAncestral G T C
        let C₁ := containingCComponent (G.induce A) C
        have hAsubT : A ⊆ T := inducedAncestral_subset_left G T C
        have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, hAT⟩
        have hC₁subA : C₁ ⊆ A := containingCComponent_induce_subset G A C
        have hlt : C₁.card < n := by
          rw [← hcard]
          exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
            (Finset.card_lt_card hAssubT)
        exact ih C₁.card hlt C₁ C _ _ rfl
  exact hP T.card T C hT q rfl

/-- For [a finite population of variables](hyp:N) with [measurable value spaces](hyp:Ω),
[a structural causal model](hyp:M), [reference measures](hyp:ref), [a fixed-value
assignment](hyp:s), [a containing c-component](hyp:C), and [a target district](hyp:S),
assuming finite value spaces, finite observational-kernel slices, standard-Borel and nonempty
one-node observed value spaces, and countably generated prefix value spaces, [the recursively
recovered factor](goal) assigns to every observed-data realization the recursive identification
mass for the target divided by its reference atom, and is zero when either named node set is
not observed.

Obs-side recursive recovered factor for a target district.

The seed is the observational mass form of the full containing c-component
factor `Q[C]`: the c-component density factor multiplied by the `C` reference
atom.  The mass-level IDENTIFY recursion then recovers the target mass `Q[S]`,
and the final division converts it back to a density with respect to the `S`
reference atom. -/
@[irreducible] noncomputable def recoveredFactorRec
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (C S : Finset (SWIGNode N))
    [hfin : ∀ n, Fintype (Ω n)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    if hC : C ⊆ M.observed then
      if hSobs : S ⊆ M.observed then
        SCM.identifyMassRec M.observed M.toSWIGGraph C S hC
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
              M.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) x /
          jointRef ref S
            ({valuesProjection hSobs x} : Set (ValuesOn S (swigΩ Ω)))
      else 0
    else 0

/-- Equal observational kernels transport the recursive recovered factor. -/
lemma recoveredFactorRec_heq_of_obsKernel_heq
    (M₁ M₂ : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (C S : Finset (SWIGNode N))
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hobs : HEq M₁.obsKernel M₂.obsKernel)
    [hfin : ∀ n, Fintype (Ω n)]
    [∀ s' : M₁.FixedValues, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      Nonempty
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₁.FixedValues (ValuesOn (M₁.prefixNodes k) (swigΩ Ω))]
    [∀ s' : M₂.FixedValues, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      Nonempty
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₂.FixedValues (ValuesOn (M₂.prefixNodes k) (swigΩ Ω))] :
    HEq (fun s => recoveredFactorRec M₁ ref s C S)
      (fun s => recoveredFactorRec M₂ ref s C S) := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hfio : fio₂ = fio₁ := Subsingleton.elim _ _
  subst fio₂
  have hoi : oi₂ = oi₁ := Subsingleton.elim _ _
  subst oi₂
  have hod : od₂ = od₁ := Subsingleton.elim _ _
  subst od₂
  have hoou : oou₂ = oou₁ := Subsingleton.elim _ _
  subst oou₂
  have hfoi : foi₂ = foi₁ := Subsingleton.elim _ _
  subst foi₂
  have hfou : fou₂ = fou₁ := Subsingleton.elim _ _
  subst fou₂
  have haic : aic₂ = aic₁ := Subsingleton.elim _ _
  subst aic₂
  have hdc : dc₂ = dc₁ := Subsingleton.elim _ _
  subst dc₂
  have hfoff : foff₂ = foff₁ := Subsingleton.elim _ _
  subst foff₂
  have haco : aco₂ = aco₁ := Subsingleton.elim _ _
  subst aco₂
  let M₁' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁,
      unobserved := unobserved₁, fixed_is_fixed := fio₁,
      observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁,
      unobs_are_roots := dc₁, fixed_outside_fixed_isolated := foff₁,
      all_children_in_observed := aco₁, edgeTypes := eT₁,
      iota_valueSpace := iota₁, structFun := sf₁,
      structFun_measurable := mf₁, latentDist := lD₁,
      isProbability_latent := pL₁ }
  let M₂' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁,
      unobserved := unobserved₁, fixed_is_fixed := fio₁,
      observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁,
      unobs_are_roots := dc₁, fixed_outside_fixed_isolated := foff₁,
      all_children_in_observed := aco₁, edgeTypes := eT₂,
      iota_valueSpace := iota₂, structFun := sf₂,
      structFun_measurable := mf₂, latentDist := lD₂,
      isProbability_latent := pL₂ }
  have hk : _ = _ := eq_of_heq hobs
  apply heq_of_eq
  funext s x
  unfold recoveredFactorRec
  by_cases hC : C ⊆ observed₁
  · by_cases hSobs : S ⊆ observed₁
    · rw [dif_pos hC, dif_pos hSobs, dif_pos hC, dif_pos hSobs]
      change
        SCM.identifyMassRec M₁'.observed M₁'.toSWIGGraph C S hC _ x / _ =
          SCM.identifyMassRec M₂'.observed M₂'.toSWIGGraph C S hC _ x / _
      rw [← identifyMassRecObserved_eq_identifyMassRec M₁' M₁'.toSWIGGraph C S hC]
      rw [← identifyMassRecObserved_eq_identifyMassRec M₂' M₂'.toSWIGGraph C S hC]
      have hseed :
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin observed₁.card =>
                  (M₁'.observedAt i).val ∈ C),
              M₁'.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) =
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin observed₁.card =>
                  (M₂'.observedAt i).val ∈ C),
              M₂'.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) := by
        funext x'
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        unfold obsStepCondDensity obsStepCondKernel SCM.obsCondKernel SCM.obsCondPairKernel
        repeat' congr
      rw [hseed]
    · rw [dif_pos hC, dif_neg hSobs, dif_pos hC, dif_neg hSobs]
  · rw [dif_neg hC, dif_neg hC]

/-- **Recursive district-density recovery from the observational kernel.** Fix [a standard
structural causal model `M`](hyp:hStd) and an intervention target set `X` for which [every
targeted node is currently a random observed node](hyp:hObs) and [none of its fixed copies is
already fixed](hyp:hFix), an output set `Y`, and [a reference-measure family faithful to the
graph](hyp:href). For [a district `S` of the truncated c-component set of the post-intervention
ancestral graph](hyp:hS) and [a c-component `C` of the base graph that is recursively
factor-reachable from `S`](hyp:hReach,hCmem), assume [every fixed-value assignment gives an
observational kernel with everywhere-positive point masses](hyp:hpos), [no intervention
target's random form lies in `Y`](hyp:hYX), and that [an extension map from ancestral
assignments to full observed assignments restricts back to the identity](hyp:hExtend) and
[agrees with the intervention values `sDo` on the targeted coordinates](hyp:hExtendX). Then
[the district factor of `S` computed from the density of the do-law's ancestral marginal
equals, almost everywhere, the full-graph c-component density factor of `C` evaluated at the
extension of the ancestral assignment](goal).

This is the density-level IDENTIFY step needed to replace the no-fixing
`doAncestralDistrictDensity_recovered_from_obs` recovery. -/
theorem doAncestralDistrictDensity_recovered_from_obs_rec
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
    (S C : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hReach : CFactorReachableRec M.toSWIGGraph C S)
    (hCmem : C ∈ M.toSWIGGraph.cComponentSet)
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
          recoveredFactorRec M ref
            (M.fixSetProj X hObs hFix sDo) C S (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let sObs := M.fixSetProj X hObs hFix sDo
  have hCobs : C ⊆ M.observed := by
    simpa using M.toSWIGGraph.cComponentSet_subset_observed C hCmem
  have hSobs : S ⊆ M.observed := fun _ hv => hCobs (hReach.target_subset hv)
  have hSD : S ⊆ D := by
    have hScomp : S ∈ H.cComponentSet := by
      change S ∈
        ((M.fixSet X hObs hFix).toSWIGGraph.induce
          (fixAncestralSet M X hObs hFix Y)).cComponentSet
      simpa [fixTruncCComponentSet] using hS
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    -- `H.observed` is `fixAncestralSet … ∩ MX.observed` only after delta-unfolding
    -- `SWIGGraph.induce`, whose body is `let`-structured: simp will not do it, and
    -- the folded/unfolded pair is defeq only at default transparency.
    exact hSHobs
  have hSX : ∀ n ∈ X, SWIGNode.random n ∉ S := by
    intro n hn hnS
    have hnD : SWIGNode.random n ∈ D := hSD hnS
    have hnA : SWIGNode.random n ∈ fixAncestralSet M X hObs hFix Y := by
      simpa [D, fixObservedAncestralSet] using (Finset.mem_inter.mp hnD).1
    exact hYX n hn
      ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hn).mp hnA)
  filter_upwards with xD
  have hproj :
      valuesProjection hSobs (extend xD) =
        valuesProjection hSD xD := by
    ext v
    have h := congrFun (hExtend xD) ⟨v.val, hSD v.property⟩
    simpa [valuesProjection] using h
  have hdo :
      MX.qLocalMass sDo S (by simpa [MX, SCM.fixSet_observed] using hSobs)
          (extend xD) =
        M.qLocalMass sObs S hSobs (extend xD) := by
    simpa [MX, sObs] using
      qLocalMass_fixSet_invariant M X hObs hFix sDo S hSobs hSX
        (extend xD) (fun D hD => hExtendX xD D hD)
  have hseed :
      (fun x' =>
        (∏ i ∈ Finset.univ.filter
            (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
          M.obsStepCondDensity ref sObs i x') *
        jointRef ref C
          ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω)))) =
        M.qLocalMass sObs C hCobs := by
    funext x'
    have hprod :
        (∏ i ∈ Finset.univ.filter
            (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
          M.obsStepCondDensity ref sObs i x') =
          M.cComponentDensityFactor ref sObs C x' := by
      unfold cComponentDensityFactor
      refine Finset.prod_congr ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (M.observedAt i).property hCmem)
      · intro i _hi
        rfl
    let atom :=
      jointRef ref C ({valuesProjection hCobs x'} :
        Set (ValuesOn C (swigΩ Ω)))
    have hatom0 : atom ≠ 0 := by
      exact jointRef_singleton_ne_zero ref href C (valuesProjection hCobs x')
    have hatomtop : atom ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref C)
        ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω))))
    have hmech :
        M.mechCFactor ref C hCobs sObs x' =
          M.qLocalMass sObs C hCobs x' / atom := by
      simpa [atom] using
        mechCFactor_eq_qLocalMass_div_jointRef M ref sObs C hCobs href
          (standard_fixed_random_edgeless M hStd) x'
    calc
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
        M.obsStepCondDensity ref sObs i x') *
          jointRef ref C
            ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω)))
          = M.cComponentDensityFactor ref sObs C x' * atom := by
              rw [hprod]
      _ = M.mechCFactor ref C hCobs sObs x' * atom := by
              rw [cComponentDensityFactor_eq_mechCFactor
                M ref sObs hStd C hCobs hCmem href (hpos sObs) x']
      _ = (M.qLocalMass sObs C hCobs x' / atom) * atom := by
              rw [hmech]
      _ = M.qLocalMass sObs C hCobs x' := by
              exact ENNReal.div_mul_cancel hatom0 hatomtop
  have hidentify :
      SCM.identifyMassRec M.observed M.toSWIGGraph C S hCobs
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
              M.obsStepCondDensity ref sObs i x') *
            jointRef ref C
              ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω))))
          (extend xD) =
        M.qLocalMass sObs S hSobs (extend xD) := by
    rw [hseed]
    exact identifyMassRec_qLocalMass M sObs (hpos sObs) C S hCobs hReach (extend xD)
  have hkey :=
    tianDistrictDensity_eq_qLocalMass_div_jointRef_district
      M X hObs hFix Y ref href sDo hpos hYX S hS extend hExtend xD
  calc
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
        =
      MX.qLocalMass sDo S
          (show S ⊆ MX.observed from by
            simpa [MX, SCM.fixSet_observed] using hSobs)
          (extend xD) /
        jointRef ref S
          ({valuesProjection hSD xD} : Set (ValuesOn S (swigΩ Ω))) := by
          simpa [H, D, MX] using hkey
    _ =
      M.qLocalMass sObs S hSobs (extend xD) /
        jointRef ref S
          ({valuesProjection hSD xD} : Set (ValuesOn S (swigΩ Ω))) := by
          rw [hdo]
    _ =
      M.qLocalMass sObs S hSobs (extend xD) /
        jointRef ref S
          ({valuesProjection hSobs (extend xD)} : Set (ValuesOn S (swigΩ Ω))) := by
          rw [hproj]
    _ =
      recoveredFactorRec M ref sObs C S (extend xD) := by
          unfold recoveredFactorRec
          rw [dif_pos hCobs, dif_pos hSobs, hidentify]


end Causalean.SCM.ID

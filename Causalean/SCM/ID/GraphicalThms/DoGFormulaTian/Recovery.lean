/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Graph.DSep.InduceTransport
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Factored.ObsChainKernel
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.QFactor
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.ID.GraphicalThms.DoGFormulaTian.ChainRule
public import Causalean.SCM.ID.GraphicalThms.NonAncestorKernelTransport

/-! # SCM recovery for the Tian do-law density formula

This file proves the global-Markov property of the post-intervention ancestral
marginal, recovers each eligible district density from the observational model,
and assembles the resulting Tian c-factorization used by discrete ID
soundness.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- The do-law ancestral marginal is globally Markov with respect to the pure
ancestral graph `G_X[D]`.  This is the SCM-to-measure bridge for T1; it does
not assert that `D` is an ancestrally closed SCM support. -/
theorem doObsKernelAncestralMarginal_globalMarkovOn
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    [StandardBorelSpace (M.fixSet X hObs hFix).RandomValues]
    [StandardBorelSpace (M.fixSet X hObs hFix).ObservedValues]
    [∀ s : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).jointKernel s)]
    [∀ s : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).obsKernel s)]
    (s : (M.fixSet X hObs hFix).FixedValues)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y s)] :
    let A := fixAncestralSet M X hObs hFix Y
      let D := fixObservedAncestralSet M X hObs hFix Y
      let H := (M.fixSet X hObs hFix).toSWIGGraph.induce A
      KernelGlobalMarkovOn H D
        (doObsKernelAncestralMarginal M X hObs hFix Y s) := by
  classical
  let M' := M.fixSet X hObs hFix
  let A := fixAncestralSet M X hObs hFix Y
  let D := fixObservedAncestralSet M X hObs hFix Y
  change KernelGlobalMarkovOn (M'.toSWIGGraph.induce A) D
    ((doObsKernelAncestralMarginal M X hObs hFix Y) s)
  dsimp [KernelGlobalMarkovOn]
  intro X' Y' Z' hX hY hZ hXY hXZ hYZ hdSep
  have hD_obs : D ⊆ M'.observed := by
    intro v hv
    exact (Finset.mem_inter.mp hv).2
  have hX_obs : X' ⊆ M'.observed := fun v hv => hD_obs (hX hv)
  have hY_obs : Y' ⊆ M'.observed := fun v hv => hD_obs (hY hv)
  have hZ_obs : Z' ⊆ M'.observed := fun v hv => hD_obs (hZ hv)
  have hA_closed : M'.dag.ancestralSet A = A := by
    simpa [A, fixAncestralSet, M'] using
      (M'.dag.ancestralSet_idem Y)
  have hdSep_fixed : M'.dag.dSep X' Y' (Z' ∪ M'.fixed) := by
    simpa [A, D, M'] using
      (M'.toSWIGGraph.dSep_union_fixed_of_induce_dSep A X' Y' Z'
        hX hY hZ (by simp [hA_closed]) hdSep)
  have hCI_obs : SCM.ObsCondIndep M' X' Y' Z' hX_obs hY_obs hZ_obs
      (M'.obsKernel s) :=
    SCM.globalMarkov_with_fixed M' X' Y' Z' M'.fixed
      hX_obs hY_obs hZ_obs (by intro v hv; exact hv)
      hdSep_fixed s
  unfold KernelObsCondIndepOn
  unfold SCM.ObsCondIndep at hCI_obs
  have hCI_pre :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap
          (valuesProjection hZ ∘ valuesProjection hD_obs) inferInstance)
        (Measurable.comap_le
          ((measurable_valuesProjection hZ).comp
            (measurable_valuesProjection hD_obs)))
        (valuesProjection hX ∘ valuesProjection hD_obs)
        (valuesProjection hY ∘ valuesProjection hD_obs)
        (M'.obsKernel s) := by
    convert hCI_obs using 2 <;> rfl
  have hCI_map :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
        (comap_valuesProjection_le hZ)
        (valuesProjection hX) (valuesProjection hY)
        ((M'.obsKernel s).map (valuesProjection hD_obs)) :=
    condIndepFun_of_map
      (φ := valuesProjection hD_obs)
      (measurable_valuesProjection hD_obs)
      (measurable_valuesProjection hX)
      (measurable_valuesProjection hY)
      (measurable_valuesProjection hZ)
      hCI_pre
  convert hCI_map using 2
  rw [doObsKernelAncestralMarginal,
    ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection hD_obs)]

/-- The graph-level topological enumeration agrees definitionally with the
SCM-level observed-node enumeration. -/
lemma nodesAt_toSWIGGraph_observed_eq_observedAt
    (M : Causalean.SCM N Ω) (i : Fin M.observed.card) :
    M.toSWIGGraph.nodesAt M.observed i = M.observedAt i := by
  rfl

/-- Deprecated compatibility alias for `tian_full_cComponent_density_recovery_core_direct`:
for [a standard structural causal model](hyp:hStd) with [an intervention set whose random copies
are observed and fixed copies are not already frozen](hyp:hObs,hFix), under [faithful reference
measures](hyp:href) and [positive observational kernels](hyp:hpos), for [outcomes disjoint from
the intervened random copies](hyp:hYX), [a post-intervention ancestral district that is also a
full observational c-component](hyp:hS,hSfull), and [an extension respecting ancestral
coordinates and intervention values](hyp:hExtend,hExtendX), [the do-law Tian district density
agrees almost everywhere with the extended observational c-component density](goal). -/
@[deprecated tian_full_cComponent_density_recovery_core_direct (since := "2026-09-15")]
alias tian_full_cComponent_density_recovery_core := tian_full_cComponent_density_recovery_core_direct

/-- Finite same-district recovery: the do-law's `S`-district density factor equals
`S`'s observational c-component density factor (after extension), for a district `S`
that is already a full observational c-component.

This is Tian's identification at the DISTRICT level.  Both sides collapse to the
c-factor `Q[S]`: `tianDistrictDensity` (the do-law's `D`-prefix conditional product)
to `Q[S]` of the do-model, and `cComponentDensityFactor` (the full-observed-prefix
conditional product) to `Q[S]` of `M`; the two `Q[S]` kernels agree by
the non-ancestor kernel transport results. It is NOT a per-coordinate identity — the D-prefix
and full-observed-prefix conditionals differ node-by-node and only telescope to the
same district product. -/
lemma doAncestralDistrictDensity_recovered_from_obs_core_self
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
  exact tian_full_cComponent_density_recovery_core
    M X hStd hObs hFix Y ref href sDo S hS hSfull hpos hYX extend hExtend hExtendX
/-- T2 density-recovery core.

For one district `S` of the post-intervention ancestral graph, the product of
Tian prefix conditional densities computed from the ancestral do-law marginal
agrees a.e. with the matching full observational c-component density factor,
pulled back along any extension that agrees on the ancestral observed
coordinates.  The proof is the finite atomic bridge from the kernel-level
the non-ancestor kernel transport results to the scalar `rnDeriv` factors,
together with the index bijection between the `D`-topological `S` nodes and the
full observed `C` nodes and extension-independence off `D`. -/
lemma doAncestralDistrictDensity_recovered_from_obs_core
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
    (hReach : cFactorReachable M.toSWIGGraph C S)
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
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) C (extend xD) := by
  classical
  rcases hReach with ⟨hSnonempty, hSsubC, hSmem⟩
  have hCS : C = S := by
    by_contra hne
    rcases hSnonempty with ⟨v, hvS⟩
    have hvC : v ∈ C := hSsubC hvS
    have hdisj := M.toSWIGGraph.cComponentSet_pairwise_disjoint hCmem hSmem hne
    exact (Finset.disjoint_left.mp hdisj) hvC hvS
  subst C
  exact doAncestralDistrictDensity_recovered_from_obs_core_self
    M X hStd hObs hFix Y ref href sDo S hS hSmem hpos hYX extend hExtend hExtendX

/-- **T2, abstract density recovery statement.** Fix [a standard structural causal model
`M`](hyp:hStd) and an intervention target set `X` for which [every targeted node is currently a
random observed node](hyp:hObs) and [none of its fixed copies is already fixed](hyp:hFix), an
output set `Y`, and [a reference-measure family faithful to the graph](hyp:href). For [a district
`S` of the truncated c-component set of the post-intervention ancestral graph](hyp:hS) and [a
c-component `C` of the base graph that is factor-reachable from `S`](hyp:hReach,hCmem), assume
[every fixed-value assignment gives an observational kernel with everywhere-positive point
masses](hyp:hpos), [no intervention target's random form lies in `Y`](hyp:hYX), and that [an
extension map from ancestral assignments to full observed assignments restricts back to the
identity](hyp:hExtend) and [agrees with the intervention values `sDo` on the targeted
coordinates](hyp:hExtendX). Then [the district factor of `S` computed from the density of the
do-law's ancestral marginal equals, almost everywhere, the full-graph c-component density
factor of `C` evaluated at the extension of the ancestral assignment](goal).

The extension parameter makes the statement honest about the type mismatch:
the left side lives on `D = An_{G_X}(Y) ∩ observed`, while the already-proven
full-graph factor `cComponentDensityFactor` lives on the original observed
state.  The right side is extension-independent under the
reachability/no-descendant hypotheses. -/
theorem doAncestralDistrictDensity_recovered_from_obs
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
    (hReach : cFactorReachable M.toSWIGGraph C S)
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
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) C (extend xD) := by
  exact doAncestralDistrictDensity_recovered_from_obs_core
    M X hStd hObs hFix Y ref href sDo S C hS hReach hCmem hpos hYX extend hExtend
      hExtendX

/-- **ID-specific T1 wrapper.** For an intervention target set `X` where [every targeted node is
currently a random observed node with no fixed copy already fixed](hyp:hObs,hFix), if [the
ancestral marginal of the do-law `ν_M = (M.fixSet X).obsKernel.map π_D` is absolutely continuous
with respect to the product reference measure on the ancestral observed set](hyp:hdomD), then
[its Radon–Nikodym density equals, almost everywhere, the product over the c-components of the
induced post-intervention ancestral graph `G_X[D]` of their Tian district-density
factors](goal). -/
theorem doObsKernelAncestralMarginal_tian_cfactorization_density
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (s : (M.fixSet X hObs hFix).FixedValues)
    [StandardBorelSpace
      (ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω))]
    [StandardBorelSpace (M.fixSet X hObs hFix).RandomValues]
    [StandardBorelSpace (M.fixSet X hObs hFix).ObservedValues]
    [∀ s' : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).jointKernel s')]
    [∀ s' : (M.fixSet X hObs hFix).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M.fixSet X hObs hFix).obsKernel s')]
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y s)]
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
    (hdomD :
      doObsKernelAncestralMarginal M X hObs hFix Y s ≪
        Causalean.SCM.jointRef ref (fixObservedAncestralSet M X hObs hFix Y)) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    (doObsKernelAncestralMarginal M X hObs hFix Y s).rnDeriv
        (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun x => ∏ S ∈ H.cComponentSet,
          tianDistrictDensity H D
            (doObsKernelAncestralMarginal M X hObs hFix Y s) ref S x := by
  intro D H
  exact markov_tian_cfactorization_density H D rfl
    (doObsKernelAncestralMarginal M X hObs hFix Y s) ref hdomD


end SCM.ID
end Causalean

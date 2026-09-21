/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Backdoor
public import Causalean.SCM.ID.Adjustment
public import Causalean.SCM.ID.Toolkit.FrontdoorGraph
public import Causalean.SCM.ID.GraphicalThms.NonAncestorKernelTransport
public import Causalean.SCM.Model.EquivKernel
public import Causalean.SCM.Do.ValuesReindex

public import Causalean.SCM.ID.Frontdoor.Interception

/-! # Frontdoor adjustment equality, a.e. in treatment

This file assembles the mediator, outcome, and interception identities into the
frontdoor functional.  It proves both the version-safe compProd equality and
the resulting almost-everywhere equality between `frontdoorAdjustment` and the
post-intervention outcome marginal.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
-- Genuine per-node primitives; all ValuesOn-level `StandardBorelSpace`/`Nonempty` (incl.
-- `M.RandomValues`), every kernel finiteness (`obsKernel`/`jointKernel`/`doKernelY`/
-- `adjustmentKernelY`/`frontdoorKernelY`), and `CountableOrCountablyGenerated` derive from these.
variable [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. The frontdoor-adjustment kernel in the treatment value
-- ============================================================

/-- For [a finite structural causal model with measurable, standard-Borel, nonempty
node-value spaces](hyp:N,Ω,M), [treatment nodes](hyp:X) [whose random copies are observed
and whose fixed copies are not already fixed](hyp:hObs,hFix), [mediator nodes](hyp:Wbase)
[with the same intervention validity conditions](hyp:hWobs,hWfix), [outcome
nodes](hyp:Y), [observability of outcomes](hyp:hY),
[the frontdoor criterion](hyp:hFD), [an original fixed-node
assignment](hyp:s0), and
[the API's three formal support premises](hyp:hPositivityA,hPositivityB,hPositivityFD1),
[the joint law of the
treatment marginal with the post-intervention outcome equals its joint law with the
frontdoor-adjustment functional](goal). The first and third premises are empty-coordinate
self-domination conditions; only the middle premise expresses substantive
treatment–mediator overlap.

    **Frontdoor completeness — joint (compProd), version-safe primary form.**
    `νX ⊗ₘ doKernelY = νX ⊗ₘ frontdoorKernelY` at base `s₀`, under the frontdoor
    criterion and the three formal absolute-continuity premises. This is the frontdoor
    analogue of
    `backdoor_completeness_ae_compProd`.

    Proof plan: combine Leg A (`frontdoor_legA_mediator`) and Leg B
    (`backdoor_completeness_ae_compProd` with treatment `:= W`, adjustment
    `:= X.image .random`, outcome `:= Y`), then reassemble into the
    `frontdoorAdjustment` body.  See the module docstring. -/
theorem frontdoor_completeness_ae_compProd
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hFD : Causalean.SWIGGraph.frontdoorCriterion M.toSWIGGraph
      X hObs hFix Wbase hWobs hWfix Y)
    (s0 : M.FixedValues)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed)
        (by simpa using (Finset.image_subset_iff.mpr hObs)) s0)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        (Finset.image_subset_iff.mpr hObs)
        (Finset.union_subset (Finset.image_subset_iff.mpr hWobs)
          (Finset.image_subset_iff.mpr hObs)) s0)
    (hPositivityFD1 : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      ((((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [SCM.fixSet_observed] using
              (Finset.image_subset_iff.mpr hWobs))) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel s).map
              (valuesProjection (Finset.empty_subset _)))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ (((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (I := (M.fixSet X hObs hFix).observed)
            (J := Wbase.image SWIGNode.random ∪ ∅)
            (Ω := swigΩ Ω)
            (by simpa [Finset.union_empty, SCM.fixSet_observed] using
              (Finset.image_subset_iff.mpr hWobs))))) :
    (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
        (M.doKernelY X hObs hFix Y hY s0)
      = (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
          (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY
            (Finset.image_subset_iff.mpr hWobs) s0) := by
  exact frontdoor_fd1_interception_compProd M X hObs hFix Wbase hWobs hWfix Y hY
    hFD s0 hPositivityA hPositivityB hPositivityFD1

/-- For [a finite structural causal model with measurable, standard-Borel, nonempty
node-value spaces](hyp:N,Ω,M), [treatment nodes](hyp:X) [whose random copies are observed
and whose fixed copies are not already fixed](hyp:hObs,hFix), [mediator nodes](hyp:Wbase)
[with the same intervention validity conditions](hyp:hWobs,hWfix), [outcome
nodes](hyp:Y), [observability of outcomes](hyp:hY),
[the frontdoor criterion](hyp:hFD), [an original fixed-node
assignment](hyp:s0), and
[the API's three formal support premises](hyp:hPositivityA,hPositivityB,hPositivityFD1),
[for almost every treatment value, the post-intervention outcome law equals the
frontdoor-adjustment functional](goal). The first and third premises are empty-coordinate
self-domination conditions; only the middle premise expresses substantive
treatment–mediator overlap.

    **Frontdoor adjustment equality, a.e. in the treatment value.** This within-model
    identity follows from `frontdoor_completeness_ae_compProd` by
    `ae_eq_of_compProd_eq`. -/
theorem frontdoor_adjustment_ae
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hFD : Causalean.SWIGGraph.frontdoorCriterion M.toSWIGGraph
      X hObs hFix Wbase hWobs hWfix Y)
    (s0 : M.FixedValues)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed)
        (by simpa using (Finset.image_subset_iff.mpr hObs)) s0)
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        (Finset.image_subset_iff.mpr hObs)
        (Finset.union_subset (Finset.image_subset_iff.mpr hWobs)
          (Finset.image_subset_iff.mpr hObs)) s0)
    (hPositivityFD1 : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      ((((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (by simpa [SCM.fixSet_observed] using
              (Finset.image_subset_iff.mpr hWobs))) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel s).map
              (valuesProjection (Finset.empty_subset _)))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ (((M.fixSet X hObs hFix).obsKernel s).map
          (valuesProjection
            (I := (M.fixSet X hObs hFix).observed)
            (J := Wbase.image SWIGNode.random ∪ ∅)
            (Ω := swigΩ Ω)
            (by simpa [Finset.union_empty, SCM.fixSet_observed] using
              (Finset.image_subset_iff.mpr hWobs))))) :
    ∀ᵐ t ∂(M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0),
      M.doKernelY X hObs hFix Y hY s0 t
        = M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY
            (Finset.image_subset_iff.mpr hWobs) s0 t := by
  have hWr : Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hWobs
  have hXr : X.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hObs
  have hXrW : X.image SWIGNode.random ∪ Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.union_subset hXr hWr
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal X hXr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  exact ProbabilityTheory.Kernel.ae_eq_of_compProd_eq
    (M.frontdoor_completeness_ae_compProd X hObs hFix Wbase hWobs hWfix Y hY
      hFD s0 hPositivityA hPositivityB hPositivityFD1)


end SCM

end Causalean

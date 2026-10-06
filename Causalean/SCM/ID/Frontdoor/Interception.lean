/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.SCM.Do.ValuesReindex
public import Causalean.SCM.ID.Adjustment
public import Causalean.SCM.ID.Backdoor
public import Causalean.SCM.ID.GraphicalThms.NonAncestorKernelTransport
public import Causalean.SCM.ID.Toolkit.FrontdoorGraph
public import Causalean.SCM.Model.EquivKernel

public import Causalean.SCM.ID.Frontdoor.Setup

/-! # The interception bridge for frontdoor adjustment

This file proves the compProd identity contributed by the frontdoor
interception clause.  It connects the double-intervention outcome kernel to the
single-intervention kernel and is the FD1 bridge consumed by the final
frontdoor assembly.
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

/-- For [a finite structural causal model with measurable node-value spaces](hyp:N,Ω,M),
[treatment nodes](hyp:X), [observability of their random copies](hyp:hObs), [absence of their
fixed copies from the original fixed set](hyp:hFix), [mediator nodes](hyp:Wbase), [observability
of their random copies](hyp:hWobs), [absence of their fixed copies from the original fixed
set](hyp:hWfix), [outcome nodes](hyp:Y), [observability of outcomes](hyp:hY),
[the frontdoor criterion](hyp:hFD), [an original fixed-node
assignment](hyp:s0), and
[the API's three formal support premises](hyp:hPositivityA,hPositivityB,hPositivityFD1), [the
treatment-indexed causal outcome law equals the treatment-indexed frontdoor adjustment
law](goal). The first and third premises are empty-coordinate self-domination conditions;
only the middle premise expresses substantive treatment–mediator overlap. -/
theorem frontdoor_fd1_interception_compProd
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
              (Finset.image_subset_iff.mpr hWobs)))))
    :
    (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
        (M.doKernelY X hObs hFix Y hY s0)
      = (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
          (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY
            (Finset.image_subset_iff.mpr hWobs) s0) := by
  have hWr : Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hWobs
  have hXr : X.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hObs
  have hDisj_WrXr :
      Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random) :=
    hFD.2.2.2.1
  have hDisj_YWr : Disjoint Y (Wbase.image SWIGNode.random) :=
    hFD.2.2.2.2.symm
  have hXrW : X.image SWIGNode.random ∪ Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.union_subset hXr hWr
  have hLegA := frontdoor_legA_mediator M X hObs hFix Wbase hWobs hWfix Y
    hFD s0 hPositivityA
  have hLegB := frontdoor_legB_outcome M X hObs hFix Wbase hWobs hWfix Y hY
    hFD s0 hPositivityB
  have hG1 :=
    frontdoor_fd3_rule2_dSep M X Wbase hObs hFix hWobs hWfix Y hY hFD.2.2.1
      hDisj_WrXr
  have hG2 :=
    frontdoor_fd1_rule3_nonDesc M X Wbase hObs hFix hWobs hWfix Y hFD.1 hDisj_WrXr
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal X hXr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal Wbase hWr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0) := by
    rw [SCM.doKernelY]; infer_instance
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY Wbase hWobs hWfix Y hY s0) := by
    rw [SCM.doKernelY]; infer_instance
  have hLegA_ae :
      (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0)
        =ᵐ[M.treatmentMarginal X hXr s0]
      (M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
        (∅ : Finset (SWIGNode N)) hWr (Finset.empty_subset M.observed) s0) :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hLegA
  have hLegB_ae :
      (M.doKernelY Wbase hWobs hWfix Y hY s0)
        =ᵐ[M.treatmentMarginal Wbase hWr s0]
      (M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random) hY hXr s0) :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hLegB
  -- Package the FD1 transport lemma.  The finite-kernel obstruction is handled
  -- by `hLegA_ae`/`hLegB_ae` above; the remaining step is to turn `hG1` into
  -- the per-treatment Rule-2 conditional equality for
  -- `(M.fixSet X).fixSet Wbase` with empty conditioning, then transport that
  -- double intervention to the `do(Wbase)` orientation consumed by `hG2`/Rule 3.
  -- This uses the FD1 positivity hypothesis; the remaining ingredient is a
  -- reusable structural kernel-transport lemma across the two intervention orders.
  have hWobsX : ∀ D ∈ Wbase, SWIGNode.random D ∈ (M.fixSet X hObs hFix).observed := by
    intro D hD
    simpa [SCM.fixSet_observed] using hWobs D hD
  have hDisjBaseXW : Disjoint X Wbase :=
    (disjoint_base_of_disjoint_random_image X Wbase hDisj_WrXr).symm
  have hWfixX : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ (M.fixSet X hObs hFix).fixed :=
    Causalean.SCM.fixSet_fixed_not_mem_of_disjoint M Wbase X hObs hFix hWfix hDisjBaseXW
  have hWrX : Wbase.image SWIGNode.random ⊆ (M.fixSet X hObs hFix).observed := by
    simpa [SCM.fixSet_observed] using hWr
  have hWrEmptyX :
      Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)) ⊆
        (M.fixSet X hObs hFix).observed := by
    simpa [Finset.union_empty] using hWrX
  have hYpost : Y ⊆ (M.fixSet X hObs hFix).observed := by
    simpa [SCM.fixSet_observed] using hY
  have hR2FD1 (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
      ∀ᵐ p ∂(((M.fixSet X hObs hFix).obsKernel
          (M.fixSetExtend X hObs hFix s0 t)).map
            (valuesProjection hWrX) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            (((M.fixSet X hObs hFix).obsKernel
              (M.fixSetExtend X hObs hFix s0 t)).map
              (valuesProjection (Finset.empty_subset _)))),
        ((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
            (∅ : Finset (SWIGNode N))
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              (Finset.empty_subset (M.fixSet X hObs hFix).observed))
            ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
              (M.fixSetExtend X hObs hFix s0 t) p.1, p.2)
          =
        (M.fixSet X hObs hFix).obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
            hYpost hWrEmptyX
            (M.fixSetExtend X hObs hFix s0 t, valuesUnionMk p.1 p.2) := by
    exact SCM.do_rule2_kernel_of_nondescendant_product_ae
      (M.fixSet X hObs hFix) Wbase hWobsX hWfixX
      Y (∅ : Finset (SWIGNode N)) hYpost (Finset.empty_subset _)
      hWrX hWrEmptyX
      (by simpa [hWobsX, hWfixX] using hG1)
      (by intro z hz v hv; simpa using hv)
      (by intro z hz v hv; simpa using hv)
      (M.fixSetExtend X hObs hFix s0 t)
      (by
        simpa [hWrX, hWrEmptyX] using
          hPositivityFD1 (M.fixSetExtend X hObs hFix s0 t))
  -- Reduce the joint (compProd) equality to a per-treatment a.e. kernel equality.
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY X hObs hFix Y hY s0) := by
    rw [SCM.doKernelY]; infer_instance
  haveI : ProbabilityTheory.IsSFiniteKernel
      (M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0) := by
    rw [SCM.frontdoorKernelY, SCM.frontdoorAdjustment]; infer_instance
  set sT := fun t => M.fixSetExtend X hObs hFix s0 t with hsT
  set κ := M.doKernelY X hObs hFix (Wbase.image SWIGNode.random) hWr s0 with hκ_def
  set condDoX :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.fixSet X hObs hFix).obsCondKernel Y (Wbase.image SWIGNode.random) hYpost hWrX
      with hcondDoX_def
  have hP1 : ∀ t,
      M.doKernelY X hObs hFix Y hY s0 t
        = condDoX.sectR (sT t) ∘ₘ κ t := by
    -- Now a direct application of the treatment-indexed chain rule.
    intro t
    rw [hsT, hcondDoX_def, hκ_def]
    exact SCM.doKernelY_disintegrate M X hObs hFix Y (Wbase.image SWIGNode.random)
      hY hWr s0 t
  let xDo : (M.fixSet X hObs hFix).FixedValues →
      ValuesOn (X.image SWIGNode.random) (swigΩ Ω) :=
    fun s => zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M X hObs hFix) s)
  have hxDo : Measurable xDo :=
    measurable_zFixedAsRandom.comp
      (measurable_valuesProjection (fixSet_image_fixed_subset M X hObs hFix))
  haveI : ProbabilityTheory.IsMarkovKernel
      (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr) := by
    unfold SCM.obsCondKernel
    infer_instance
  let zCondXdo :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) :=
    (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr).comap
      (fun s => (M.fixSetProj X hObs hFix s, xDo s))
      (Measurable.prodMk (M.measurable_fixSetProj X hObs hFix) hxDo)
  haveI : ProbabilityTheory.IsSFiniteKernel zCondXdo := by
    dsimp [zCondXdo]
    infer_instance
  let xMarginal :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
    (M.obsKernel.map (valuesProjection hXr)).comap
      (M.fixSetProj X hObs hFix)
      (M.measurable_fixSetProj X hObs hFix)
  let yCondXZ :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (X.image SWIGNode.random) (swigΩ Ω) ×
            ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.obsCondKernel Y (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random)
        hY hXrW).comap
      (fun p =>
        (M.fixSetProj X hObs hFix p.1,
         valuesUnionMk p.2.1 p.2.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hObs hFix).comp measurable_fst)
        (measurable_valuesUnionMk.comp
          (Measurable.prodMk
            (measurable_fst.comp measurable_snd)
            (measurable_snd.comp measurable_snd))))
  let innerY :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    ((xMarginal.comap Prod.fst measurable_fst) ⊗ₖ
      (yCondXZ.comap
        (fun q : ((M.fixSet X hObs hFix).FixedValues ×
            ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
            ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
          (q.1.1, q.2, q.1.2))
        (Measurable.prodMk
          (measurable_fst.comp measurable_fst)
          (Measurable.prodMk measurable_snd
            (measurable_snd.comp measurable_fst))))).map Prod.snd
  have hP2 : ∀ t,
      M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 t
        = innerY.sectR (sT t) ∘ₘ zCondXdo (sT t) := by
    intro t
    have hfd :
        M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 t
          = M.frontdoorAdjustment X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr
              (sT t) := by
      rw [SCM.frontdoorKernelY, ProbabilityTheory.Kernel.comap_apply, hsT]
    rw [hfd]
    change (((zCondXdo ⊗ₖ innerY).map Prod.snd) (sT t))
      = innerY.sectR (sT t) ∘ₘ zCondXdo (sT t)
    rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply]
  refine MeasureTheory.Measure.compProd_congr ?_
  have hZc : ∀ a,
      zCondXdo (sT a)
        = M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
            hWr hXr (s0, a) := by
    intro a
    rw [hsT]
    change (M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
        hWr hXr).comap
        (fun s => (M.fixSetProj X hObs hFix s, xDo s))
        (Measurable.prodMk (M.measurable_fixSetProj X hObs hFix) hxDo)
        (M.fixSetExtend X hObs hFix s0 a)
      = M.obsCondKernel (Wbase.image SWIGNode.random) (X.image SWIGNode.random)
          hWr hXr (s0, a)
    rw [ProbabilityTheory.Kernel.comap_apply]
    rw [SCM.fixSetProj_fixSetExtend]
    have hx : xDo (M.fixSetExtend X hObs hFix s0 a) = a := by
      dsimp [xDo]
      exact SCM.zFixedAsRandom_proj_fixSetExtend M X hObs hFix s0 a
    rw [hx]
  have hAdjZ : ∀ a,
      M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
          (∅ : Finset (SWIGNode N)) hWr (Finset.empty_subset M.observed) s0 a
        = zCondXdo (sT a) := by
    intro a
    rw [hZc a]
    exact adjustmentKernelY_empty_eq M X hObs hFix (Wbase.image SWIGNode.random)
      hWr hXr s0 a
  have hQ1 :
      ⇑κ =ᵐ[M.treatmentMarginal X hXr s0] fun a => zCondXdo (sT a) := by
    filter_upwards [hLegA_ae] with a ha
    rw [ha]
    exact hAdjZ a
  have hQ2 :
      ∀ᵐ a ∂M.treatmentMarginal X hXr s0,
        ∀ᵐ z ∂κ a, condDoX (sT a, z) = innerY (sT a, z) := by
    have hFD1Collapse : ∀ a,
        ∀ᵐ z ∂κ a,
          condDoX (sT a, z) = M.doKernelY Wbase hWobs hWfix Y hY s0 z := by
      intro a
      have hκ_a :
          ((M.fixSet X hObs hFix).obsKernel (sT a)).map (valuesProjection hWrX)
            = κ a := by
        rw [hκ_def, SCM.doKernelY,
          ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
          ProbabilityTheory.Kernel.comap_apply, hsT]
      have hprod := MeasureTheory.Measure.ae_ae_of_ae_compProd (hR2FD1 a)
      rw [hκ_a] at hprod
      filter_upwards [hprod] with z hz
      have hzDefault :
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
              (∅ : Finset (SWIGNode N))
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z,
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
            =
            ((M.fixSet X hObs hFix).obsCondKernel Y
              (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
              hYpost hWrEmptyX)
              (M.fixSetExtend X hObs hFix s0 a,
                valuesUnionMk z
                  (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
        have hdir :
            (((M.fixSet X hObs hFix).obsKernel (M.fixSetExtend X hObs hFix s0 a)).map
              (valuesProjection (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              = MeasureTheory.Measure.dirac
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) := by
          exact obsKernel_empty_projection_eq_dirac (M.fixSet X hObs hFix)
            (Finset.empty_subset (M.fixSet X hObs hFix).observed)
            (M.fixSetExtend X hObs hFix s0 a)
            (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
        have hz' : ∀ᵐ e ∂(MeasureTheory.Measure.dirac
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))),
            (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
                (∅ : Finset (SWIGNode N))
                ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
                ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                  (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
                ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                  (M.fixSetExtend X hObs hFix s0 a) z, e)
              =
              ((M.fixSet X hObs hFix).obsCondKernel Y
                (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
                hYpost hWrEmptyX)
                (M.fixSetExtend X hObs hFix s0 a, valuesUnionMk z e) := by
          rw [ProbabilityTheory.Kernel.const_apply] at hz
          rw [hdir] at hz
          exact hz
        simpa [MeasureTheory.ae_dirac_eq, Filter.eventually_pure] using hz'
      -- The remaining rewrites are exactly the empty-conditioning marginal
      -- collapse and intervention-order marginal transport.
      have hXobsW : ∀ D ∈ X, SWIGNode.random D ∈
          (M.fixSet Wbase hWobs hWfix).observed := by
        intro D hD
        simpa [SCM.fixSet_observed] using hObs D hD
      have hXfixW : ∀ D ∈ X, SWIGNode.fixed D ∉
          (M.fixSet Wbase hWobs hWfix).fixed :=
        Causalean.SCM.fixSet_fixed_not_mem_of_disjoint M X Wbase hWobs hWfix hFix
          hDisjBaseXW.symm
      have hG2' : ∀ d ∈ X, ∀ v ∈ Y,
          ¬ ((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).dag.isAncestor
            (SWIGNode.fixed d) v := by
        intro d hd v hv
        exact hG2 v (by simpa using hv) d hd
      have hLhsMarg :
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
              (∅ : Finset (SWIGNode N))
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                hYpost)
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z,
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
            =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z)).map
            (valuesProjection
              ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
                hYpost)) := by
        exact obsCondKernel_empty_eq_marginal
          ((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX) Y
          ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸ hYpost)
          ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
            (M.fixSetExtend X hObs hFix s0 a) z)
          (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
      have hDrop := frontdoor_doubledo_dropX_marginal M X hObs hFix Wbase hWobs hWfix
        Y hY hDisjBaseXW hWobsX hWfixX hXobsW hXfixW hG2' s0 a z
      calc
        condDoX (sT a, z)
            =
          ((M.fixSet X hObs hFix).obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hYpost
            hWrEmptyX)
            (M.fixSetExtend X hObs hFix s0 a,
              valuesUnionMk z
                (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
          rw [hcondDoX_def, hsT]
          apply obsCondKernel_congr_cc (M.fixSet X hObs hFix) Y
            (Wbase.image SWIGNode.random)
            (Wbase.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
            (by simp) hYpost hWrX hWrEmptyX
          exact valuesOn_heq_of_coord (by simp) _ _
            (fun v hvW hvU => (valuesUnionMk_apply_left z
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) hvW).symm)
        _ =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsCondKernel Y
            (∅ : Finset (SWIGNode N))
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              hYpost)
            ((SCM.fixSet_observed (M.fixSet X hObs hFix) Wbase hWobsX hWfixX).symm ▸
              (Finset.empty_subset (M.fixSet X hObs hFix).observed)))
            ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
              (M.fixSetExtend X hObs hFix s0 a) z,
              (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := hzDefault.symm
        _ =
          (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
              ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
                (M.fixSetExtend X hObs hFix s0 a) z)).map
            (valuesProjection (by simpa [SCM.fixSet_observed] using hY)) := by
          rw [hLhsMarg]
        _ = M.doKernelY Wbase hWobs hWfix Y hY s0 z := hDrop
    have hκComp : κ ∘ₘ M.treatmentMarginal X hXr s0 = M.treatmentMarginal Wbase hWr s0 := by
      have hChain := SCM.obsKernel_map_eq_obsCondKernel_comp M
        (Wbase.image SWIGNode.random) (X.image SWIGNode.random) hWr hXr s0
      rw [SCM.treatmentMarginal, SCM.treatmentMarginal]
      rw [hChain]
      refine MeasureTheory.Measure.bind_congr_right ?_
      filter_upwards [hQ1] with a ha
      rw [ha]
      rw [hZc a]
      rfl
    have hLegB_pull :
        ∀ᵐ a ∂M.treatmentMarginal X hXr s0,
          ∀ᵐ z ∂κ a,
            M.doKernelY Wbase hWobs hWfix Y hY s0 z
              = M.adjustmentKernelY Wbase hWobs hWfix Y
                  (X.image SWIGNode.random) hY hXr s0 z := by
      have hb :
          ∀ᵐ z ∂κ ∘ₘ M.treatmentMarginal X hXr s0,
            M.doKernelY Wbase hWobs hWfix Y hY s0 z
              = M.adjustmentKernelY Wbase hWobs hWfix Y
                  (X.image SWIGNode.random) hY hXr s0 z := by
        rw [hκComp]
        exact hLegB_ae
      exact MeasureTheory.Measure.ae_ae_of_ae_bind (ProbabilityTheory.Kernel.aemeasurable κ) hb
    have hInner : ∀ a z,
        M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
            hY hXr s0 z = innerY (sT a, z) := by
      intro a z
      let μX : MeasureTheory.Measure (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
        (M.obsKernel s0).map (valuesProjection hXr)
      let sW := M.fixSetExtend Wbase hWobs hWfix s0 z
      have hWrXr :
          Wbase.image SWIGNode.random ∪ X.image SWIGNode.random ⊆ M.observed :=
        Finset.union_subset hWr hXr
      let condPostW :
          ProbabilityTheory.Kernel
            ((M.fixSet Wbase hWobs hWfix).FixedValues ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
            (ValuesOn Y (swigΩ Ω)) :=
        (M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr).comap
          (fun p =>
            (M.fixSetProj Wbase hWobs hWfix p.1,
             M.fillZrW Wbase hWobs hWfix (X.image SWIGNode.random) p.1 p.2))
          (Measurable.prodMk
            ((M.measurable_fixSetProj Wbase hWobs hWfix).comp measurable_fst)
            (M.measurable_fillZrW_prod Wbase hWobs hWfix (X.image SWIGNode.random)))
      let yInner :
          ProbabilityTheory.Kernel
            (((M.fixSet X hObs hFix).FixedValues ×
              ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
            (ValuesOn Y (swigΩ Ω)) :=
        yCondXZ.comap
          (fun q : ((M.fixSet X hObs hFix).FixedValues ×
              ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) ×
              ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
            (q.1.1, q.2, q.1.2))
          (Measurable.prodMk
            (measurable_fst.comp measurable_fst)
            (Measurable.prodMk measurable_snd
              (measurable_snd.comp measurable_fst)))
      haveI : ProbabilityTheory.IsMarkovKernel
          (M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr) := by
        unfold SCM.obsCondKernel
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel
          (M.obsCondKernel Y
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random) hY hXrW) := by
        unfold SCM.obsCondKernel
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel yCondXZ := by
        dsimp [yCondXZ]
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel condPostW := by
        dsimp [condPostW]
        infer_instance
      haveI : ProbabilityTheory.IsMarkovKernel yInner := by
        dsimp [yInner, yCondXZ]
        infer_instance
      haveI : ProbabilityTheory.IsSFiniteKernel condPostW := by
        infer_instance
      haveI : ProbabilityTheory.IsSFiniteKernel yInner := by
        infer_instance
      have hLhs :
          M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
              hY hXr s0 z = condPostW.sectR sW ∘ₘ μX := by
        have hadj :
            M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
                hY hXr s0 z =
              M.backdoorAdjustment Wbase hWobs hWfix Y (X.image SWIGNode.random)
                hY hXr sW := by
          rw [SCM.adjustmentKernelY, ProbabilityTheory.Kernel.comap_apply]
        rw [hadj]
        change ((((M.obsKernel.map (valuesProjection hXr)).comap
                (M.fixSetProj Wbase hWobs hWfix)
                (M.measurable_fixSetProj Wbase hWobs hWfix))
              ⊗ₖ condPostW).map Prod.snd) sW
          = condPostW.sectR sW ∘ₘ μX
        rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply,
          ProbabilityTheory.Kernel.comap_apply,
          ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        simp [sW, μX, SCM.fixSetProj_fixSetExtend]
      have hRhs :
          innerY (sT a, z) = yInner.sectR (sT a, z) ∘ₘ μX := by
        change (((xMarginal.comap Prod.fst measurable_fst) ⊗ₖ yInner).map Prod.snd)
            (sT a, z) = yInner.sectR (sT a, z) ∘ₘ μX
        rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply,
          ProbabilityTheory.Kernel.comap_apply]
        have hx : xMarginal (sT a) = μX := by
          rw [hsT]
          change ((M.obsKernel.map (valuesProjection hXr)).comap
              (M.fixSetProj X hObs hFix)
              (M.measurable_fixSetProj X hObs hFix))
              (M.fixSetExtend X hObs hFix s0 a) = μX
          rw [ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend,
            ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        rw [hx]
      rw [hLhs, hRhs]
      refine MeasureTheory.Measure.comp_congr ?_
      filter_upwards [] with x'
      calc
        condPostW.sectR sW x'
            =
          M.obsCondKernel Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random) hY hWrXr
            (s0, valuesUnionMk z x') := by
          rw [ProbabilityTheory.Kernel.sectR_apply]
          simp [condPostW, sW, ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend, SCM.fillZrW_fixSetExtend]
        _ =
          M.obsCondKernel Y
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random) hY hXrW
            (s0, valuesUnionMk x' z) := by
          exact obsCondKernel_congr_cc M Y
            (Wbase.image SWIGNode.random ∪ X.image SWIGNode.random)
            (X.image SWIGNode.random ∪ Wbase.image SWIGNode.random)
            (Finset.union_comm _ _) hY hWrXr hXrW s0
            (valuesUnionMk z x') (valuesUnionMk x' z)
            (valuesUnionMk_union_comm_heq hDisj_WrXr z x')
        _ = yInner.sectR (sT a, z) x' := by
          rw [ProbabilityTheory.Kernel.sectR_apply, hsT]
          simp [yInner, yCondXZ, ProbabilityTheory.Kernel.comap_apply,
            SCM.fixSetProj_fixSetExtend]
    filter_upwards [hLegB_pull] with a haB
    filter_upwards [hFD1Collapse a, haB] with z hzFD hzB
    calc
      condDoX (sT a, z)
          = M.doKernelY Wbase hWobs hWfix Y hY s0 z := hzFD
      _ = M.adjustmentKernelY Wbase hWobs hWfix Y
            (X.image SWIGNode.random) hY hXr s0 z := hzB
      _ = innerY (sT a, z) := hInner a z
  filter_upwards [hQ1, hQ2] with a ha1 ha2
  calc
    M.doKernelY X hObs hFix Y hY s0 a
        = condDoX.sectR (sT a) ∘ₘ κ a := hP1 a
    _ = innerY.sectR (sT a) ∘ₘ κ a := by
      refine MeasureTheory.Measure.bind_congr_right ?_
      filter_upwards [ha2] with z hz
      rw [ProbabilityTheory.Kernel.sectR_apply, ProbabilityTheory.Kernel.sectR_apply]
      exact hz
    _ = innerY.sectR (sT a) ∘ₘ zCondXdo (sT a) := by
      rw [ha1]
    _ = M.frontdoorKernelY X hObs hFix Y (Wbase.image SWIGNode.random) hY hWr s0 a :=
      (hP2 a).symm


end SCM

end Causalean

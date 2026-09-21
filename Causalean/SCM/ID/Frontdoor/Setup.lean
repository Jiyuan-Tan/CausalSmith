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


/-! # Frontdoor criterion and component identities

This file defines `frontdoorCriterion`, establishes the mediator and outcome
legs used by frontdoor adjustment, and proves the kernel reindexing identities
needed to compose them.  The mediator is represented by a base-node set so it
can be used as an intervention set.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- For [a finite node population](hyp:N), [a SWIG graph](hyp:G), [a treatment-variable set](hyp:X) whose [random copies are observed](hyp:hX_obs) and whose [fixed copies are not already fixed](hyp:hX_fix), [a mediator-variable set](hyp:W) whose [random copies are observed](hyp:hW_obs) and whose [fixed copies are not already fixed](hyp:hW_fix), and [an outcome-node set](hyp:Y), the [frontdoor criterion](goal) holds exactly when [the mediator random copies d-separate the outcomes from the treatment fixed copies after intervening on the treatments](step:1), [the empty set satisfies the back-door criterion for treatment and mediator](step:2), [the treatment random copies satisfy the back-door criterion for mediator and outcome](step:3), and [the mediator random copies are disjoint from both treatment random copies and outcomes](step:4).

    `frontdoorCriterion` says that the base mediator set `W` satisfies Pearl's
    frontdoor criterion for treatment variables `X` and outcome nodes `Y`: the
    mediator random nodes intercept every directed treatment-outcome path, have
    no open back-door path from treatment, permit treatment adjustment for the
    mediator-outcome effect, and are excluded from the treatment and outcome
    sets.

    Writing `Z := W.image SWIGNode.random` for the mediator's random copies, `W`
    satisfies these graph clauses relative to treatment `X` and outcome `Y` if:

    * **(FD1) Interception.**  `Z` intercepts all directed paths from `X` to `Y`:
      in the `splitMono` graph (the do(X) split, where the outgoing edges of each
      `random D`, `D ∈ X`, are carried by the root intervention copy `fixed D`, so
      `random D` is a sink), the mediator set `Z = W.image .random` d-separates `Y`
      from the intervention copies `X.image .fixed`.  Because each `fixed D` is a root
      carrying exactly `D`'s causal outgoing edges, this d-separation says exactly
      that every directed `X → Y` path (the causal effect of intervening on `X`) runs
      through the mediator `Z` — i.e. full mediation / the exclusion restriction.
      (Using `X.image .random` here would be wrong: `random X` is a sink in the split
      graph, so a d-separation against it encodes a back-door condition, not
      interception.)
    * **(FD2) No back-door `X → Z`.**  There is no unblocked back-door path from `X`
      to the mediator, i.e. `∅` is a back-door adjustment set for `(X, Z)`.  Encoded
      as the backdoor criterion of the empty adjustment set:
      `G.backdoorCriterion X hX_obs hX_fix Z ∅`.
    * **(FD3) Back-door `Z → Y` blocked by `X`.**  `X.image .random` is a valid
      back-door adjustment set for the mediator's effect on `Y`:
      `G.backdoorCriterion W hW_obs hW_fix Y (X.image SWIGNode.random)`.
    * **(FD4) Mediator exclusion.**  The mediator random nodes are disjoint from
      both the treatment random nodes and the outcome set. -/
def frontdoorCriterion
    (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hX_fix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (W : Finset N)
    (hW_obs : ∀ D ∈ W, SWIGNode.random D ∈ G.observed)
    (hW_fix : ∀ D ∈ W, SWIGNode.fixed D ∉ G.fixed)
    (Y : Finset (SWIGNode N)) : Prop :=
  -- (FD1) interception: Z = W.random intercepts all directed X → Y paths, i.e. the
  -- intervention copies `X.fixed` (carrying X's causal outgoing edges; `random X` is a
  -- sink) reach `Y` only through `Z`.
  (G.splitMono X hX_obs hX_fix).dag.dSep Y (X.image SWIGNode.fixed)
      (W.image SWIGNode.random) ∧
  -- (FD2) no back-door X → Z (∅ is a backdoor adjustment set for (X, Z)).
  Causalean.SWIGGraph.backdoorCriterion G X hX_obs hX_fix
    (W.image SWIGNode.random) ∅ ∧
  -- (FD3) X.random is a backdoor adjustment set for the mediator effect (W → Y).
  Causalean.SWIGGraph.backdoorCriterion G W hW_obs hW_fix Y
    (X.image SWIGNode.random) ∧
  -- (FD4) mediator exclusions from treatment and outcome nodes.
  Disjoint (W.image SWIGNode.random) (X.image SWIGNode.random) ∧
  Disjoint (W.image SWIGNode.random) Y

end SWIGGraph

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

/-- For [a finite node population](hyp:N) with [measurable, nonempty standard-Borel node-value spaces](hyp:Ω), [a structural causal model](hyp:M), [a treatment-variable set](hyp:X) whose [random copies are observed](hyp:hObs) and whose [fixed copies are not already fixed](hyp:hFix), [an outcome-node set](hyp:Y), [a mediator-node set](hyp:W), [the requirement that every outcome node is observed](hyp:hY), [the requirement that every mediator node is observed](hyp:hW), and [an assignment to the model's original fixed nodes](hyp:s0), the [frontdoor-adjustment conditional law of outcomes indexed by treatment values](goal) is the frontdoor-adjustment law evaluated after extending the fixed-node assignment by that treatment value. It is defined [by reindexing the graph-level frontdoor-adjustment law along this extension](step:1).

    Frontdoor-adjustment `Y`-marginal as a kernel in the treatment value `t`, at base
    `s₀` — the frontdoor analogue of `adjustmentKernelY`.  Reindexes the graph-level
    `frontdoorAdjustment` (with mediator `Z := W.image SWIGNode.random`) along
    `fixSetExtend s₀`, so its input is the treatment value `t` rather than the full
    post-intervention slice. -/
noncomputable def frontdoorKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y W : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hW : W ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.Kernel (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
      (ValuesOn Y (swigΩ Ω)) :=
  (M.frontdoorAdjustment X hObs hFix Y W hY hW).comap
    (M.fixSetExtend X hObs hFix s0) (M.measurable_fixSetExtend X hObs hFix s0)

/-- For [a finite, distinguishable node population with measurable, standard-Borel, nonempty node-value spaces](hyp:N,Ω) and [a structural causal model](hyp:M), [a finite treatment set](hyp:X), [the requirement that every corresponding random treatment node is observed](hyp:hObs), [the requirement that no corresponding fixed treatment node is already fixed](hyp:hFix), [finite observed outcome and mediator-node sets](hyp:Y,W,hY,hW), and [a fixed-node assignment](hyp:s0), the [treatment-indexed frontdoor-adjustment outcome kernel](goal) is finite.

The treatment-indexed frontdoor-adjustment outcome kernel is finite. -/
instance instIsFiniteKernelFrontdoorKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y W : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hW : W ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.IsFiniteKernel (M.frontdoorKernelY X hObs hFix Y W hY hW s0) := by
  rw [SCM.frontdoorKernelY]; infer_instance

-- ============================================================
-- § 2. Completeness, a.e. in treatment (compProd primary form)
-- ============================================================

/-- For [a finite structural causal model with measurable node-value spaces](hyp:N,Ω,M),
[treatment nodes](hyp:X), [observability of their random copies](hyp:hObs), [absence of their
fixed copies from the original fixed set](hyp:hFix), [mediator nodes](hyp:Wbase), [observability
of their random copies](hyp:hWobs), [absence of their fixed copies from the original fixed
set](hyp:hWfix), [outcome nodes](hyp:Y), [the frontdoor criterion](hyp:hFD),
[an original fixed-node assignment](hyp:s0), and [the API's empty-adjustment
absolute-continuity premise](hyp:hPositivityA),
[the mediator law under treatment intervention equals the empty-adjustment back-door
functional in treatment-indexed joint-law form](goal). The premise is an
empty-coordinate self-domination condition.

**Frontdoor Leg A (mediator).**

    The mediator law under `do(X)` agrees, in the version-safe compProd form, with
    the empty-adjustment backdoor functional.  This is `backdoor_completeness_ae_compProd`
    instantiated with outcome `Wbase.image .random` and adjustment set `∅`, using
    the FD2 clause of the frontdoor criterion. -/
theorem frontdoor_legA_mediator
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hFD : Causalean.SWIGGraph.frontdoorCriterion M.toSWIGGraph
      X hObs hFix Wbase hWobs hWfix Y)
    (s0 : M.FixedValues)
    (hPositivityA : M.BackdoorPositivityAE X (∅ : Finset (SWIGNode N))
        (Finset.empty_subset M.observed)
        (by simpa using (Finset.image_subset_iff.mpr hObs)) s0) :
    (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
        (M.doKernelY X hObs hFix (Wbase.image SWIGNode.random)
          (Finset.image_subset_iff.mpr hWobs) s0)
      =
    (M.treatmentMarginal X (Finset.image_subset_iff.mpr hObs) s0) ⊗ₘ
        (M.adjustmentKernelY X hObs hFix (Wbase.image SWIGNode.random)
          (∅ : Finset (SWIGNode N)) (Finset.image_subset_iff.mpr hWobs)
          (Finset.empty_subset M.observed) s0) := by
  have hWr : Wbase.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hWobs
  exact M.backdoor_completeness_ae_compProd X hObs hFix
    (Wbase.image SWIGNode.random) (∅ : Finset (SWIGNode N))
    hWr (Finset.empty_subset M.observed) hFD.2.1 s0 hPositivityA

/-- For [a finite structural causal model with measurable node-value spaces](hyp:N,Ω,M),
[treatment nodes](hyp:X), [observability of their random copies](hyp:hObs), [absence of their
fixed copies from the original fixed set](hyp:hFix), [mediator nodes](hyp:Wbase), [observability
of their random copies](hyp:hWobs), [absence of their fixed copies from the original fixed
set](hyp:hWfix), [outcome nodes](hyp:Y), [observability of outcomes](hyp:hY),
[the frontdoor criterion](hyp:hFD), [an original fixed-node
assignment](hyp:s0), and [the corresponding positivity condition](hyp:hPositivityB), [the outcome law under mediator intervention equals
the back-door functional adjusting for observed treatment in mediator-indexed joint-law
form](goal).

**Frontdoor Leg B (outcome).**

    The outcome law under `do(Wbase)` is identified by adjusting for the
    observational treatment variables `X.image .random`.  This is
    `backdoor_completeness_ae_compProd` instantiated with treatment `Wbase`,
    outcome `Y`, and adjustment set `X.image .random`, using FD3. -/
theorem frontdoor_legB_outcome
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
    (hPositivityB : M.BackdoorPositivityAE Wbase (X.image SWIGNode.random)
        (Finset.image_subset_iff.mpr hObs)
        (Finset.union_subset (Finset.image_subset_iff.mpr hWobs)
          (Finset.image_subset_iff.mpr hObs)) s0) :
    (M.treatmentMarginal Wbase (Finset.image_subset_iff.mpr hWobs) s0) ⊗ₘ
      (M.doKernelY Wbase hWobs hWfix Y hY s0)
      =
    (M.treatmentMarginal Wbase (Finset.image_subset_iff.mpr hWobs) s0) ⊗ₘ
        (M.adjustmentKernelY Wbase hWobs hWfix Y (X.image SWIGNode.random)
          hY (Finset.image_subset_iff.mpr hObs) s0) := by
  have hXr : X.image SWIGNode.random ⊆ M.observed :=
    Finset.image_subset_iff.mpr hObs
  exact M.backdoor_completeness_ae_compProd Wbase hWobs hWfix Y (X.image SWIGNode.random)
    hY hXr hFD.2.2.1 s0 hPositivityB

/-- Structurally equivalent structural causal models assign the same observational marginal law
to a shared set of observed variables when their fixed-variable assignments correspond. -/
lemma obsKernel_map_proj_eq_of_equiv
    {M₁ M₂ : Causalean.SCM N Ω} (h : SCM.Equiv M₁ M₂)
    (Y : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hY₂ : Y ⊆ M₂.observed)
    (s₁ : M₁.FixedValues) (s₂ : M₂.FixedValues) (hs : HEq s₁ s₂) :
    (M₁.obsKernel s₁).map (valuesProjection hY₁)
      = (M₂.obsKernel s₂).map (valuesProjection hY₂) := by
  -- Extract the `obsKernel` HEq while `h` still has its `Equiv` type.
  have hok0 : HEq M₁.obsKernel M₂.obsKernel :=
    SCM.Equiv.heq_obsKernel h.1 h.2.2.1 h.2.2.2
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  rcases h.1 with ⟨_hEdge, rfl, rfl, rfl⟩
  -- After unifying `observed`/`fixed`/`unobserved`, the `FixedValues` and
  -- `ObservedValues` types coincide, so the `HEq`s collapse to `Eq`.
  have hs_eq : s₁ = s₂ := eq_of_heq hs
  subst hs_eq
  have hok := eq_of_heq hok0
  rw [hok]

/-- Given [a finite structural causal model, target set, and two conditioning sets](hyp:N,Ω,M,Y,CC₁,CC₂),
if [the conditioning sets are equal](hyp:hCCeq), [all three coordinate sets are observed](hyp:hY,hCC₁,hCC₂),
and [two conditioning assignments are equal after type transport](hyp:s,c₁,c₂,hc), then [the resulting
observational conditional measures are equal](goal). -/
lemma obsCondKernel_congr_cc
    (M : Causalean.SCM N Ω) (Y CC₁ CC₂ : Finset (SWIGNode N))
    (hCCeq : CC₁ = CC₂)
    (hY : Y ⊆ M.observed) (hCC₁ : CC₁ ⊆ M.observed) (hCC₂ : CC₂ ⊆ M.observed)
    (s : M.FixedValues) (c₁ : ValuesOn CC₁ (swigΩ Ω)) (c₂ : ValuesOn CC₂ (swigΩ Ω))
    (hc : HEq c₁ c₂) :
    M.obsCondKernel Y CC₁ hY hCC₁ (s, c₁) = M.obsCondKernel Y CC₂ hY hCC₂ (s, c₂) := by
  subst hCCeq
  have hc' : c₁ = c₂ := eq_of_heq hc
  subst hc'
  have hp : hCC₁ = hCC₂ := Subsingleton.elim _ _
  subst hp
  rfl

/-- Given [two disjoint finite coordinate sets](hyp:N,Ω,A,B,hDisj) and [assignments on each](hyp:a,b),
[combining the assignments in either order gives equal values after type transport](goal). -/
lemma valuesUnionMk_union_comm_heq
    {A B : Finset (SWIGNode N)}
    (hDisj : Disjoint A B)
    (a : ValuesOn A (swigΩ Ω)) (b : ValuesOn B (swigΩ Ω)) :
    HEq (valuesUnionMk a b : ValuesOn (A ∪ B) (swigΩ Ω))
      (valuesUnionMk b a : ValuesOn (B ∪ A) (swigΩ Ω)) :=
  -- Now a one-line corollary of the `ValuesReindex` algebra layer.
  valuesUnionMk_comm_heq hDisj a b

/-- With an empty adjustment set, the outcome adjustment kernel equals the observed conditional
kernel of the outcome variables given the treated variables at the same fixed values. -/
lemma adjustmentKernelY_empty_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wr : Finset (SWIGNode N)) (hWr : Wr ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (s0 : M.FixedValues)
    (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    M.adjustmentKernelY X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) s0 t
      = M.obsCondKernel Wr (X.image SWIGNode.random) hWr hXr (s0, t) := by
  let sTt := M.fixSetExtend X hObs hFix s0 t
  let zMarginalPost :
      ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
        (ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) :=
    (M.obsKernel.map (valuesProjection (Finset.empty_subset M.observed))).comap
      (M.fixSetProj X hObs hFix)
      (M.measurable_fixSetProj X hObs hFix)
  haveI : ProbabilityTheory.IsMarkovKernel (M.obsCondKernel Wr
      (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
      (Finset.union_subset hXr (Finset.empty_subset M.observed))) := by
    unfold SCM.obsCondKernel
    infer_instance
  let condPost :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues ×
          ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))
        (ValuesOn Wr (swigΩ Ω)) :=
    (M.obsCondKernel Wr
        (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
        (Finset.union_subset hXr (Finset.empty_subset M.observed))).comap
      (fun p =>
        (M.fixSetProj X hObs hFix p.1,
         M.fillZrW X hObs hFix (∅ : Finset (SWIGNode N)) p.1 p.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hObs hFix).comp measurable_fst)
        (M.measurable_fillZrW_prod X hObs hFix (∅ : Finset (SWIGNode N))))
  haveI : ProbabilityTheory.IsSFiniteKernel zMarginalPost := by
    dsimp [zMarginalPost]
    infer_instance
  haveI : ProbabilityTheory.IsSFiniteKernel condPost := by
    dsimp [condPost]
    infer_instance
  have hcollapse : ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt
      = condPost (sTt, (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
    rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply]
    have hz : zMarginalPost sTt =
        MeasureTheory.Measure.dirac
          (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) := by
      ext S hS
      by_cases hempty : S = ∅
      · simp [hempty]
      · have h_univ : S = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          by_contra hx
          apply hempty
          ext y
          constructor
          · intro hy
            have : y = x := Subsingleton.elim y x
            exact False.elim (hx (this ▸ hy))
          · intro hy
            simp at hy
        rw [h_univ]
        dsimp [zMarginalPost]
        rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
        rw [MeasureTheory.Measure.map_apply (measurable_valuesProjection _) MeasurableSet.univ]
        simp [M.obsKernel_apply_univ (M.fixSetProj X hObs hFix sTt)]
    rw [hz]
    simpa [ProbabilityTheory.Kernel.sectR] using
      (MeasureTheory.Measure.dirac_bind
        (a := (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
        (f := condPost.sectR sTt) (hf := by fun_prop))
  have hadj : M.adjustmentKernelY X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) s0 t
      = ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt := by
    rw [SCM.adjustmentKernelY, ProbabilityTheory.Kernel.comap_apply]
    change M.backdoorAdjustment X hObs hFix Wr (∅ : Finset (SWIGNode N)) hWr
        (Finset.empty_subset _) sTt = ((zMarginalPost ⊗ₖ condPost).map Prod.snd) sTt
    rw [SCM.backdoorAdjustment]
  rw [hadj, hcollapse]
  have hcond : condPost
      (sTt, (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)))
      = M.obsCondKernel Wr
          (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N))) hWr
          (Finset.union_subset hXr (Finset.empty_subset M.observed))
          (s0, valuesUnionMk t
            (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω))) := by
    simp [condPost, sTt, SCM.fixSetProj_fixSetExtend,
      SCM.fillZrW_fixSetExtend]
  rw [hcond]
  apply obsCondKernel_congr_cc M Wr
    (X.image SWIGNode.random ∪ (∅ : Finset (SWIGNode N)))
    (X.image SWIGNode.random)
    (Finset.union_empty _)
    hWr (Finset.union_subset hXr (Finset.empty_subset M.observed)) hXr
  exact valuesOn_heq_of_coord (Finset.union_empty _) _ _
    (fun v hvU hvX => valuesUnionMk_apply_left t
      (default : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) hvX)

/-- Given [a finite structural causal model, disjoint treatment and mediator sets with valid
interventions, and an observed outcome set](hyp:N,Ω,M,X,hObs,hFix,Wbase,hWobs,hWfix,Y,hY,hDisjBaseXW,hWobsX,hWfixX,hXobsW,hXfixW),
if [no fixed treatment copy is an ancestor of an outcome after both interventions](hyp:hG2), then for
[fixed, treatment, and mediator assignments](hyp:s0,t,w), [marginalizing the twice-intervened
observational kernel to the outcome equals the outcome kernel under the mediator intervention](goal). -/
lemma frontdoor_doubledo_dropX_marginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Wbase : Finset N)
    (hWobs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hWfix : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed)
    (hDisjBaseXW : Disjoint X Wbase)
    (hWobsX : ∀ D ∈ Wbase, SWIGNode.random D ∈ (M.fixSet X hObs hFix).observed)
    (hWfixX : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ (M.fixSet X hObs hFix).fixed)
    (hXobsW : ∀ D ∈ X, SWIGNode.random D ∈ (M.fixSet Wbase hWobs hWfix).observed)
    (hXfixW : ∀ D ∈ X, SWIGNode.fixed D ∉ (M.fixSet Wbase hWobs hWfix).fixed)
    (hG2 : ∀ z ∈ X, ∀ v ∈ Y,
      ¬ ((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).dag.isAncestor
        (SWIGNode.fixed z) v)
    (s0 : M.FixedValues)
    (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
    (w : ValuesOn (Wbase.image SWIGNode.random) (swigΩ Ω)) :
    (((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
        ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
          (M.fixSetExtend X hObs hFix s0 t) w)).map
      (valuesProjection (by simpa [SCM.fixSet_observed] using hY))
      = M.doKernelY Wbase hWobs hWfix Y hY s0 w := by
  let M₁ := (M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX
  let M₂ := (M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW
  let s₁ : M₁.FixedValues :=
    (M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
      (M.fixSetExtend X hObs hFix s0 t) w
  let s₃ : M₂.FixedValues :=
    (M.fixSet Wbase hWobs hWfix).fixSetExtend X hXobsW hXfixW
      (M.fixSetExtend Wbase hWobs hWfix s0 w) t
  have hU1o : ∀ D ∈ X ∪ Wbase, SWIGNode.random D ∈ M.observed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hObs D hD
    · exact hWobs D hD
  have hU1f : ∀ D ∈ X ∪ Wbase, SWIGNode.fixed D ∉ M.fixed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hFix D hD
    · exact hWfix D hD
  have hU2o : ∀ D ∈ Wbase ∪ X, SWIGNode.random D ∈ M.observed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hWobs D hD
    · exact hObs D hD
  have hU2f : ∀ D ∈ Wbase ∪ X, SWIGNode.fixed D ∉ M.fixed := by
    intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact hWfix D hD
    · exact hFix D hD
  have e1 : SCM.Equiv M₁ (M.fixSet (X ∪ Wbase) hU1o hU1f) := by
    exact SCM.ID.intervention_target_simp M X Wbase hObs hFix hWobsX hWfixX
      hU1o hU1f hDisjBaseXW
  have e2 : SCM.Equiv M₂ (M.fixSet (Wbase ∪ X) hU2o hU2f) := by
    exact SCM.ID.intervention_target_simp M Wbase X hWobs hWfix hXobsW hXfixW
      hU2o hU2f hDisjBaseXW.symm
  have eb : SCM.Equiv
      (M.fixSet (X ∪ Wbase) hU1o hU1f) (M.fixSet (Wbase ∪ X) hU2o hU2f) := by
    simpa [Finset.union_comm] using
      (SCM.Equiv.refl (M.fixSet (X ∪ Wbase) hU1o hU1f))
  have eswap : SCM.Equiv M₁ M₂ := SCM.Equiv.trans e1 (SCM.Equiv.trans eb e2.symm)
  have hY₁ : Y ⊆ M₁.observed := by
    simpa [M₁, SCM.fixSet_observed] using hY
  have hY₂ : Y ⊆ M₂.observed := by
    simpa [M₂, SCM.fixSet_observed] using hY
  have hs : HEq s₁ s₃ := by
    have hFixed : M₁.fixed = M₂.fixed := by
      dsimp [M₁, M₂]
      simp [Finset.union_comm, Finset.union_left_comm]
    have hDisjXWf : Disjoint (X.image SWIGNode.fixed) (Wbase.image SWIGNode.fixed) := by
      rw [Finset.disjoint_left]
      intro v hvX hvW
      rcases Finset.mem_image.mp hvX with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hvW with ⟨w0, hw0, hEq⟩
      cases hEq
      exact (Finset.disjoint_left.mp hDisjBaseXW) hx hw0
    apply Function.hfunext
    · exact congrArg (fun S : Finset (SWIGNode N) => {i // i ∈ S}) hFixed
    · rintro ⟨v, hv₁⟩ ⟨v', hv₃⟩ hidx
      have hv_eq : v = v' := by
        exact (Subtype.heq_iff_coe_eq (by intro x; rw [hFixed])).mp hidx
      subst hv_eq
      apply heq_of_eq
      have hv₁_full :
          v ∈ (M.fixed ∪ X.image SWIGNode.fixed) ∪ Wbase.image SWIGNode.fixed := by
        simpa [M₁, SCM.fixSet_fixed] using hv₁
      by_cases hM : v ∈ M.fixed
      · simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed, hM]
      · by_cases hXf : v ∈ X.image SWIGNode.fixed
        · have hnotWf : v ∉ Wbase.image SWIGNode.fixed := fun hWf =>
            (Finset.disjoint_left.mp hDisjXWf) hXf hWf
          have hnotMW : v ∉ M.fixed ∪ Wbase.image SWIGNode.fixed := by
            simp [hM, hnotWf]
          have hMX : v ∈ M.fixed ∪ X.image SWIGNode.fixed :=
            Finset.mem_union_right _ hXf
          simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed,
            hM, hnotMW, hMX]
        · have hWf : v ∈ Wbase.image SWIGNode.fixed := by
            rcases Finset.mem_union.mp hv₁_full with hMX | hWf
            · rcases Finset.mem_union.mp hMX with hM' | hXf'
              · exact False.elim (hM hM')
              · exact False.elim (hXf hXf')
            · exact hWf
          have hnotMX : v ∉ M.fixed ∪ X.image SWIGNode.fixed := by
            simp [hM, hXf]
          have hMW : v ∈ M.fixed ∪ Wbase.image SWIGNode.fixed :=
            Finset.mem_union_right _ hWf
          simp [s₁, s₃, M₁, M₂, SCM.fixSetExtend, SCM.fixSet_fixed,
            hM, hnotMX, hMW]
  have hswap := obsKernel_map_proj_eq_of_equiv eswap Y hY₁ hY₂ s₁ s₃ hs
  have hdrop := SCM.condDistrib_intervention_ancestral_eq (M.fixSet Wbase hWobs hWfix)
    X hXobsW hXfixW Y (by simpa [SCM.fixSet_observed] using hY) hG2 s₃
  have hproj :
      (M.fixSet Wbase hWobs hWfix).fixSetProj X hXobsW hXfixW s₃
        = M.fixSetExtend Wbase hWobs hWfix s0 w := by
    dsimp [s₃]
    rw [SCM.fixSetProj_fixSetExtend]
  rw [show ((((M.fixSet X hObs hFix).fixSet Wbase hWobsX hWfixX).obsKernel
        ((M.fixSet X hObs hFix).fixSetExtend Wbase hWobsX hWfixX
          (M.fixSetExtend X hObs hFix s0 t) w)).map
      (valuesProjection (by simpa [SCM.fixSet_observed] using hY))) =
        (M₁.obsKernel s₁).map (valuesProjection hY₁) from rfl]
  rw [hswap]
  rw [show (M₂.obsKernel s₃).map (valuesProjection hY₂) =
      (((M.fixSet Wbase hWobs hWfix).fixSet X hXobsW hXfixW).obsKernel s₃).map
        (valuesProjection
          ((SCM.fixSet_observed (M.fixSet Wbase hWobs hWfix) X hXobsW hXfixW).symm ▸
            (by simpa [SCM.fixSet_observed] using hY))) from rfl]
  rw [hdrop]
  rw [hproj]
  rw [SCM.doKernelY, ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
    ProbabilityTheory.Kernel.comap_apply]


end SCM

end Causalean

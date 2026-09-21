/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DAG
public import Causalean.Graph.SWIG
public import Causalean.Graph.SWIGSplitMono
public import Causalean.SCM.Model.SCM
public import Causalean.SCM.Model.Kernel
public import Causalean.SCM.ID.BackdoorCriterion
public import Causalean.SCM.ID.Toolkit.Derivation

/-! # Real-Valued Backdoor Example

This file gives a real-valued backdoor example in which the confounder,
treatment, and outcome all take values in `ℝ`. The declarations `CBNode`,
`CBΩ`, `cbDAG`, `cbSWIGGraph`, and `continuousBackdoorSCM` build a degenerate
constant structural model whose purpose is to exercise the real-valued graph and
kernel interfaces. The theorem `cb_backdoor_criterion` verifies the graphical
backdoor criterion by computation. The theorem `cb_backdoor_rule2_ae` then
specializes the conditional-kernel Rule-2 equality to this graph once overlap
and positivity are supplied; it does not state the final adjustment formula or
cross-model identification.
-/

@[expose] public section

open Causalean.Graph


set_option linter.style.nativeDecide false

open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM.Examples.ContinuousBackdoor

open Causalean
open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Vertex set and value spaces
-- ============================================================

/-- [The node set of the continuous-backdoor example](goal) consists of three positions
representing, in order, the confounder, treatment, and outcome. -/
abbrev CBNode : Type := Fin 3

/-- [The value-space assignment for the continuous-backdoor example](goal) gives every node the
real-valued state space. -/
abbrev CBΩ : CBNode → Type := fun _ => ℝ

/-- [The confounder node index](goal) is the first of the three node positions in the
continuous-backdoor example. -/
@[reducible] def Zidx : CBNode := 0
/-- [The treatment node index](goal) is the second of the three node positions in the
continuous-backdoor example. -/
@[reducible] def Xidx : CBNode := 1
/-- [The outcome node index](goal) is the third of the three node positions in the
continuous-backdoor example. -/
@[reducible] def Yidx : CBNode := 2

-- ============================================================
-- § 2. Underlying DAG on `CBNode`
-- ============================================================

/-- [The Boolean edge indicator](goal) is true exactly for an arrow from confounder to treatment,
from confounder to outcome, or from treatment to outcome.

It is Boolean-valued so the graphical criterion can be discharged by computation. -/
def cbEdgeBool : CBNode → CBNode → Bool := fun a b =>
  (a.val == 0 && b.val == 1) || (a.val == 0 && b.val == 2) ||
  (a.val == 1 && b.val == 2)

/-- [The edge relation of the continuous-backdoor graph](goal) holds exactly when the Boolean edge
indicator is true, namely for arrows from confounder to treatment or outcome and from treatment to
outcome. -/
def cbEdge : CBNode → CBNode → Prop := fun a b => cbEdgeBool a b = true

/-- For every ordered pair of continuous-backdoor vertices,
[a decision procedure for whether the pair is a directed edge](goal) is provided. -/
instance : DecidableRel cbEdge := by
  intro a b; unfold cbEdge; infer_instance

/-- [The topological-order label of the continuous-backdoor graph](goal) is each node's position,
so it places the confounder before treatment and treatment before outcome. -/
def cbTopo : CBNode → ℕ := fun n => n.val

/-- [Every edge in the continuous-backdoor graph points from an earlier to a later node in the
chosen topological order](goal). -/
theorem cbTopo_lt : ∀ u v, cbEdge u v → cbTopo u < cbTopo v := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [cbEdge, cbEdgeBool, cbTopo]

/-- [The directed acyclic graph of the continuous backdoor example](goal) has the stated three-node
edge relation and topological ordering, and is acyclic. -/
def cbDAG : DAG CBNode where
  edge := cbEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder cbTopo_lt

-- ============================================================
-- § 3. The SWIGGraph (computable, used for `decide` proofs)
-- ============================================================

/-- [The pre-intervention SWIG graph for the continuous-backdoor example](goal) has no fixed or
unobserved nodes and has the confounder, treatment, and outcome as observed random nodes.

It is defined separately from the full structural model so the graphical
backdoor criterion can be checked by computation. -/
def cbSWIGGraph : SWIGGraph CBNode where
  dag := initialSWIG cbDAG
  fixed := ∅
  observed := {SWIGNode.random Zidx, SWIGNode.random Xidx, SWIGNode.random Yidx}
  unobserved := ∅
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by intro u hu; simp at hu
  obs_unobs_disjoint := by
    rw [Finset.disjoint_right]; intro x hx; simp at hx
  dag_edges_classified := by decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by intro u hu; simp at hu
  fixed_outside_fixed_isolated := by
    intro n _
    refine ⟨?_, ?_⟩
    · revert n; decide
    · revert n; decide
  all_children_in_observed := by decide

-- ============================================================
-- § 4. The SCM
-- ============================================================

/-- [The continuous-backdoor structural causal model](goal) has the specified real-valued
pre-intervention graph, no latent variables, nonparametric edges, and constant-zero structural
responses for every observed node.

The structural functions are all constant `0`, so the induced observed law is
degenerate. The model is used as a minimal real-valued witness for the graph and
measurability interfaces, not as a non-degenerate continuous-treatment data
generating process. -/
noncomputable def continuousBackdoorSCM : Causalean.SCM CBNode CBΩ where
  toSWIGGraph := cbSWIGGraph
  edgeTypes := EdgeTypeAssignment.allNonparametric cbSWIGGraph.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := fun v => by
    -- Structural functions: constant 0 for every observed node.  `swigΩ CBΩ v.val`
    -- reduces to `ℝ` for any `.random _` or `.fixed _` (since `CBΩ _ = ℝ`).
    rcases v with ⟨n, _⟩
    cases n <;> exact fun _ => (0 : ℝ)
  structFun_measurable := by
    intro v
    rcases v with ⟨n, _⟩
    cases n <;> exact measurable_const
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

-- ============================================================
-- § 4. Trivial sanity checks
-- ============================================================

/-- The model is in the *standard* regime (no interventions). -/
example : continuousBackdoorSCM.isStandard := rfl

/-- `Z` is a parent of `X` in the base DAG. -/
example : Zidx ∈ cbDAG.parents Xidx := by decide

/-- `Z` is a parent of `Y` in the base DAG. -/
example : Zidx ∈ cbDAG.parents Yidx := by decide

/-- `X` is a parent of `Y` in the base DAG. -/
example : Xidx ∈ cbDAG.parents Yidx := by decide

-- ============================================================
-- § 5. Backdoor criterion for `do(X)` with adjustment set `{Z}`
-- ============================================================

/-- [The treatment's observed random node belongs to the computable continuous-backdoor SWIG
graph](goal).

The witness is stated against the computable graph rather than the full structural
model, whose observed set is definitionally the same. -/
theorem cb_Xrand_obs :
    ∀ D ∈ ({Xidx} : Finset CBNode), SWIGNode.random D ∈ cbSWIGGraph.observed := by
  intro D hD
  rw [Finset.mem_singleton] at hD
  subst hD
  change SWIGNode.random Xidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
  simp

/-- [The treatment's fixed node is not already fixed in the computable continuous-backdoor SWIG
graph](goal). -/
theorem cb_Xfixed :
    ∀ D ∈ ({Xidx} : Finset CBNode), SWIGNode.fixed D ∉ cbSWIGGraph.fixed := by
  intro D _ hmem
  simp [cbSWIGGraph] at hmem

/-- [The observed confounder satisfies the graphical backdoor criterion relative to the treatment
and outcome nodes in the continuous-backdoor example graph](goal).

The statement is on the computable SWIG graph; the full structural model has the
same graph by definition. -/
theorem cb_backdoor_criterion :
    Causalean.SWIGGraph.backdoorCriterion cbSWIGGraph
      ({Xidx} : Finset CBNode) cb_Xrand_obs cb_Xfixed
      {SWIGNode.random Yidx} {SWIGNode.random Zidx} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Guard: `{random Z}` is observed.
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    change SWIGNode.random Zidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
      SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
    simp
  · -- Guard: `{random Z}` is disjoint from `{random Y}`.
    decide
  · -- Guard: `{random Z}` is disjoint from `{random X}`.
    decide
  · -- Condition (i): no element of `{random Z}` is a descendant of `random X`.
    intro z hz D hD
    rw [Finset.mem_singleton] at hz hD
    subst hz; subst hD
    -- Goal: ¬ (initialSWIG cbDAG).isAncestor (.random X) (.random Z).
    -- The only edges from `random X` go to `random Y`; `Z` is not reachable.
    decide
  · -- Condition (ii): `{random Z} ∪ {fixed X}` d-separates `{random Y}` from
    -- `{random X}` in the splitMono graph.  Discharged via `splitMonoDAG`
    -- (computable) + `decide`, mirroring `SCM/Examples/BackDoor.lean`.
    exact (by decide :
      (cbSWIGGraph.splitMonoDAG ({Xidx} : Finset CBNode)).dSep
        {SWIGNode.random Yidx}
        (Finset.image SWIGNode.random ({Xidx} : Finset CBNode))
        ({SWIGNode.random Zidx} ∪ Finset.image SWIGNode.fixed ({Xidx} : Finset CBNode)))

-- ============================================================
-- § 5. Conditional Rule-2 identity via the toolkit (sanity check)
-- ============================================================

/-- [The outcome node is observed in the continuous-backdoor model](goal). -/
theorem cb_Yobs : ({SWIGNode.random Yidx} : Finset (SWIGNode CBNode)) ⊆
    continuousBackdoorSCM.observed := by
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Yidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- [The adjustment-set node is observed in the continuous-backdoor model](goal). -/
theorem cb_Zobs : ({SWIGNode.random Zidx} : Finset (SWIGNode CBNode)) ⊆
    continuousBackdoorSCM.observed := by
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Zidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- [The treatment's random-node image is observed in the continuous-backdoor model](goal). -/
theorem cb_Xr_obs : (({Xidx} : Finset CBNode).image SWIGNode.random) ⊆
    continuousBackdoorSCM.observed := by
  rw [Finset.image_singleton]
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Xidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- [The treatment's random-node image together with the adjustment set is observed](goal). -/
theorem cb_XrZ_obs : (({Xidx} : Finset CBNode).image SWIGNode.random ∪
    {SWIGNode.random Zidx}) ⊆ continuousBackdoorSCM.observed :=
  Finset.union_subset cb_Xr_obs cb_Zobs

/-- [The outcome node is disjoint from the treatment's random-node image](goal). -/
theorem cb_disj_YXr : Disjoint ({SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
    (({Xidx} : Finset CBNode).image SWIGNode.random) := by
  rw [Finset.image_singleton]; decide

/-- [The treatment's random-node image is disjoint from the adjustment set](goal). -/
theorem cb_disj_XrZ : Disjoint (({Xidx} : Finset CBNode).image SWIGNode.random)
    ({SWIGNode.random Zidx} : Finset (SWIGNode CBNode)) := by
  rw [Finset.image_singleton]; decide

/-- **Conditional Rule-2 identity on the continuous-backdoor example.** Given
    [fixed background values](hyp:s0),
    [observational joint positivity](hyp:hPositivity_ae),
    [the two Rule-2 conditional kernels agree almost everywhere](goal).

    This is a sanity check confirming that the general toolkit lemma
    `SCM.backdoor_rule2_ae` applies to the graphical criterion
    `cb_backdoor_criterion` on this concrete real-valued, degenerate example
    SCM: it verifies that the toolkit correctly handles the graph,
    non-descendance, kernel disintegration, and typeclass bookkeeping for
    this instance. It does not prove the positivity hypothesis itself from the
    model's constant structural equations. -/
theorem cb_backdoor_rule2_ae
    (s0 : continuousBackdoorSCM.FixedValues)
    (hPositivity_ae :
      (((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Xr_obs) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Zobs))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_XrZ_obs))) :
    ∀ᵐ p ∂((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Xr_obs) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Zobs))),
      (continuousBackdoorSCM.fixSet ({Xidx} : Finset CBNode) cb_Xrand_obs cb_Xfixed).obsCondKernel
          {SWIGNode.random Yidx} {SWIGNode.random Zidx}
          ((SCM.fixSet_observed continuousBackdoorSCM ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed).symm ▸ cb_Yobs)
          ((SCM.fixSet_observed continuousBackdoorSCM ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed).symm ▸ cb_Zobs)
          (continuousBackdoorSCM.fixSetExtend ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed s0 p.1, p.2)
      = continuousBackdoorSCM.obsCondKernel {SWIGNode.random Yidx}
          (({Xidx} : Finset CBNode).image SWIGNode.random ∪ {SWIGNode.random Zidx})
          cb_Yobs cb_XrZ_obs (s0, valuesUnionMk p.1 p.2) :=
  SCM.backdoor_rule2_ae continuousBackdoorSCM ({Xidx} : Finset CBNode)
    cb_Xrand_obs cb_Xfixed {SWIGNode.random Yidx} {SWIGNode.random Zidx}
    cb_Yobs cb_Zobs cb_Xr_obs cb_XrZ_obs cb_backdoor_criterion s0 hPositivity_ae

/-- Deprecated former name of `cb_backdoor_rule2_ae`. -/
@[deprecated cb_backdoor_rule2_ae (since := "2026-09-20")]
alias cb_backdoor_identified := cb_backdoor_rule2_ae

end Causalean.SCM.Examples.ContinuousBackdoor

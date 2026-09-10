/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM

/-! # Structural Monotonicity Assumptions

This file defines monotonicity as a restriction on a structural equation itself.
The predicate fixes an observed child and one of its parents, then requires the
child's structural function to be nondecreasing in that parent coordinate while
all other parent coordinates are held fixed.

The file also contains a two-node Boolean SCM used as a sanity check: one model
satisfies the structural restriction and one model violates it. These witnesses
show that the predicate is a genuine constraint on `structFun`, not a vacuous
edge label.
-/

namespace Causalean.SCM.Assumptions

open Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [a finite collection of variables whose members can be compared for equality and that have measurable ordered value spaces](hyp:N,Ω) and [each random or fixed copy of a variable](hyp:s), [an order on that copy's value space](goal) is provided by the order on the corresponding base-variable value space, with [the random-copy case](step:1) and [the fixed-copy case](step:2) treated identically.

The random and fixed copies of a node use the same value space, so an order on
each base-variable space also orders each SWIG coordinate. -/
instance instPreorderSwigΩ [∀ n, Preorder (Ω n)] :
    ∀ s : SWIGNode N, Preorder (swigΩ Ω s)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- For [a finite population of nodes with measurable ordered value spaces](hyp:N,Ω), [a child
node](hyp:child), [a parent node](hyp:parent), and [a structural causal model](hyp:M), [the
monotone-mechanism condition](goal) holds precisely when [the child is observed](step:1), the
parent is a parent of that child, and for every two parent-value assignments that agree
at all other parent coordinates and are ordered at the designated parent coordinate, the child's
structural-function value is ordered in the same direction.

`MonotoneMechanism child parent M` says that `child` is an observed node of the
model, `parent` is a parent of that child in the model's DAG, and the structural
equation for `child` is nondecreasing in the `parent` input when all other
parent inputs are held fixed. This is a restriction on the structural function,
not on the graph's edge-type labels. -/
def MonotoneMechanism [∀ n, Preorder (Ω n)]
    (child parent : SWIGNode N) (M : Causalean.SCM N Ω) : Prop :=
  ∃ hchild : child ∈ M.observed,
    ∃ hparent : parent ∈ M.dag.parents child,
      ∀ x y : ∀ w : {w // w ∈ M.dag.parents child}, swigΩ Ω w.val,
        x ⟨parent, hparent⟩ ≤ y ⟨parent, hparent⟩ →
        (∀ w, w.val ≠ parent → x w = y w) →
        M.structFun ⟨child, hchild⟩ x ≤ M.structFun ⟨child, hchild⟩ y

/-! ## Concrete Boolean witnesses -/

/-- [The Boolean-chain node type](goal) consists of [the treatment node](hyp:d) and [the outcome node](hyp:y). -/
inductive BoolChainNode
  | d
  | y
  deriving DecidableEq, Repr

namespace BoolChainNode

/-- [A finite enumeration of the Boolean-chain node type](goal) is provided by [the two-element collection containing treatment and outcome](step:1) together with [the assertion that every Boolean-chain node belongs to that collection](step:2).

Written out by hand rather than obtained from `deriving Fintype`: Mathlib's
enum `Fintype` deriving handler currently emits a `Finset.mk` whose `nodup`
field is only defeq-correct at default transparency, which the `rw` in its
generated completeness proof rejects. -/
instance instFintype : Fintype BoolChainNode where
  elems := {d, y}
  complete := by intro x; cases x <;> decide

/-- [The Boolean-chain edge relation](goal) holds for the ordered pair consisting of treatment
$d$ and outcome $y$, and holds for no other ordered pair of Boolean-chain nodes. -/
def edge : BoolChainNode → BoolChainNode → Prop
  | d, y => True
  | _, _ => False

/-- For every ordered pair of Boolean-chain nodes, [a decision procedure for whether the pair is a directed edge](goal) is provided. -/
instance edgeDecidable : DecidableRel edge := by
  intro a b
  cases a <;> cases b
  · exact isFalse (fun h => h)
  · exact isTrue trivial
  · exact isFalse (fun h => h)
  · exact isFalse (fun h => h)

/-- [The Boolean-chain topological ranking](goal) assigns rank zero to treatment $d$ and rank one
to outcome $y$. -/
def topo : BoolChainNode → ℕ
  | d => 0
  | y => 1

private theorem topo_injective : Function.Injective topo := by
  intro a b h
  cases a <;> cases b <;> simp [topo] at h ⊢

private theorem topo_lt : ∀ a b, edge a b → topo a < topo b := by
  intro a b h
  cases a <;> cases b <;> simp [edge, topo] at h ⊢

/-- [The Boolean-chain directed acyclic graph](goal) is the two-node graph whose only directed
edge is from treatment $d$ to outcome $y$. -/
def dag : DAG BoolChainNode where
  edge := edge
  decEdge := edgeDecidable
  acyclic := DAG.acyclic_of_topoOrder topo_lt

end BoolChainNode

open BoolChainNode

/-- [The Boolean-chain single-world intervention graph](goal) has random observed treatment $d$
and outcome $y$, no fixed nodes, and no unobserved nodes, with the Boolean-chain directed graph.
-/
def boolChainSWIG : SWIGGraph BoolChainNode where
  dag := initialSWIG BoolChainNode.dag
  fixed := ∅
  observed := {SWIGNode.random d, SWIGNode.random y}
  unobserved := ∅
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by intro u hu; simp at hu
  obs_unobs_disjoint := by
    rw [Finset.disjoint_right]
    intro x hx
    simp at hx
  dag_edges_classified := by decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by intro u hu; simp at hu
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by decide, by decide⟩
  all_children_in_observed := by decide

/-- [The Boolean-chain value-space assignment](goal) gives both treatment $d$ and outcome $y$
the two-point Boolean value space. -/
def boolChainΩ : BoolChainNode → Type := fun _ => Bool

/-- For [each Boolean-chain node](hyp:n), [the measurable-space structure on its Boolean value space](goal) is the discrete measurable space, with [the treatment case](step:1) and [the outcome case](step:2) specified separately. -/
instance boolChainMeasurableSpace : ∀ n, MeasurableSpace (boolChainΩ n)
  | d => ⊤
  | y => ⊤

/-- For [each Boolean-chain node](hyp:n), [the preorder on its Boolean value space](goal) is the usual Boolean preorder, with [the treatment case](step:1) and [the outcome case](step:2) specified separately. -/
instance boolChainPreorder : ∀ n, Preorder (boolChainΩ n)
  | d => inferInstanceAs (Preorder Bool)
  | y => inferInstanceAs (Preorder Bool)

/-- [The designated Boolean-chain outcome-parent coordinate](goal) is the random treatment node
$d$, the sole parent of the random outcome node $y$. -/
def boolChainDParent :
    {w // w ∈ boolChainSWIG.dag.parents (SWIGNode.random y)} :=
  ⟨SWIGNode.random d, by decide⟩

/-- For [an observed node of the Boolean-chain graph](hyp:v), [the Boolean copying structural
equation](goal) returns false at treatment $d$ and, at outcome $y$, returns the value assigned to
the treatment-parent coordinate.

The treatment node is fixed at `false`; the outcome node copies the treatment
parent coordinate. -/
def copyStructFun (v : {v // v ∈ boolChainSWIG.observed}) :
    (∀ w : {w // w ∈ boolChainSWIG.dag.parents v.val}, swigΩ boolChainΩ w.val) →
      swigΩ boolChainΩ v.val := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact fun _ => false
      | y => exact fun parents => parents boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- For [an observed node of the Boolean-chain graph](hyp:v), [the Boolean reversing structural
equation](goal) returns false at treatment $d$ and, at outcome $y$, returns the Boolean negation
of the value assigned to the treatment-parent coordinate.

The treatment node is fixed at `false`; the outcome node reverses the treatment
parent coordinate. -/
def flipStructFun (v : {v // v ∈ boolChainSWIG.observed}) :
    (∀ w : {w // w ∈ boolChainSWIG.dag.parents v.val}, swigΩ boolChainΩ w.val) →
      swigΩ boolChainΩ v.val := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact fun _ => false
      | y => exact fun parents => !parents boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- Each structural function of the copy mechanism on the Boolean chain example is
measurable. -/
@[fun_prop]
theorem copyStructFun_measurable (v : {v // v ∈ boolChainSWIG.observed}) :
    Measurable (copyStructFun v) := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact measurable_const
      | y => exact measurable_pi_apply boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- Each structural function of the flip mechanism on the Boolean chain example is
measurable. -/
@[fun_prop]
theorem flipStructFun_measurable (v : {v // v ∈ boolChainSWIG.observed}) :
    Measurable (flipStructFun v) := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact measurable_const
      | y =>
          exact (measurable_of_finite (fun b : Bool => !b)).comp
            (measurable_pi_apply boolChainDParent)
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- [The monotone Boolean structural causal model](goal) is the Boolean-chain model with no
fixed or latent nodes, nonparametric edge labels, and the copying structural equation.

This concrete model witnesses that the structural monotonicity predicate is
satisfiable. -/
noncomputable def monotoneBoolSCM : Causalean.SCM BoolChainNode boolChainΩ where
  toSWIGGraph := boolChainSWIG
  edgeTypes := EdgeTypeAssignment.allNonparametric boolChainSWIG.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := copyStructFun
  structFun_measurable := copyStructFun_measurable
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

/-- [The antitone Boolean structural causal model](goal) is the Boolean-chain model with no
fixed or latent nodes, nonparametric edge labels, and the reversing structural equation.

This concrete model witnesses that the structural monotonicity predicate is a
nontrivial restriction: an otherwise well-formed SCM can violate it. -/
noncomputable def antitoneBoolSCM : Causalean.SCM BoolChainNode boolChainΩ where
  toSWIGGraph := boolChainSWIG
  edgeTypes := EdgeTypeAssignment.allNonparametric boolChainSWIG.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := flipStructFun
  structFun_measurable := flipStructFun_measurable
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

/-- For [a Boolean value](hyp:b), [the Boolean-chain outcome-parent assignment](goal) assigns
that value to the designated treatment-parent coordinate and false to every other parent
coordinate.

All non-designated parent coordinates, if any, are fixed at `false`. In the
two-node witness graph there are no such coordinates. -/
def boolParentAssignment (b : Bool) :
    ∀ w : {w // w ∈ boolChainSWIG.dag.parents (SWIGNode.random y)},
      swigΩ boolChainΩ w.val := by
  intro w
  rcases w with ⟨n, _⟩
  cases n with
  | random n =>
      cases n with
      | d => exact b
      | y => exact false
  | fixed n =>
      cases n <;> exact false

/-- Evaluating the Boolean parent assignment at the designated parent returns
the assigned value. -/
@[simp] theorem boolParentAssignment_boolChainDParent (b : Bool) :
    boolParentAssignment b boolChainDParent = b := by
  cases b <;> rfl

/-- [The copying Boolean structural causal model satisfies monotonicity of the outcome mechanism
in the designated parent coordinate](goal).

The witness is substantive: the proof applies the actual structural equation
for the outcome node. -/
theorem monotoneBoolSCM_satisfies :
    MonotoneMechanism (Ω := boolChainΩ)
      (SWIGNode.random y) (SWIGNode.random d) monotoneBoolSCM := by
  refine ⟨by simp [monotoneBoolSCM, boolChainSWIG], boolChainDParent.property, ?_⟩
  intro x y hxy _
  exact hxy

/-- [The reversing Boolean structural causal model violates monotonicity of the outcome mechanism
in the designated parent coordinate](goal).

The low parent value maps to `true` and the high parent value maps to `false`,
so the required nondecreasing inequality fails. -/
theorem antitoneBoolSCM_violates :
    ¬ MonotoneMechanism (Ω := boolChainΩ)
      (SWIGNode.random y) (SWIGNode.random d) antitoneBoolSCM := by
  intro hmono
  rcases hmono with ⟨hchild, hparent, hmono⟩
  have hle :
      boolParentAssignment false ⟨SWIGNode.random d, hparent⟩ ≤
        boolParentAssignment true ⟨SWIGNode.random d, hparent⟩ := by
    change false ≤ true
    decide
  have hsame :
      ∀ w, w.val ≠ SWIGNode.random d →
        boolParentAssignment false w = boolParentAssignment true w := by
    intro w hw
    rcases w with ⟨n, hn⟩
    cases n with
    | random n =>
        cases n with
        | d => simp at hw
        | y => rfl
    | fixed n =>
        cases n <;> rfl
  have hbad := hmono (boolParentAssignment false) (boolParentAssignment true) hle hsame
  change Bool.not (boolParentAssignment false boolChainDParent) ≤
      Bool.not (boolParentAssignment true boolChainDParent) at hbad
  simp only [boolParentAssignment_boolChainDParent] at hbad
  cases hbad rfl

end Causalean.SCM.Assumptions

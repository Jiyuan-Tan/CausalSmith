/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.MinimaxATE.Model
import Causalean.PO.ID.Exact.ATE
import Causalean.PO.Bridge.FromSCM
import Causalean.Graph.DAG
import Causalean.Graph.SWIG
import Causalean.SCM.Model.EdgeType
import Causalean.SCM.Model.SCM
import Mathlib.Probability.Distributions.Uniform

/-!
# Causal Grounding of the Minimax ATE Model

This file builds, from a finite data-generating process `(m, g)` on a finite
covariate space `C`, a concrete generalized SCM realizing the textbook backdoor
triangle and lifts it through `Causalean.PO.Bridge.FromSCM.POSystem.ofSCM` to a
`POBackdoorSystem`.  Its potential-outcome ATE `S.ATE = E[Y(1) − Y(0)]` is what
the minimax lower bound is *really* about; the bridge `MinimaxATE/Causal/Bridge.lean`
identifies `S.ATE` with the observed-data contrast `ate g` used by the proof
machinery.

The DAG is the backdoor triangle on the OBSERVED covariate `Xc`:
`Un → Xc → A → Y` with `Xc → Y`, plus independent latent noise roots
`Ea → A`, `Ey → Y`:

* `Un ~ Uniform(C)`, the latent covariate draw; the observed covariate node
  `Xc := Un` copies it (Causalean SCM observed nodes must be endogenous);
* treatment `A := 1{Ea ≤ m Xc}`, so `A | X=x ~ Bernoulli(m x)` (`Ea ~ U[0,1]`);
* outcome `Y(a) := 1{Ey ≤ g a Xc}` and `Y := A·Y(1) + (1−A)·Y(0)`
  (`Ey ~ U[0,1]`), the consistency assignment; `Ea ⟂ Ey | X` so unconfoundedness
  `A ⟂ (Y(1), Y(0)) | X` holds.

Mirrors the proven-shape witness construction in
`CausalSmith/.../STAT_AteOverlapDecay_Clean/Witness/Construction.lean` (Causalean
cannot import CausalSmith, so the construction is reproduced here, specialized to
a finite covariate `C` and the propensity/outcome pair `(m, g)`).  The main
public objects are the witness graph data `WNode`, `wDAG`, and `wSWIGGraph`; the
structural functions `treatFun` and `outFun`; the laws `unifLaw` and `covLaw`;
the concrete SCM `dgpSCM`; and the induced potential-outcome/backdoor systems
`dgpPO` and `dgpBackdoor`.
-/

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO
open MeasureTheory

/-! ## The witness node type and graph (covariate-independent) -/

/-- The [finite backdoor witness-node type](goal) consists of [the observed covariate node](hyp:Xc), the treatment node, the outcome node, the latent covariate-draw node, the treatment-noise node, and the outcome-noise node. -/
inductive WNode
  | Xc | A | Y | Un | Ea | Ey
  deriving DecidableEq

namespace WNode

/-- [The printable representation of a witness-graph node](goal) is its corresponding node label,
with [the observed covariate](step:1), [treatment](step:2), [outcome](step:3), [the latent
covariate draw](step:4), [treatment noise](step:5), and [outcome noise](step:6) given their six
respective labels. -/
protected def repr : WNode → Nat → Std.Format
  | Xc, _ => "WNode.Xc"
  | A, _ => "WNode.A"
  | Y, _ => "WNode.Y"
  | Un, _ => "WNode.Un"
  | Ea, _ => "WNode.Ea"
  | Ey, _ => "WNode.Ey"

/-- The [printable representation of a finite backdoor witness node](goal) is [the node's corresponding label](step:1). -/
instance : Repr WNode := ⟨WNode.repr⟩

/-- The [finite enumeration of backdoor witness nodes](goal) consists of [the six witness nodes, with every witness node included](step:1) and [a proof that this enumeration is exhaustive](step:2). -/
instance : Fintype WNode where
  elems := {Xc, A, Y, Un, Ea, Ey}
  complete := by intro x; cases x <;> simp

end WNode

open WNode

/-- [The edge relation of the finite backdoor witness graph](goal) contains [the arrow from the
latent covariate draw to the observed covariate](step:1), [the arrow from the observed covariate
to treatment](step:2), [the arrow from the observed covariate to outcome](step:3), [the arrow
from treatment to outcome](step:4), [the arrow from treatment noise to treatment](step:5), and
[the arrow from outcome noise to outcome](step:6); [every other ordered pair has no arrow](step:7). -/
def wEdge : WNode → WNode → Prop
  | Un, Xc => True
  | Xc, A  => True
  | Xc, Y  => True
  | A,  Y  => True
  | Ea, A  => True
  | Ey, Y  => True
  | _,  _  => False

/-- The [procedure deciding whether an ordered pair of witness nodes is an edge](goal) [examines the finite witness-graph edge relation](step:1). -/
instance : DecidableRel wEdge := by
  intro a b; cases a <;> cases b <;> simp [wEdge] <;> infer_instance

/-- [The topological ordering of a witness-graph node](goal) assigns [rank zero to the latent
covariate draw](step:1), [rank one to treatment noise](step:2), [rank two to outcome noise](step:3),
[rank three to the observed covariate](step:4), [rank four to treatment](step:5), and [rank five
to the outcome](step:6). -/
def wTopo : WNode → ℕ
  | Un => 0
  | Ea => 1
  | Ey => 2
  | Xc => 3
  | A  => 4
  | Y  => 5

/-- [Every edge of the finite backdoor witness graph points strictly forward in the chosen
topological order on its nodes](goal). -/
theorem wTopo_lt : ∀ u v, wEdge u v → wTopo u < wTopo v := by
  intro u v h; cases u <;> cases v <;> simp_all [wEdge, wTopo]

/-- [The directed acyclic graph for the finite backdoor witness](goal) is the graph whose nodes
are the witness nodes and whose arrows are the specified witness-graph edge relation. -/
def wDAG : DAG WNode where
  edge := wEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder wTopo_lt

/-- [The single-world intervention graph for the finite backdoor witness](goal) has the witness
directed acyclic graph, no fixed nodes, observed nodes for the covariate, treatment, and outcome,
and unobserved nodes for the three latent noise variables. -/
def wSWIGGraph : SWIGGraph WNode where
  dag := initialSWIG wDAG
  fixed := ∅
  observed := {SWIGNode.random Xc, SWIGNode.random A, SWIGNode.random Y}
  unobserved := {SWIGNode.random Un, SWIGNode.random Ea, SWIGNode.random Ey}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obs_unobs_disjoint := by decide
  dag_edges_classified := by decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl <;>
      simpa [initialSWIG] using
        (swig_random_root_of_root wDAG ∅ _ (by decide))
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by decide, by decide⟩
  all_children_in_observed := by decide

section DGP

variable (C : Type) [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]

/-- For [a covariate space](hyp:C), [the value space assigned to each witness-graph node](goal)
is [the covariate space for the observed covariate](step:1), [the binary space for treatment](step:2),
[the real line for the outcome](step:3), [the covariate space for the latent covariate draw](step:4),
[the real line for treatment noise](step:5), and [the real line for outcome noise](step:6). -/
def WΩ : WNode → Type
  | Xc => C
  | A  => Bool
  | Y  => ℝ
  | Un => C
  | Ea => ℝ
  | Ey => ℝ

/-- For [a covariate space equipped with a measurable structure](hyp:C) and [each witness node](hyp:n), the [measurable-space structure for that witness-node value space](goal) is [the given covariate measurable structure for the observed covariate](step:1), [the binary measurable structure for treatment](step:2), [the real-line measurable structure for outcome](step:3), [the given covariate measurable structure for the latent covariate draw](step:4), [the real-line measurable structure for treatment noise](step:5), and [the real-line measurable structure for outcome noise](step:6). -/
noncomputable instance WΩ_meas : ∀ n, MeasurableSpace (WΩ C n)
  | Xc => inferInstanceAs (MeasurableSpace C)
  | A  => inferInstanceAs (MeasurableSpace Bool)
  | Y  => inferInstanceAs (MeasurableSpace ℝ)
  | Un => inferInstanceAs (MeasurableSpace C)
  | Ea => inferInstanceAs (MeasurableSpace ℝ)
  | Ey => inferInstanceAs (MeasurableSpace ℝ)

/-- For [a covariate space equipped with a measurable structure and a standard-Borel structure](hyp:C) and [each witness node](hyp:n), the [standard-Borel structure for that witness-node value space](goal) is [the given structure for the observed covariate](step:1), [the binary structure for treatment](step:2), [the real-line structure for outcome](step:3), [the given structure for the latent covariate draw](step:4), [the real-line structure for treatment noise](step:5), and [the real-line structure for outcome noise](step:6). -/
noncomputable instance WΩ_borel : ∀ n, StandardBorelSpace (WΩ C n)
  | Xc => inferInstanceAs (StandardBorelSpace C)
  | A  => inferInstanceAs (StandardBorelSpace Bool)
  | Y  => inferInstanceAs (StandardBorelSpace ℝ)
  | Un => inferInstanceAs (StandardBorelSpace C)
  | Ea => inferInstanceAs (StandardBorelSpace ℝ)
  | Ey => inferInstanceAs (StandardBorelSpace ℝ)

/-- For [a nonempty covariate space](hyp:C) and [each witness node](hyp:n), the [nonemptiness certificate for that witness-node value space](goal) is [the given certificate for the observed covariate](step:1), [a binary value for treatment](step:2), [a real value for outcome](step:3), [the given certificate for the latent covariate draw](step:4), [a real value for treatment noise](step:5), and [a real value for outcome noise](step:6). -/
instance WΩ_nonempty : ∀ n, Nonempty (WΩ C n)
  | Xc => inferInstanceAs (Nonempty C)
  | A  => inferInstanceAs (Nonempty Bool)
  | Y  => inferInstanceAs (Nonempty ℝ)
  | Un => inferInstanceAs (Nonempty C)
  | Ea => inferInstanceAs (Nonempty ℝ)
  | Ey => inferInstanceAs (Nonempty ℝ)

/-! ## Structural functions and parent-value plumbing -/

/-- Given [a real-valued propensity score](hyp:p) and [a real-valued treatment-noise draw](hyp:ea),
[the binary treatment assignment](goal) is true exactly when the noise draw is no greater than
the propensity score. -/
noncomputable def treatFun (p ea : ℝ) : Bool := decide (ea ≤ p)

/-- Given [a covariate space](hyp:C), [an outcome-regression function indexed by binary treatment and covariate value](hyp:g),
[a binary treatment value](hyp:a), [a covariate value](hyp:x), and [a real-valued outcome-noise
draw](hyp:ey), [the real-valued outcome](goal) is one exactly when the noise draw is no greater
than the corresponding outcome-regression value, and is zero otherwise. -/
noncomputable def outFun (g : Bool → C → ℝ) (a : Bool) (x : C) (ey : ℝ) : ℝ :=
  if ey ≤ g a x then 1 else 0

/-- [For any edge from node `p` to node `c` in the finite backdoor witness graph](hyp:h),
[the SWIG node for `p` is a parent of the SWIG node for `c` in the initial SWIG built from
that graph](goal). -/
theorem wParent_mem {p c : WNode} (h : wEdge p c) :
    (SWIGNode.random p) ∈ (initialSWIG wDAG).parents (SWIGNode.random c) := by
  rw [DAG.mem_parents, initialSWIG_random_edge]; exact h

/-- Given [a covariate space](hyp:C),
[a child witness node](hyp:c), [the supplied values of all parents of that child](hyp:vals),
[a parent witness node](hyp:p), and [an arrow from that parent to the child](hyp:h), [the
extracted parent value](goal) is that parent’s supplied value. -/
def parentVal {c : WNode}
    (vals : ∀ w : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random c)}, swigΩ (WΩ C) w.val)
    {p : WNode} (h : wEdge p c) : WΩ C p :=
  vals ⟨SWIGNode.random p, wParent_mem h⟩

/-- [The latent-noise probability law](goal) is the uniform probability distribution on the
closed unit interval $[0,1]$ of the real line. -/
noncomputable def unifLaw : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- [The uniform law on the closed unit interval is a probability measure](goal). -/
instance instIsProbabilityMeasureUnifLaw : IsProbabilityMeasure unifLaw := by
  unfold unifLaw
  constructor
  simp [Real.volume_Icc]

/-- For [a finite, nonempty covariate space equipped with a measurable structure](hyp:C),
[the covariate probability law](goal) assigns equal probability to every covariate value. -/
noncomputable def covLaw : Measure C := (PMF.uniformOfFintype C).toMeasure

/-- For [a finite, nonempty covariate space equipped with a measurable structure](hyp:C), [the uniform covariate law is a probability measure](goal). -/
instance instIsProbabilityMeasureCovLaw : IsProbabilityMeasure (covLaw C) := by
  unfold covLaw; infer_instance

variable {C}

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C),
[a propensity function](hyp:m), and [an outcome-regression function for the two treatment
arms](hyp:g), [the structural causal model](goal) has a uniformly distributed latent covariate,
independent unit-interval treatment and outcome noises, treatment generated by thresholding its
noise at the propensity, and outcome generated by thresholding its noise at the arm-specific
outcome regression.

It realizes the backdoor triangle with a uniform covariate root, independent unit-interval noise
for treatment and outcome, treatment generated from the propensity, and outcome generated from
the arm-specific outcome regression. -/
noncomputable def dgpSCM (m : C → ℝ) (g : Bool → C → ℝ) :
    Causalean.SCM WNode (WΩ C) where
  toSWIGGraph := wSWIGGraph
  edgeTypes := EdgeTypeAssignment.allNonparametric (initialSWIG wDAG)
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := fun v vals =>
    match v with
    | ⟨SWIGNode.random Xc, _⟩ =>
        (parentVal (C := C) vals (show wEdge Un Xc from trivial) : C)
    | ⟨SWIGNode.random A, _⟩ =>
        treatFun (m (parentVal (C := C) vals (show wEdge Xc A from trivial)))
                 (parentVal (C := C) vals (show wEdge Ea A from trivial))
    | ⟨SWIGNode.random Y, _⟩ =>
        outFun (C := C) g (parentVal (C := C) vals (show wEdge A Y from trivial))
                 (parentVal (C := C) vals (show wEdge Xc Y from trivial))
                 (parentVal (C := C) vals (show wEdge Ey Y from trivial))
    | ⟨SWIGNode.random Un, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.random Ea, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.random Ey, h⟩ => absurd h (by decide)
    | ⟨SWIGNode.fixed n, h⟩ =>
        (by simp only [wSWIGGraph, Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h | h <;> exact absurd h (by simp) : False).elim
  structFun_measurable := by
    intro v
    rcases v with ⟨n, hn⟩
    cases n with
    | random a =>
        cases a <;> simp [parentVal, treatFun, outFun]
        · exact measurable_pi_apply _
        · let iEa : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random A)} :=
            ⟨SWIGNode.random Ea, wParent_mem (show wEdge Ea A from trivial)⟩
          let iX : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random A)} :=
            ⟨SWIGNode.random Xc, wParent_mem (show wEdge Xc A from trivial)⟩
          have hEa : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random A)},
                  swigΩ (WΩ C) w.val) => (show ℝ from vals iEa)) := by
            exact measurable_pi_apply iEa
          have hX : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random A)},
                  swigΩ (WΩ C) w.val) => (show C from vals iX)) := by
            exact measurable_pi_apply iX
          -- `decide P` and `if P then true else false` are definitionally equal,
          -- so we may take the `ite` route and avoid any rewrite inside the goal.
          show Measurable
            (fun vals : (∀ w : {w // w ∈
                (initialSWIG wDAG).parents (SWIGNode.random A)},
                swigΩ (WΩ C) w.val) =>
              if (show ℝ from vals iEa) ≤ m (show C from vals iX) then true else false)
          refine Measurable.ite ?_ measurable_const measurable_const
          exact measurableSet_le hEa ((measurable_of_finite m).comp hX)
        · let iEy : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random Ey, wParent_mem (show wEdge Ey Y from trivial)⟩
          let iA : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random A, wParent_mem (show wEdge A Y from trivial)⟩
          let iX : {w // w ∈ (initialSWIG wDAG).parents (SWIGNode.random Y)} :=
            ⟨SWIGNode.random Xc, wParent_mem (show wEdge Xc Y from trivial)⟩
          have hEy : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show ℝ from vals iEy)) := by
            exact measurable_pi_apply iEy
          have hA : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show Bool from vals iA)) := by
            exact measurable_pi_apply iA
          have hX : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) => (show C from vals iX)) := by
            exact measurable_pi_apply iX
          have hg : Measurable
              (fun vals : (∀ w : {w // w ∈
                  (initialSWIG wDAG).parents (SWIGNode.random Y)},
                  swigΩ (WΩ C) w.val) =>
                g (show Bool from vals iA) (show C from vals iX)) :=
            (measurable_of_finite (fun p : Bool × C => g p.1 p.2)).comp
              (hA.prodMk hX)
          refine Measurable.ite ?_ measurable_const measurable_const
          exact measurableSet_le hEy hg
    | fixed a =>
        simp [wSWIGGraph] at hn
  latentDist := fun u => by
    rcases u with ⟨n, hn⟩
    exact
      match n, hn with
      | SWIGNode.random Un, _ => covLaw C
      | SWIGNode.random Ea, _ => unifLaw
      | SWIGNode.random Ey, _ => unifLaw
      | _, _ => (0 : Measure _)
  isProbability_latent := by
    intro u
    rcases u with ⟨n, hn⟩
    cases n with
    | random n =>
        cases n <;> simp [wSWIGGraph] at hn ⊢
        · exact instIsProbabilityMeasureCovLaw C
        · exact instIsProbabilityMeasureUnifLaw
        · exact instIsProbabilityMeasureUnifLaw
    | fixed n =>
        simp [wSWIGGraph] at hn

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C),
[a propensity function](hyp:m), and [an outcome-regression function](hyp:g), [the background
assignment for the witness causal model](goal) assigns no fixed values. -/
noncomputable def dgpFixed (m : C → ℝ) (g : Bool → C → ℝ) :
    SCM.FixedValues (dgpSCM m g) :=
  fun s => (Finset.notMem_empty s.val s.property).elim

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the induced potential-outcome system](goal) is the
one generated by the witness structural causal model with its empty background assignment. -/
noncomputable def dgpPO (m : C → ℝ) (g : Bool → C → ℝ) : POSystem :=
  POSystem.ofSCM (dgpSCM m g) (dgpFixed m g)

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the treatment index](goal) is the observed
treatment node of the induced potential-outcome system. -/
noncomputable def AIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random A, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the outcome index](goal) is the observed outcome
node of the induced potential-outcome system. -/
noncomputable def YIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random Y, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the covariate index](goal) is the observed
covariate node of the induced potential-outcome system. -/
noncomputable def XIdx (m : C → ℝ) (g : Bool → C → ℝ) : (dgpPO m g).V :=
  (⟨SWIGNode.random Xc, by simp [dgpSCM, wSWIGGraph]⟩ : ObsIdx (dgpSCM m g))

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the measurable identification of the treatment
node’s value space with the binary treatment space](goal) is the identity map. -/
noncomputable def AEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (AIdx m g) ≃ᵐ Bool :=
  MeasurableEquiv.refl Bool

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the measurable identification of the outcome
node’s value space with the real line](goal) is the identity map. -/
noncomputable def YEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (YIdx m g) ≃ᵐ ℝ :=
  MeasurableEquiv.refl ℝ

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the measurable identification of the covariate
node’s value space with the covariate space](goal) is the identity map. -/
noncomputable def XEquiv (m : C → ℝ) (g : Bool → C → ℝ) :
    (dgpPO m g).X (XIdx m g) ≃ᵐ C :=
  MeasurableEquiv.refl C

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C), [a propensity function](hyp:m),
and [an outcome-regression function](hyp:g), [the backdoor potential-outcome system](goal) uses
the constructed treatment, outcome, and covariate nodes as its treatment, outcome, and adjustment
variables.

It uses the constructed treatment, outcome, and covariate nodes as the variables of the backdoor
estimation problem. -/
noncomputable def dgpBackdoor (m : C → ℝ) (g : Bool → C → ℝ) :
    POBackdoorSystem (dgpPO m g) C where
  D := AIdx m g
  Y := YIdx m g
  Xvar := ⟨XIdx m g, XEquiv m g⟩
  hDbool := AEquiv m g
  hYreal := YEquiv m g
  hDY := by
    intro h; have := congrArg Subtype.val h
    simp only [AIdx, YIdx] at this; exact absurd this (by decide)
  hDX := by
    intro h; have := congrArg Subtype.val h
    simp only [AIdx, XIdx] at this; exact absurd this (by decide)
  hYX := by
    intro h; have := congrArg Subtype.val h
    simp only [YIdx, XIdx] at this; exact absurd this (by decide)

end DGP

end Causalean.Estimation.MinimaxATE.Causal

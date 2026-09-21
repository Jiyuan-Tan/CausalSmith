/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Identifiable
public import Causalean.Stat.AttainableSet

/-! # Compatible structural causal models for graphical partial identification

This file provides the object over which graphical **partial identification** quantifies:
the class of structural causal models that share a given causal diagram, satisfy stated
structural assumptions, and reproduce a reference observational law. A bound on a causal
query is *sound* when every model in this class satisfies it, and the resulting identified
set is the range of the query over the class.

Concretely, fixing a SWIG graph `G`, a structural-assumption predicate `As`, and a reference
model `M₀`, the **compatible class** collects the models `M` that (i) have diagram `G`, (ii)
satisfy `As`, and (iii) are observationally equivalent to `M₀` (same derived observational
kernel). The **compatible identified set** of a real-valued query is the range of that query
over the compatible class — an instance of the shared abstract `IdentifiedSet`.

## Finite response-function reduction

For finite observed-variable domains, Theorem 1 of Zhang, Tian, and Bareinboim (2022),
*Partial Counterfactual Identification from Observational and Experimental Data*, gives a
canonical representation with finite exogenous domains that preserves counterfactual
distributions. That result does not justify a finite reduction for the arbitrary measurable
value spaces admitted here, and no such reduction is formalized in this file. Soundness of a
bound uses only the compatible class. The library's finite Balke–Pearl realization instead
lives in the potential-outcomes framework (`Causalean/PO/ID/Partial/BalkePearl/`).
-/

@[expose] public section

open Causalean.Graph


namespace Causalean.SCM.PartialID

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [a finite collection of distinguishable node labels](hyp:N) with
[measurable value spaces](hyp:Ω), [a SWIG graph](hyp:G),
[a predicate specifying structural assumptions](hyp:As), and
[a reference structural causal model](hyp:M₀), the [compatible-model class](goal)
is the collection of structural causal models that [have the given graph](step:1),
satisfy the given assumptions, and
are observationally equivalent to the reference model.

The **compatible class** for a graphical partial-identification problem: the structural
causal models `M` that share the SWIG graph `G`, satisfy the structural assumptions `As`, and
are observationally equivalent to the reference model `M₀` (their derived observational
kernels agree). This is the class over which a bound must hold to be *sound*. -/
def CompatibleSCM (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) : Causalean.SCM N Ω → Prop :=
  fun M => M.toSWIGGraph = G ∧ As M ∧ Causalean.SCM.ID.obsEquiv M M₀

/-- For any graph `G`, structural-assumption predicate `As`, and reference model `M₀`, if [`M₀`'s
own SWIG graph is `G`](hyp:hG) and [`M₀` satisfies the structural assumptions `As`](hyp:hAs),
then [`M₀` belongs to its own compatible class `CompatibleSCM G As M₀`](goal). -/
theorem compatibleSCM_self (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) (hG : M₀.toSWIGGraph = G) (hAs : As M₀) :
    CompatibleSCM G As M₀ M₀ :=
  ⟨hG, hAs, HEq.rfl⟩

/-- If [the structural-assumption predicate `As'` is stronger than `As`, i.e. every model
satisfying `As'` also satisfies `As`](hyp:h), then [every model compatible with the reference
model `M₀` under the stricter assumptions `As'` is also compatible under the weaker assumptions
`As`](goal) — strengthening the structural assumptions can only shrink the compatible class. -/
theorem compatibleSCM_mono {G : SWIGGraph N} {As As' : Causalean.SCM N Ω → Prop}
    {M₀ : Causalean.SCM N Ω} (h : ∀ M, As' M → As M) :
    ∀ M, CompatibleSCM G As' M₀ M → CompatibleSCM G As M₀ M :=
  fun _ hM => ⟨hM.1, h _ hM.2.1, hM.2.2⟩

/-- For [a finite collection of distinguishable node labels](hyp:N) with
[measurable value spaces](hyp:Ω), [a SWIG graph](hyp:G),
[a predicate specifying structural assumptions](hyp:As),
[a reference structural causal model](hyp:M₀), and [a real-valued causal query](hyp:obj),
the [compatible identified set](goal) is the set of all query values attained by
structural causal models compatible with that graph, assumptions, and reference model.

The defined range need not be an interval. A partial-identification bound `[L, U]` is *sound*
exactly when this set is contained in `Set.Icc L U`, and *sharp* when they are equal. Built on
the abstract `IdentifiedSet`. -/
noncomputable def compatibleIdentifiedSet (G : SWIGGraph N)
    (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) (obj : Causalean.SCM N Ω → ℝ) : Set ℝ :=
  Causalean.Stat.AttainableSet.IdentifiedSet obj (CompatibleSCM G As M₀)

/-- Deprecated former name of `compatibleIdentifiedSet`. -/
@[deprecated compatibleIdentifiedSet (since := "2026-09-20")]
alias compatibleInterval := compatibleIdentifiedSet

end Causalean.SCM.PartialID

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.InvariantPrediction.Invariance

/-!
# Invariant Causal Prediction: the identified set `S(E)`

The **identified set** `S(E)` is the intersection of all invariant predictor
sets.  By `mechanism_invariant` the target's observed parents are invariant, so
the collection is nonempty and `S(E)` is contained in the parents — the
soundness direction (proved in `Soundness.lean`).
-/

@[expose] public section

open Causalean.Graph


namespace Causalean.Discovery.InvariantPrediction

open Causalean MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace EnvFamily

variable {ι : Type*} [Fintype ι]

/-- [The invariant predictor collection](goal) retains exactly the finite node sets observed
throughout [an environment family](hyp:F) and make the target's conditional law stable across its
[finite environments](hyp:ι), for [finite nodes](hyp:N) with [measurable coordinate
outcomes](hyp:Ω). -/
def invariantSets (F : EnvFamily N Ω ι) : Set (Set (SWIGNode N)) :=
  { T | ∃ (S : Finset (SWIGNode N)) (hS : ∀ i, S ⊆ (F.M i).observed),
      (↑S : Set (SWIGNode N)) = T ∧ F.Invariant S hS }

/-- [The ICP identified set](goal) contains precisely the nodes that survive every invariant
predictor specification admitted by [the environment family](hyp:F), over [finite nodes](hyp:N),
[finite environments](hyp:ι), and [measurable coordinate outcomes](hyp:Ω).

The **identified set** `S(E)`: the intersection of all invariant predictor
sets across the environment family. -/
def idSet (F : EnvFamily N Ω ι) : Set (SWIGNode N) := ⋂₀ F.invariantSets

/-- The identified set is contained in every invariant set. -/
theorem idSet_subset_of_mem (F : EnvFamily N Ω ι) {T : Set (SWIGNode N)}
    (hT : T ∈ F.invariantSets) : F.idSet ⊆ T :=
  Set.sInter_subset_of_mem hT

/-- [The target's observed parents belong to the invariant predictor collection](goal), so the ICP
intersection ranges over a causally sufficient candidate selected in [environment
`i₀`](hyp:i₀) of [family `F`](hyp:F), over [finite nodes](hyp:N), [finite
environments](hyp:ι), and [measurable coordinate outcomes](hyp:Ω). -/
theorem paObs_mem_invariantSets (F : EnvFamily N Ω ι) (i₀ : ι) :
    (↑(F.paObs i₀) : Set (SWIGNode N)) ∈ F.invariantSets :=
  ⟨F.paObs i₀, (fun j => F.paObs_subset_observed i₀ j), rfl, F.mechanism_invariant i₀⟩

end EnvFamily

end Causalean.Discovery.InvariantPrediction

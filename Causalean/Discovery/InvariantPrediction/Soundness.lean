/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.InvariantPrediction.IdentifiedSet

/-!
# Invariant Causal Prediction: soundness

This file proves the soundness theorem for invariant causal prediction:
`icp_sound` states that the identified set `S(E)` is contained in the target's
observed parents `PA(Y)`.  Thus every variable selected by ICP is a genuine
direct cause in the observed parent set.

This is a population set-inclusion consequence of the mechanism validity
represented by Proposition 1 in Peters–Bühlmann–Meinshausen. The parent set is
itself invariant (`paObs_mem_invariantSets`), and the ICP identified set is the
intersection of all invariant sets (`idSet_subset_of_mem`), so it must be
contained in the parents. The paper's Theorem 1 is a finite-sample coverage
result and is not asserted here.
-/

public section

open Causalean.Graph


namespace Causalean.Discovery.InvariantPrediction

open Causalean MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace EnvFamily

variable {ι : Type*} [Fintype ι]

/-- **Population ICP soundness from parent-set invariance.** For [an environment family](hyp:F) and [an index i₀ selecting
the target's observed-parent set](hyp:i₀), [the identified set is contained in the target's
observed parents: every node selected by ICP is a genuine direct cause](goal). -/
theorem icp_sound (F : EnvFamily N Ω ι) (i₀ : ι) :
    F.idSet ⊆ (↑(F.paObs i₀) : Set (SWIGNode N)) :=
  F.idSet_subset_of_mem (F.paObs_mem_invariantSets i₀)

end EnvFamily

end Causalean.Discovery.InvariantPrediction

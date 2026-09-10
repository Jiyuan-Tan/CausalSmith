/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Deterministic step kernel

For the factored construction of `jointKernel`, at step `n` the value of the
next observed node `v_n = M.observedAt ⟨n, hn⟩` is produced **deterministically**
from its parent tuple by the structural function `M.structFun v_n`.  We package
this as a `Kernel.deterministic` kernel whose source is the prefix state
`FixedValues M × OrderedLatentPrefixValues M n _` and whose target is
`swigΩ Ω v_n.val`.

## Main definitions

* `SCM.stepFun hn` — the deterministic assignment
  `structFun v_n ∘ parentValuesFromPrefix hn`.
* `SCM.measurable_stepFun hn` — its measurability.
* `SCM.stepKernel hn` — `Kernel.deterministic (stepFun hn) _`.
* `SCM.isMarkov_stepKernel hn` — the `IsMarkovKernel` instance.
-/

import Causalean.SCM.Factored.ParentLookup
import Mathlib.Probability.Kernel.Basic

/-! # Step Kernels for Observed Nodes

This file constructs the deterministic kernel that generates the next observed
coordinate from its fixed, latent, and previously generated observed parents.
The step kernels are the local transition pieces in the sequential
factorization of the joint kernel, and their measurability follows from the
parent-lookup map and the SCM structural-function measurability field. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. The deterministic step function and its measurability
-- ============================================================

/-- For [a structural causal model](hyp:M) and an index $n$ [for which at
    least $n+1$ observed vertices exist](hyp:hn), the [deterministic step
    function](goal) maps a fixed-value assignment together with the latent and
    already generated observed-prefix values to the value of the $n$-th
    observed vertex in the model's canonical topological order, by applying
    that vertex's structural function to the values of its parents. -/
noncomputable def stepFun (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    (M.FixedValues × M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn)) →
      swigΩ Ω (M.observedAt ⟨n, hn⟩).val :=
  fun sℓξ => M.structFun (M.observedAt ⟨n, hn⟩) (M.parentValuesFromPrefix hn sℓξ)

/-- Fix a structural causal model `M` and a step index `n` such that [there are
    at least `n + 1` observed nodes, so `n` names a valid position in the
    canonical topological order of observed nodes](hyp:hn). Then [the
    deterministic map `stepFun`, which produces the value of the `n`-th
    observed node by assembling its parent tuple from the fixed values,
    latent values, and previously generated observed prefix and applying the
    node's structural equation, is measurable](goal). -/
@[fun_prop]
theorem measurable_stepFun (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.stepFun hn) :=
  (M.structFun_measurable (M.observedAt ⟨n, hn⟩)).comp
    (M.measurable_parentValuesFromPrefix hn)

-- ============================================================
-- § 2. The step kernel
-- ============================================================

/-- For [a structural causal model](hyp:M) and an index $n$ [for which at
    least $n+1$ observed vertices exist](hyp:hn), the [step kernel](goal) is
    the probability kernel that assigns unit mass to the value of the $n$-th
    observed vertex produced by its structural function from the fixed values,
    latent values, and already generated observed-prefix values.

    Since the structural assignment is deterministic and measurable, this
    kernel is the corresponding Dirac kernel. -/
noncomputable def stepKernel (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    ProbabilityTheory.Kernel
      (M.FixedValues × M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn))
      (swigΩ Ω (M.observedAt ⟨n, hn⟩).val) :=
  ProbabilityTheory.Kernel.deterministic (M.stepFun hn) (M.measurable_stepFun hn)

/-- For [a finite node population with measurable value spaces](hyp:N,Ω), [a structural causal
model](hyp:M), [a nonnegative integer](hyp:n), and [proof that adding one to this integer does not
exceed the number of observed nodes](hyp:hn), [the Markov-kernel structure for the corresponding
deterministic step kernel](goal) asserts that the kernel assigning the next observed value from its
structural equation is a Markov kernel. -/
instance isMarkov_stepKernel (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    ProbabilityTheory.IsMarkovKernel (M.stepKernel hn) := by
  unfold stepKernel; infer_instance

end SCM

end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Recursive prefix kernel

For the factored construction of `jointKernel`, we assemble the prefix kernel
`jointKernelPrefix n hn : Kernel (FixedValues M) (OrderedLatentPrefixValues M n hn)`
by **sequential `compProd`** of the base latent kernel with the step kernels
`stepKernel` built in `Causalean.SCM.Factored.StepKernel`.

## Main definitions

* `SCM.jointKernelPrefixZero` — base case at `n = 0`: push the constant kernel at
  `latentProduct` through `ℓ ↦ (ℓ, PUnit.unit)`.
* `SCM.jointKernelPrefix` — recursive prefix kernel for each `n ≤ observed.card`.
* `SCM.isMarkov_jointKernelPrefixZero`, `SCM.isMarkov_jointKernelPrefix` — Markov
  instances at every step.
-/

import Causalean.SCM.Factored.StepKernel
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompProd

/-! # Prefix Kernels for Sequential Factorization

This file constructs the prefix kernels that generate latent variables and then
observed variables sequentially along a topological order. These kernels are the
recursive components used to express the structural-model joint kernel as a
Markov factorization, with Markov-kernel instances for the base and recursive
cases. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Latent constant kernel (shorthand)
-- ============================================================

/-- For [a finite collection of nodes with a measurable outcome space for each node](hyp:N,Ω)
    and [a structural causal model](hyp:M), the [kernel giving the distribution of the latent-node
    values conditional on the fixed-node values](goal) assigns the same latent product
    distribution to every fixed-node assignment.

    The latent product law as a kernel indexed by fixed values.  Ignores the
    fixed input and always returns the product distribution `latentProduct`.
    Shorthand for readability of the recursion below. -/
noncomputable def latentKernelOnFixed (M : Causalean.SCM N Ω) :
    ProbabilityTheory.Kernel M.FixedValues M.LatentValues :=
  ProbabilityTheory.Kernel.const _ M.latentProduct

/-- For [a finite collection of nodes with measurable value spaces](hyp:N,Ω) and [a structural
causal model](hyp:M), [the Markov-kernel structure for the constant latent-value kernel](goal)
asserts that the kernel assigning the latent product distribution to every fixed-value assignment
is a Markov kernel. -/
instance isMarkov_latentKernelOnFixed (M : Causalean.SCM N Ω) :
    ProbabilityTheory.IsMarkovKernel M.latentKernelOnFixed := by
  unfold latentKernelOnFixed; infer_instance

-- ============================================================
-- § 2. Base prefix kernel at `n = 0`
-- ============================================================

/-- For [a finite collection of nodes with a measurable outcome space for each node](hyp:N,Ω)
    and [a structural causal model](hyp:M), the [zero-step prefix kernel](goal) maps every
    fixed-node assignment to the joint distribution of all latent-node values and the unique
    empty observed-node prefix [at prefix length zero](step:1).

    Base case of the recursive prefix kernel: only the latent variables have been
    generated so far, paired with the trivial `PUnit` observed prefix.

    Concretely: the constant kernel at `latentProduct`, pushed through
    `ℓ ↦ (ℓ, PUnit.unit)`.  Note `ObservedPrefixValues M 0 _ = PUnit.{uΩ + 1}`. -/
noncomputable def jointKernelPrefixZero (M : Causalean.SCM N Ω) :
    ProbabilityTheory.Kernel M.FixedValues
      (M.OrderedLatentPrefixValues 0 (Nat.zero_le _)) :=
  M.latentKernelOnFixed.map (fun ℓ => (ℓ, (PUnit.unit : PUnit.{uΩ + 1})))

/-- For [a finite collection of nodes with measurable value spaces](hyp:N,Ω) and [a structural
causal model](hyp:M), [the Markov-kernel structure for the zero-step prefix kernel](goal) asserts
that the kernel generating the latent values and the empty observed prefix is a Markov kernel. -/
instance isMarkov_jointKernelPrefixZero (M : Causalean.SCM N Ω) :
    ProbabilityTheory.IsMarkovKernel M.jointKernelPrefixZero := by
  unfold jointKernelPrefixZero
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map
    M.latentKernelOnFixed (by fun_prop)

-- ============================================================
-- § 3. Recursive prefix kernel
-- ============================================================

/-- For [a finite collection of nodes with a measurable outcome space for each node](hyp:N,Ω),
    [a structural causal model](hyp:M), [a nonnegative integer](hyp:n), and [proof that this
    integer does not exceed the number of observed nodes](hyp:hn), the [prefix kernel](goal)
    maps each fixed-node assignment to the joint distribution of all latent-node values and the
    values of the first specified number of observed nodes.  [At zero observed nodes it is the
    zero-step prefix kernel](step:1); [at each positive prefix length it extends the preceding
    prefix distribution by the next observed node's deterministic structural equation](step:2).

    The prefix kernel at level `n`: sends fixed values `s` to the joint law of
    the latent tuple together with the values of the first `n` observed nodes,
    built by sequential `compProd` with the deterministic `stepKernel`s.

    Base case: `n = 0` returns `jointKernelPrefixZero`.
    Step case: `jointKernelPrefix (k+1) hn =
      ((jointKernelPrefix k _) ⊗ₖ stepKernel hn).map (extendOrderedLatentPrefix hn)`. -/
noncomputable def jointKernelPrefix (M : Causalean.SCM N Ω) :
    (n : ℕ) → (hn : n ≤ M.observed.card) →
      ProbabilityTheory.Kernel M.FixedValues (M.OrderedLatentPrefixValues n hn)
  | 0, _ => M.jointKernelPrefixZero
  | k + 1, hn =>
      ((M.jointKernelPrefix k (Nat.le_of_succ_le hn)) ⊗ₖ (M.stepKernel hn)).map
        (M.extendOrderedLatentPrefix hn)

/-- For [a finite collection of nodes with measurable value spaces](hyp:N,Ω), [a structural
causal model](hyp:M), [a nonnegative integer](hyp:n), and [proof that this integer does not exceed
the number of observed nodes](hyp:hn), [the Markov-kernel structure for the corresponding prefix
kernel](goal) asserts that the kernel generating all latent values and the first specified observed
values is a Markov kernel. -/
instance isMarkov_jointKernelPrefix (M : Causalean.SCM N Ω) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      ProbabilityTheory.IsMarkovKernel (M.jointKernelPrefix n hn)
  | 0, _ => M.isMarkov_jointKernelPrefixZero
  | k + 1, hn => by
      letI := M.isMarkov_jointKernelPrefix k (Nat.le_of_succ_le hn)
      letI := M.isMarkov_stepKernel hn
      change ProbabilityTheory.IsMarkovKernel
        (((M.jointKernelPrefix k (Nat.le_of_succ_le hn)) ⊗ₖ
          (M.stepKernel hn)).map (M.extendOrderedLatentPrefix hn))
      exact ProbabilityTheory.Kernel.IsMarkovKernel.map
        ((M.jointKernelPrefix k (Nat.le_of_succ_le hn)) ⊗ₖ (M.stepKernel hn))
        (M.measurable_extendOrderedLatentPrefix hn)

end SCM

end Causalean

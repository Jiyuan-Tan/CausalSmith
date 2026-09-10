/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM

/-! # Prefix States for Factored Kernels

This file builds the finite prefix state spaces used to construct a structural
causal model's joint kernel sequentially along a topological ordering. The
definitions package latent values together with already generated observed values,
with measurability facts for the downstream factored-kernel construction.
-/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Observed prefix values
-- ============================================================

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a natural number $n$ no greater
than its number of observed nodes](hyp:n), the [observed-prefix value space](goal)
is [the one-point space of the empty assignment when $n=0$](step:1), and the
product of the preceding prefix space and the value space of the $n$-th observed
node when $n$ is positive. -/
def ObservedPrefixValues (M : Causalean.SCM N Ω) :
    (n : ℕ) → n ≤ M.observed.card → Type _ :=
  fun n hn =>
    match n with
    | 0 => PUnit.{uΩ + 1}
    | k + 1 => ObservedPrefixValues M k (Nat.le_of_succ_le hn) ×
        swigΩ Ω (M.observedAt ⟨k, hn⟩).val

/-- For [a finite, distinguishable node population with measurable node-value spaces](hyp:N,Ω), [a structural causal model](hyp:M), and [any natural number no greater than the number of its observed nodes](hyp:n,hn), the [measurable-space structure on the corresponding observed-prefix value space](goal) is provided [by the one-point measurable space for a zero-length prefix](step:1) and [by the product measurable space for a positive-length prefix](step:2).

This structure is constructed by the same recursion as the observed-prefix value space. -/
noncomputable instance instMeasurableSpaceObservedPrefixValues (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card), MeasurableSpace (M.ObservedPrefixValues n hn)
  | 0, _ => by
      dsimp [ObservedPrefixValues]
      infer_instance
  | k + 1, hn => by
      dsimp [ObservedPrefixValues]
      letI := instMeasurableSpaceObservedPrefixValues (M := M) (hn := Nat.le_of_succ_le hn)
      infer_instance

/-- Random values consisting of the latent tuple paired with an observed prefix.
    This is the state-space of the kernel at step `n` in the factored construction. -/
abbrev OrderedLatentPrefixValues (M : Causalean.SCM N Ω) (n : ℕ)
    (hn : n ≤ M.observed.card) :=
  LatentValues M × ObservedPrefixValues M n hn

-- ============================================================
-- § 2. Coordinate reader on an observed prefix
-- ============================================================

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a prefix length no greater than
the number of its observed nodes](hyp:n), an assignment on that prefix,
and [a position within the prefix](hyp:i), the [observed-prefix coordinate
reader](goal) [has no value when the prefix is empty](step:1), and [otherwise
returns the assigned value at that position, reading recursively from the
preceding prefix or directly from its final coordinate](step:2). -/
noncomputable def observedPrefixValue (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card),
      M.ObservedPrefixValues n hn →
      (i : Fin n) →
        swigΩ Ω (M.observedAt ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩).val
  | 0, _, _, i => Fin.elim0 i
  | k + 1, hn, ξ, i =>
      Fin.lastCases
        (by simpa using ξ.2)
        (fun j => by
          simpa using M.observedPrefixValue (Nat.le_of_succ_le hn) ξ.1 j)
        i

/-- `observedPrefixValue` is measurable in its prefix-state argument. -/
@[fun_prop]
theorem measurable_observedPrefixValue (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card) (i : Fin n),
      Measurable (fun ξ : M.ObservedPrefixValues n hn => M.observedPrefixValue hn ξ i)
  | 0, _, i => Fin.elim0 i
  | k + 1, hn, i =>
      Fin.lastCases
        (by
          have h : Measurable
              (fun ξ : M.ObservedPrefixValues k (Nat.le_of_succ_le hn) ×
                swigΩ Ω (M.observedAt ⟨k, hn⟩).val => ξ.2) := measurable_snd
          simp only [SCM.observedPrefixValue, Fin.lastCases_last]
          exact h)
        (fun j => by
          have h : Measurable
              (fun ξ : M.ObservedPrefixValues k (Nat.le_of_succ_le hn) ×
                swigΩ Ω (M.observedAt ⟨k, hn⟩).val =>
                M.observedPrefixValue (Nat.le_of_succ_le hn) ξ.1 j) :=
            (M.measurable_observedPrefixValue (Nat.le_of_succ_le hn) j).comp measurable_fst
          simp only [SCM.observedPrefixValue, Fin.lastCases_castSucc]
          exact h)
        i

-- ============================================================
-- § 3. Extending a prefix state by one position
-- ============================================================

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a natural number $n$](hyp:n), and [evidence
that the model has at least $n+1$ observed nodes](hyp:hn), the [ordered-latent
prefix extension map](goal) takes a latent assignment, an assignment to the
first $n$ observed nodes, and the value of the next observed node, and returns
[the same latent assignment paired with the resulting length-$n+1$ observed prefix](step:1).

Append the next observed value to an ordered-latent prefix state.  This is the
    state-space normalization map used after one `compProd` step in the factored
    construction: `((ℓ, ξ), y) ↦ (ℓ, (ξ, y))`. -/
def extendOrderedLatentPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    (M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) ×
      swigΩ Ω (M.observedAt ⟨n, hn⟩).val) →
      M.OrderedLatentPrefixValues (n + 1) hn
  | ((ℓ, ξ), y) => (ℓ, (ξ, y))

/-- Fix a structural causal model `M` and a step index `n` such that [there are
    at least `n + 1` observed nodes, so `n` names the next node to be appended
    in the canonical topological order of observed nodes](hyp:hn). Then [the
    map that appends the freshly generated value of that node to a length-`n`
    prefix of previously observed values, together with the latent
    assignment, producing a length-`(n + 1)` prefix, is measurable](goal). -/
@[fun_prop]
theorem measurable_extendOrderedLatentPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.extendOrderedLatentPrefix hn) :=
  Measurable.prodMk (measurable_fst.comp measurable_fst)
    (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd)

end SCM

end Causalean

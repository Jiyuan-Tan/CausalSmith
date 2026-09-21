# Substrate requirement: chunked-finite-interval-certificates

## Goal
Build reusable Lean substrate for axiom-free, memory-bounded verification of large exact-rational finite-array interval recurrences by independently checked chunks.

## Provides (API contract)
- A proof-producing certificate API for finite vectors/matrices of rational intervals whose scalar leaves are independently kernel-checked.
- A chunked finite-sum checker and soundness theorem that combines bounded-size exact-rational dot-product chunks into a full coordinate result.
- A coordinatewise finite-array recurrence certificate and soundness theorem that composes opaque verified coordinate/chunk leaves across finitely many steps.
- An adapter usable with the existing `FiniteIterateCertificate` and stationary-reward interval theorems under `Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation`.
- Verification cost and kernel-memory peak must be bounded by the selected chunk size rather than by reducing one whole-program Boolean over every coordinate and recurrence step.

## Statement / milestones
Given caller-supplied exact rational interval matrix/vector data, a finite sequence of interval-vector iterates, and for every output coordinate a partition of the dot product into bounded chunks with checked rational bounds, prove that every recurrence step is sound. Combine those coordinate theorems into the existing finite-iterate certificate interface and hence permit downstream stationary expectation enclosure proofs.

The checker must remain axiom-free under `#print axioms`: it may use `norm_num`, `decide +kernel`, or ordinary opaque theorem composition on small leaves, but never `native_decide`, `ofReduceBool`, generated native axioms, untrusted external computation, or a monolithic Boolean whose kernel reduction recreates the full large array computation.

## Standard reference
Proof-by-reflection with small proof-producing certificates, exact interval arithmetic, chunked finite sums/dot products, and compositional verification of finite recurrence traces.

## Intended reuse
Large finite-state Markov reward and stationary-expectation certificates, including the immediate `insulinGrid_bias_certificate` consumer. The reusable API must be generic in finite index types and rational interval data; the paper-specific 360-state kernels, CDF table, 20-step traces, and final strict inequality remain in the research module.

## May assume / must derive
May assume caller-supplied exact rational arrays, chunk partitions, intermediate chunk bounds, and small scalar equalities/inequalities accompanied by ordinary Lean proofs. Must derive soundness of chunk concatenation, finite-sum/dot-product assembly, coordinatewise recurrence assembly, interval containment propagation, and the adapter to existing finite-iterate certificates.

## Non-goals (optional)
Do not embed or generate the insulin model's endpoint table, 360-state kernels, recurrence arrays, rewards, or final bias constants. Do not use `native_decide` or any axiom-producing compiled evaluator. Do not import CausalSmith research modules. Do not duplicate the existing stationary-distribution, stationary-reward, normal-CDF, or general interval-matrix semantics; extend them with a memory-bounded certificate layer.

## Known building blocks (optional)
Deduplicate against `Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation`, especially its interval matrix/vector operations, checked iterates, `FiniteIterateCertificate`, and stationary expectation soundness. Reuse Mathlib finite sums, arrays/vectors, interval containment, and `norm_num`-friendly rational arithmetic.

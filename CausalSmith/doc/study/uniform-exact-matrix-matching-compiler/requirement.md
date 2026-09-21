# Substrate requirement: uniform-exact-matrix-matching-compiler

## Goal

Build reusable, axiom-clean Lean infrastructure for a uniform exact-arithmetic register program that extends and inverts a full-row-rank matrix, extracts a deleted-row kernel block, computes matching/path-flip data from its nonzero pattern, and certifies rationality and an eventual cubic operation bound.

## Provides (API contract)

Expose neutral declarations under an appropriate `Causalean.Mathlib.LinearAlgebra` or `Causalean.Combinatorics` namespace for dimensions `2 ≤ p ≤ n`, an exact real `p × n` matrix `C` of full row rank, and a distinguished row `x : Fin p`:

- A deterministic exact Gaussian-elimination/pivoting construction of an invertible `n × n` basis extension whose observed rows are exactly `C`, together with its inverse.
- An inverse-derived kernel block and a theorem that it spans the kernel of `C` with row `x` deleted.
- A column-saturating matching in the relevant finite bipartite nonzero-pattern graph.
- An alternating-reachability forest enumerating every row that can be left unmatched, with a certified alternating path-flip operation for each such row.
- A neutral finite exact-arithmetic/register-program representation with explicit output-register maps and an execution theorem returning the advertised matrix, inverse, support/matching indicators, and path-flip data.
- Rational-input preservation for every emitted matrix/register value.
- An eventual uniform `O(n^3)` operation bound with an existential global constant and threshold.

Names may follow library style. The consumer must be able to instantiate the API without importing any `CausalSmith/*_Research` module.

## Statement / milestones

1. From full row rank of `C`, deterministically select pivots and extend its `p` rows to a basis of `ℝ^n`; expose the resulting square matrix `B`, prove its first/observed rows equal `C`, prove `B` invertible, and expose its inverse.
2. Define the block extracted from `B⁻¹` appropriate to deleting row `x`; prove every emitted vector lies in the deleted-row kernel and that the block spans that kernel.
3. On the finite bipartite graph induced by the relevant nonzero pattern, construct and certify one column-saturating matching.
4. Construct an alternating-reachability forest from unmatched vertices. Prove that it enumerates every row that can be left unmatched and provide a verified path-flip producing the corresponding matching.
5. Compile the construction into a uniform finite register program whose only external numerical inputs are the entries of `C`. Give explicit register maps and prove execution yields all advertised outputs.
6. Prove every output is rational when all entries of `C` are rational.
7. Prove an eventual cubic cost theorem of the form `∃ K N, ∀ n ≥ N, cost n ≤ K * n^3` (or an equivalent ordinary asymptotic `O(n^3)` formulation). It must not demand the bound at every small dimension.

The theorem may use a clean modular interface separating linear algebra, matching, execution, rationality, and complexity, provided one consumer-facing theorem assembles the pieces.

## Standard reference

Gaussian elimination with deterministic pivoting, basis extension, inverse-based kernel bases, and augmenting-path matching algorithms are standard finite-dimensional linear algebra and bipartite matching constructions. The novelty here is their reusable, execution-linked exact-arithmetic formalization rather than a new mathematical algorithm.

## Intended reuse

The immediate consumer is `shared_kernel_matching_certificate` in the exact-identifiability paper's `Helpers/KernelMatching.lean`. That consumer will compose this input-only compiler with paper-specific completion fibers, causal effects, and the dense-output lower bound. The substrate should remain reusable for other exact matrix algorithms and finite matching certificates.

## May assume / must derive

May assume the dimension inequalities, full row rank, and exact real inputs. May use Mathlib finite-dimensional linear algebra, matrix nonsingular-inverse and pivot/transvection results, finite graph matching/Hall results, and study-local helper modules. Must derive deterministic construction, output correctness, deleted-row kernel spanning, matching and path-flip correctness, input-only execution linkage, rational preservation, and the eventual cubic cost theorem. Do not introduce axioms, opaque gates, or `sorry`.

## Non-goals

- Do not mention or encode causal `CompletionFiber`, admissible sources, interventions, effects, law fibers, or the paper's dense-output lower bound.
- Do not import any `CausalSmith/*_Research` module.
- Do not prove the paper's headline certificate theorem.
- If compatibility with the paper-local instruction syntax is useful, extract a neutral equivalent into Causalean and leave the adapter/composition to the consumer.

## Known building blocks

- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
- Matrix pivot/transvection infrastructure, especially `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`; this is existence-level and does not itself provide the required executable compiler or output linkage.
- `Mathlib.Combinatorics.SimpleGraph.Hall` and finite matching/path APIs.
- Existing Causalean exact-arithmetic or register-machine infrastructure, if available; otherwise introduce only a neutral reusable machine.

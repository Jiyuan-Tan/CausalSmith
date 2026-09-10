# Uniform exact matrix-and-matching compiler

Develop reusable, axiom-clean Lean infrastructure for a uniform exact-arithmetic register program
implementing the following finite-dimensional construction.

For dimensions `2 ≤ p ≤ n`, an exact real `p × n` matrix `C` of full row rank, and a distinguished
row `x : Fin p`, the program must use only entries of `C` as external numerical inputs and:

- construct an invertible `n × n` basis extension whose observed rows are exactly `C`, together with
  its inverse, by a deterministic Gaussian-elimination/pivoting procedure;
- expose the kernel block obtained from the inverse and certify that it spans the kernel of `C` with
  row `x` deleted;
- construct one column-saturating matching in the relevant finite bipartite nonzero-pattern graph and
  an alternating-reachability forest that enumerates every row which can be left unmatched, with a
  certified path-flip operation for each such row;
- compile these operations to a uniform finite exact-arithmetic/register program with explicit output
  register maps and a proof that execution returns the advertised matrix entries, inverse entries,
  support/matching indicators, and path-flip data;
- prove an eventual uniform `O(n^3)` operation bound with an existential global constant and threshold;
  the threshold semantics must match ordinary asymptotic big-O rather than demanding the bound at every
  finite `n`;
- prove rational-input preservation for every emitted matrix/register value.

The reusable theorem should keep the generic linear-algebra and finite-matching outputs separate from
paper-specific causal completion matrices. It need not mention intervention effects, law fibers,
admissible sources, or the paper's dense-output lower bound; those are consumer-side consequences.

Suggested imports include `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, matrix pivot/transvection
results, `Mathlib.Combinatorics.SimpleGraph.Hall`, and finite matching/path APIs. The closest existing
result found was `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`; it proves an
existence-level elimination factorization but does not supply an executable input-only register program,
output linkage, matching forest, path flips, rationality preservation, or a cubic cost theorem.

Use only Mathlib, Causalean, and study-local prerequisites. Do not import any
`CausalSmith/*_Research` module. If the paper-local exact-instruction syntax is needed for compatibility,
extract a neutral equivalent into Causalean and provide an adapter-level API; do not encode the paper's
headline certificate theorem itself as substrate.

# Substrate requirement: johnson-kneser-spectral-decomposition

## Goal
Build a reusable, axiom-free Lean realization of the orthogonal Johnson harmonic
decomposition on the uniform finite slice and the Kneser disjointness operator's
eigenvalue on every harmonic degree.

## Provides (API contract)
- A degree-at-most-`k` inclusion-monomial subspace for real functions on
  `Omega n M = {A : Finset (Fin n) // A.card = M}`.
- Canonical degree-`k` Johnson harmonic subspaces and linear orthogonal projections
  onto them, for `k : Fin (M+1)` and `M ≤ n`.
- A projection/decomposition theorem: linearity and range/fixed-point properties,
  residual orthogonality, pairwise orthogonality of distinct positive degrees, and
  completeness of the centered part `f - mean(f)` as the sum of degrees `1..M`.
- The unnormalized Kneser adjacency sum over disjoint `M`-subsets and a theorem that
  its restriction to degree `k` has eigenvalue
  `(-1)^k * choose (n-M-k) (M-k)` under `2*M ≤ n`.
- A normalized corollary for division by `choose (n-M) M`, preferably expressed as
  `(-1)^k * M.descFactorial k / (n-M).descFactorial k` when denominators are nonzero.

## Statement / milestones
For `2*M ≤ n`, construct the canonical orthogonal projection family on real-valued
functions over the uniform `M`-slice. Prove that every centered slice function is
the finite sum of its positive-degree projected components, those components are
pairwise orthogonal under the uniform slice inner product, and the Kneser adjacency
operator acts on the degree-`k` component by the classical eigenvalue above. Include
the degree-zero/mean case needed to state a complete decomposition cleanly.

## Standard reference
Filmus, *An orthogonal basis for functions over a slice of the Boolean hypercube*,
Electronic Journal of Combinatorics 23(1), 2016, Theorem 4.1 and Lemma 4.3
(arXiv:1406.0142v2). Brouwer, Cioabă, Ihringer, and McGinnis, *The smallest
eigenvalues of Hamming graphs, Johnson graphs and other distance-regular graphs
with classical parameters*, Journal of Combinatorial Theory A 153 (2018),
Proposition 3.1 (arXiv:1709.09011), for the Kneser eigenvalues.

## Intended reuse
Randomized grouping and finite-population covariance calculations consume it, but
the API must remain generic finite combinatorics/linear algebra: no experiment,
potential-outcome, CR2, paper-qid, or run-specific types. It should support any real
function on a uniform finite slice and be reusable for Johnson/Kneser arguments.

## May assume / must derive
May assume Mathlib's finite-dimensional real inner-product/projection machinery,
finite-set counting identities, and standard binomial/falling-factorial algebra.
May assume only the explicit size hypotheses (`M ≤ n` or `2*M ≤ n`) needed for a
statement. Must derive the Johnson subspace decomposition, canonical projection
properties, cross-degree orthogonality/completeness, and Kneser action/eigenvalues;
do not expose these conclusions as structure fields, axioms, theorem parameters, or
unproved cited gates.

## Non-goals (optional)
No asymptotics, causal estimands, randomized-experiment variance theorem, CR2
software identity, or paper-specific covariance bridge. Complex-valued harmonic
analysis and the spectra of unrelated association schemes are out of scope.

## Known building blocks (optional)
Mathlib finite-dimensional submodules and orthogonal projections
(`Submodule.orthogonalProjection`, `OrthogonalFamily.decomposition` where useful),
`Finset.powersetCard`, `Nat.choose`, and existing uniform finite-design/slice-inner-
product infrastructure if it is already generic and introduces no paper import.

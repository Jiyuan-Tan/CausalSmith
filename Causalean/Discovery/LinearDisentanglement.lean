/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Identifiability
public import Causalean.Discovery.LinearDisentanglement.Quantitative
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence


/-!
# Linear causal disentanglement via interventions — umbrella

Entry point for the formalization of Squires, Seigal, Bhate & Uhler, *Linear Causal
Disentanglement via Interventions* (ICML 2023, `arXiv:2211.16467`).  Import this file to
get the whole development; the headline results are listed here so the main theorem is not
buried among the supporting linear-algebra files.

## Main results

* `Solution` (`Model.lean`) — the model: `d` latent variables following a linear SEM,
  observed only through a full-rank mixing `X = G Z`, with one perfect single-node
  intervention per context; the observable content is the precision matrices
  `Θ_k = Hᵀ Bₖᵀ Bₖ H`.
* `disentanglement_identifiability_up_to_signed_scaling_of_nondegenerate`
  (`Identifiability.lean`) — an unnormalized matrix-level uniqueness result. With one
  intervention per latent node and an explicit nondegeneracy hypothesis, two solutions
  with the same `{Θ_k}` are related by a single order-preserving relabeling `σ ∈ S(𝒢)` and
  nonzero signed diagonal scalings. Unlike the paper's Theorem 2, this model does not impose
  its row normalization and therefore does not reduce the ambiguity to permutations alone.
* `sigma_solutions` (`SigmaSolutions.lean`) — the `(⊇)` direction: every `σ ∈ S(𝒢)` yields a
  solution with the same precision matrices. This constructs the pure-permutation subclass;
  it is not a converse for every signed-scaling ambiguity allowed by the uniqueness theorem.

## Supporting machinery

`KeyIdentity.lean` (the rank-one precision-difference identity), `Rowspan.lean` (Lemma 1,
linking precision differences to the latent graph), `PartialOrderRQ.lean` (the partial-order
RQ decomposition), `Uniqueness.lean` (the orthogonal-correctness assembly), and
`Causalean/Mathlib/LinearAlgebra/Cholesky.lean` (real Cholesky existence/uniqueness).
The non-Gaussianity engine and LiNGAM development are **not** used here;
disentanglement proceeds through interventions, second moments, and the stated
linear-algebra machinery.
-/

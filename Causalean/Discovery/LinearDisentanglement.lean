/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Uniqueness
public import Causalean.Discovery.LinearDisentanglement.Quantitative
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence


/-!
# Linear causal disentanglement via interventions

Identifiability of latent causal variables that follow a linear structural equation model and are
observed only through an unknown full-rank linear mixing, from the precision matrices of one
observational and several single-node interventional contexts, after Squires, Seigal, Bhate &
Uhler, *Linear Causal Disentanglement via Interventions* (ICML 2023, `arXiv:2211.16467`). With one
intervention per latent node and every interventional precision matrix different from the
observational one, two solutions with the same precision matrices differ only by a relabeling of
the latent variables that preserves the causal order and by nonzero signed rescalings; conversely
every order-preserving relabeling of a solution reproduces the same precision matrices. The model
here does not impose the paper's row normalization, so the ambiguity is not reduced to
relabelings alone. Separately, for the matrix problem of finding one B with B·Aₑ·Bᵀ diagonal for
every environment e, the development proves explicit perturbation bounds ‖B − B₀‖ ≤ C·ε and a
non-uniqueness construction when two coordinates of the diagonal shifts are affinely collinear.

## Main results

* `Solution` (`Model.lean`) — the model: `d` latent variables following a linear SEM,
  observed only through a full-rank mixing `X = G Z`, with one perfect single-node
  intervention per context; the observable content is the precision matrices
  `Θ_k = Hᵀ Bₖᵀ Bₖ H`.
* `disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate`
  (`Uniqueness_Part4.lean`) — an unnormalized matrix-level uniqueness result. With one
  intervention per latent node and an explicit nondegeneracy hypothesis, two solutions
  with the same `{Θ_k}` are related by a single order-preserving relabeling `σ ∈ S(𝒢)` and
  nonzero signed diagonal scalings. Unlike the paper's Theorem 2, this model does not impose
  its row normalization and therefore does not reduce the ambiguity to permutations alone.
* `sigma_solutions` (`SigmaSolutions.lean`) — the `(⊇)` direction: every `σ ∈ S(𝒢)` yields a
  solution with the same precision matrices. This constructs the pure-permutation subclass;
  it is not a converse for every signed-scaling ambiguity allowed by the uniqueness theorem.
* `opNorm_sub_le_of_approximate_simultaneous_congruence` (`Quantitative/`) and
  `opNorm_sub_le_of_pairwise_affine` (`SimultaneousCongruence/`) — stability of a simultaneous
  congruence: a unit-diagonal candidate whose congruence residual is at most a small ε lies within
  an explicit constant times ε of the exact reference in operator norm.
* `exists_collinear_simultaneous_congruence_ambiguity` (`SimultaneousCongruence/Main.lean`) — if two
  coordinates of all diagonal shifts lie on one affine line, arbitrarily close distinct
  representations of the same covariance family exist.

## Supporting machinery

`KeyIdentity.lean` (the rank-one precision-difference identity), `Rowspan.lean` (Lemma 1,
linking precision differences to the latent graph), `PartialOrderRQ.lean` (the partial-order
RQ decomposition), `Uniqueness.lean` (the orthogonal-correctness assembly), and
`Causalean/Mathlib/LinearAlgebra/Cholesky.lean` (real Cholesky existence/uniqueness).
The non-Gaussianity engine and LiNGAM development are **not** used here;
disentanglement proceeds through interventions, second moments, and the stated
linear-algebra machinery.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part1
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part2
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part3
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part4
public import Mathlib.Data.Real.StarOrdered
/-!
# Conditional uniqueness for unnormalized linear disentanglement

Uniqueness of the linear causal disentanglement model up to relabeling and signed scaling. Let two
solutions each have one single-node intervention per latent variable, and let every interventional
precision matrix of the first differ from its observational precision matrix. If the two
solutions have the same observational and the same interventional precision matrices, then there
are a permutation σ of the latent coordinates that preserves the causal order, a vector μ of
nonzero scalings and a vector ν of signs such that the second mixing matrix is diag(μ)·P_σ times
the first, the structural matrices satisfy B'·diag(μ)·P_σ = diag(ν)·P_σ·B in every context, and σ
maps the first solution's intervention targets to the second's. The model does not impose a row
normalization, so the conclusion is weaker than a permutation-only statement.

## Contents

* `Uniqueness_Part1` — invertibility of the structural and latent Gram matrices, the change of
  basis H' = M·H (`exists_change_of_basis`), and the Gram identities it implies.
* `Uniqueness_Part2` — a diagonal conjugation identity, orthogonality of the per-context
  transition, and signed Cholesky uniqueness.
* `Uniqueness_Part3` — the change of basis is a scaled permutation that respects the graph order
  (`exists_orderPerm`).
* `Uniqueness_Part4` — the theorem
  `disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate`.
-/

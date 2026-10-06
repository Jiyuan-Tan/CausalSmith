/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Uniqueness

/-!
# Linear causal disentanglement: conditional uniqueness up to relabeling and signed scaling

An unnormalized matrix-level relaxation inspired by Squires, Seigal, Bhate & Uhler,
*Linear Causal Disentanglement via Interventions* (ICML 2023). This is not a
formalization of the paper's Theorem 2: `Solution` omits the row normalization in
Assumption 1(c), and the result below assumes intervention nondegeneracy separately.

Under the encoded linear model and perfect-intervention equations, plus one
intervention per latent node and explicit nondegeneracy, the latent graph and
intervention targets are unique up to `S(𝒢)`, the order-preserving relabelings,
while the latent directions are unique only up to nonzero signed diagonal scaling.

`sigma_solutions` separately shows that order-preserving permutations produce
observationally equivalent solutions. It does not construct every signed-scaling
ambiguity permitted by the conclusion below, so these results do not establish a
full orbit characterization for this unnormalized model.
-/

public section

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-- **Conditional unnormalized uniqueness up to signed scaling.** Let `S` and `S'`
be two solutions of the linear causal disentanglement model such that [each solution's
intervention-target map is a bijection onto the latent coordinates, i.e. one
intervention per latent node](hyp:hcov,hcov') and [`S`'s interventions are
non-degenerate: every intervened
precision matrix `Θ_k` differs from the observational precision matrix
`Θ_0`](hyp:hNondeg). If [`S` and `S'` share the same observational precision
matrix](hyp:hΘ0) and [agree, context by context, on every interventional precision
matrix](hyp:hΘ), then [`S` and `S'` are related by a single order-preserving
relabeling `σ` of the latent coordinates, a nonzero scaling vector `μ`, and a `±1`
sign vector `ν`: `σ`, `μ`, `ν` transport `S`'s latent-direction matrix and structural
coefficient matrices onto `S'`'s, and `σ` carries `S`'s intervention targets onto
`S'`'s](goal). -/
theorem disentanglement_identifiability_up_to_signed_scaling_of_nondegenerate
    (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      S'.H = Matrix.diagonal μ * permMat σ * S.H ∧
      S'.B0 * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) :=
  disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate
    S S' hcov hcov' hNondeg hΘ0 hΘ

end Causalean.Discovery.LinearDisentanglement

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Rowspan
public import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part1
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part2
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part3
public import Causalean.Mathlib.LinearAlgebra.Cholesky
public import Mathlib.Data.Real.StarOrdered

/-!
# Linear causal disentanglement: conditional unnormalized uniqueness, part 4

This final proof file packages the geometric collapse from `Uniqueness_Part3` as
conditional unnormalized uniqueness up to an order-preserving relabeling and
signed diagonal scaling. It contains only the public theorem that substitutes the
monomial change of basis into the latent-direction and structural-matrix relations.

The result is weaker than the normalized permutation-only conclusion of the
paper's Theorem 2. The complete route is summarized in `Uniqueness`.
-/

public section

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-! ### Final conditional uniqueness theorem -/
/-- **Conditional unnormalized uniqueness up to signed scaling.** Let [two solutions `S` and
`S'`](hyp:S,S') of the linear causal disentanglement model have [intervention-target maps
that are bijections onto the latent coordinates, i.e. one intervention per latent
node](hyp:hcov,hcov') and suppose [`S`'s interventions are non-degenerate: every
intervened precision matrix `Θ_k` differs from the observational precision matrix
`Θ_0`](hyp:hNondeg). If [`S` and `S'` share the
same observational precision matrix](hyp:hΘ0) and [agree, context by context, on
every interventional precision matrix](hyp:hΘ), then [`S` and `S'` are related by a
single order-preserving relabeling `σ` of the latent coordinates, a nonzero scaling
vector `μ`, and a `±1` sign vector `ν`, transporting `S`'s latent-direction and
structural coefficient matrices onto `S'`'s, with `σ` carrying `S`'s intervention
targets onto `S'`'s](goal).

The proof is the clean orthogonal-matrix route:
(L1) `H' = M H` for an invertible `M` (`exists_change_of_basis`, from rowspace equality
forced by `Θ₀ = Θ₀'`); (L2) the per-context Gram identity `BᵀB = (B'M)ᵀ(B'M)`
(`gram_identity`); (L3) hence `Oₖ = B'ₖ M Bₖ⁻¹` is orthogonal (`gram_to_orthogonal`);
(L4) the orthogonal-correctness collapse to a single order-preserving permutation
(`exists_orderPerm`, the geometric core); (L5) the signed conclusion is obtained by
substituting the monomial form of `M`. -/
theorem disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate
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
      (∀ k, S'.target k = σ (S.target k)) := by
  -- (L1) recover the invertible change-of-basis `M` with `H' = M H`.
  obtain ⟨M, _, hM⟩ := exists_change_of_basis S S' hΘ0
  -- (L4) the orthogonal-correctness collapse (the isolated hard core).
  obtain ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel, htarget⟩ :=
    exists_orderPerm S S' hcov hcov' hNondeg hΘ0 hΘ hM
  refine ⟨σ, μ, ν, hσ, hμ, hν, ?_, ?_, ?_, htarget⟩
  · -- `H' = diagonal μ permMat σ H`.
    rw [hM, hMeq]
  · -- Signed observational relation after substituting `M`.
    rwa [hMeq] at hB0rel
  · -- Signed interventional relations after substituting `M`.
    intro k
    rw [← hMeq]
    exact hBintrel k

end Causalean.Discovery.LinearDisentanglement

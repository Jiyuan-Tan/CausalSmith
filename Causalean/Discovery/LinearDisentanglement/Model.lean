/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

/-!
# Linear causal disentanglement: model layer

Formalization of the setup of Squires, Seigal, Bhate & Uhler, *Linear Causal
Disentanglement via Interventions* (ICML 2023), `arXiv:2211.16467`.

We work over `d` latent variables (`Fin d`) and `p ≥ d` observed variables
(`Fin p`).  The latent DAG `𝒢` is ordered so that an edge `j → i` implies `j > i`;
this makes the structural matrices upper triangular in the `Fin d` order.

For a fixed context, the latent SEM is `Z = A Z + Ω^{1/2} ε`, equivalently
`Z = B⁻¹ ε` with `B = Ω^{-1/2}(I − A)`.  The observed vector is `X = G Z` with
`G ∈ ℝ^{p×d}` full column rank, and `H := G⁺` its left inverse (a full-**row**-rank
`d × p` matrix with `H G = I_d`).  The only **observable** content is the family of
precision matrices `Θ_k = Hᵀ Bₖᵀ Bₖ H ∈ ℝ^{p×p}` (one per context).

We take an **unnormalized algebraic relaxation** of the model surrounding the
paper's Theorem 2: the data is a tuple `(H, {B_k}, {i_k}, {λ_k})`, and uniqueness
compares two such tuples that produce the *same* family `{Θ_k}`. The paper's row
normalization (Assumption 1(c)), which removes scaling and sign ambiguity, is not
encoded here. No Moore–Penrose pseudoinverse is needed: `H` enters only through
`LinearIndependent ℝ H` (full row rank) and the formula for `Θ_k`.

Conventions for a `Solution d p K`:
* context `0` is observational with matrix `B0`; contexts `1 … K` are interventional
  with matrices `Bint k`, intervention target `target k`, and (perfect-intervention)
  scaling `lam k > 0`;
* `Edge j i` means the latent edge `j → i` (`j` a parent of `i`), forced by `hAcyc`
  to satisfy `i < j`;
* `B0` is upper triangular (`B0 i j = 0` for `j < i`), has positive diagonal, and its
  off-diagonal support is exactly `Edge` — this is what *defines* `𝒢`;
* `hInt` is Assumption 1(b) specialized to perfect interventions (Assumption 2):
  `Bₖ = B₀ + e_{iₖ} cₖᵀ` with `cₖ = λₖ e_{iₖ} − B₀ᵀ e_{iₖ}`.

`S(𝒢)` is the set of node relabelings preserving edge orientation
(`Edge j i → σ i < σ j`); `permMat σ` is the corresponding permutation matrix
`(P_σ)_{ij} = ⟦i = σ j⟧`, matching the paper.
-/

@[expose] public section


namespace Causalean.Discovery.LinearDisentanglement

open scoped BigOperators

/-- [The standard basis vector](goal) isolates [coordinate `i`](hyp:i) in [dimension `d`](hyp:d),
the algebraic representation of a single-node intervention target. -/
abbrev stdVec (d : ℕ) (i : Fin d) : Fin d → ℝ := Pi.single i (1 : ℝ)

/-- [The permutation matrix](goal) relabels latent coordinates according to [permutation
`σ`](hyp:σ) in [dimension `d`](hyp:d), with one unit entry in each row and column. -/
def permMat {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if i = σ j then (1 : ℝ) else 0

/-- **An unnormalized algebraic relaxation of a linear causal disentanglement model**
with `d` latent variables, `p` observed variables, and `K` interventional contexts bundles
[a full-row-rank mixing pseudoinverse from the observed to the latent space](hyp:H,hH), [a
latent edge relation](hyp:Edge) that [respects the node order](hyp:hAcyc), and [an
observational structural matrix](hyp:B0) that is [upper triangular](hyp:hB0up), has [a
positive diagonal](hyp:hB0pos), and [has off-diagonal support exactly equal to the edge
set](hyp:hB0supp). For each interventional context it further carries [a structural
matrix](hyp:Bint), [an intervention target node](hyp:target), and [a positive
perfect-intervention scaling](hyp:lam,hlam), tied to the observational matrix by [the
perfect-single-node-intervention formula](hyp:hInt). -/
structure Solution (d p K : ℕ) where
  /-- The (transpose of the) mixing pseudoinverse: a `d × p` matrix. -/
  H : Matrix (Fin d) (Fin p) ℝ
  /-- `H` has full row rank: its rows are linearly independent. -/
  hH : LinearIndependent ℝ (fun i : Fin d => (H i : Fin p → ℝ))
  /-- The latent DAG edge relation; `Edge j i` means `j → i`. -/
  Edge : Fin d → Fin d → Prop
  /-- Edges respect the node order: `j → i` implies `i < j`. -/
  hAcyc : ∀ j i, Edge j i → i < j
  /-- Observational structural matrix `B₀`. -/
  B0 : Matrix (Fin d) (Fin d) ℝ
  /-- `B₀` is upper triangular in the node order. -/
  hB0up : ∀ i j, j < i → B0 i j = 0
  /-- `B₀` has positive diagonal. -/
  hB0pos : ∀ i, 0 < B0 i i
  /-- The off-diagonal support of `B₀` is exactly the edge set: this defines `𝒢`. -/
  hB0supp : ∀ i j, i ≠ j → (B0 i j ≠ 0 ↔ Edge j i)
  /-- Interventional structural matrices `Bₖ`, `k ∈ {1,…,K}`. -/
  Bint : Fin K → Matrix (Fin d) (Fin d) ℝ
  /-- The intervention target `iₖ` of context `k`. -/
  target : Fin K → Fin d
  /-- The perfect-intervention scaling `λₖ`. -/
  lam : Fin K → ℝ
  /-- `λₖ > 0`. -/
  hlam : ∀ k, 0 < lam k
  /-- Assumption 1(b) + Assumption 2 (perfect single-node interventions):
  `Bₖ = B₀ + e_{iₖ} cₖᵀ` with `cₖ = λₖ e_{iₖ} − B₀ᵀ e_{iₖ}`. -/
  hInt : ∀ k, Bint k =
    B0 + Matrix.vecMulVec (stdVec d (target k))
      (fun j => lam k * stdVec d (target k) j - B0 (target k) j)

namespace Solution

variable {d p K : ℕ}

/-- [The observational precision matrix](goal) is the observable Gram form induced by the baseline
structural matrix and mixing pseudoinverse of [solution `S`](hyp:S), with [latent dimension
`d`](hyp:d), [observed dimension `p`](hyp:p), and [intervention count `K`](hyp:K). -/
def Theta0 (S : Solution d p K) : Matrix (Fin p) (Fin p) ℝ :=
  S.H.transpose * S.B0.transpose * S.B0 * S.H

/-- [The precision matrix in intervention context `k`](goal) is the observable Gram form generated
by [context `k`](hyp:k) of [solution `S`](hyp:S), with [latent dimension `d`](hyp:d), [observed
dimension `p`](hyp:p), and [intervention count `K`](hyp:K). -/
def Theta (S : Solution d p K) (k : Fin K) : Matrix (Fin p) (Fin p) ℝ :=
  S.H.transpose * (S.Bint k).transpose * (S.Bint k) * S.H

/-- [A latent relabeling preserves the causal order](goal) when [permutation `σ`](hyp:σ) keeps every
child below its parent in [solution `S`](hyp:S), with [latent dimension `d`](hyp:d), [observed
dimension `p`](hyp:p), and [intervention count `K`](hyp:K). -/
def InSG (S : Solution d p K) (σ : Equiv.Perm (Fin d)) : Prop :=
  ∀ j i, S.Edge j i → σ i < σ j

end Solution

/-! ### Basic facts about permutation matrices -/

/-- [A permutation matrix is orthogonal](goal), so relabeling by [permutation `σ`](hyp:σ) in
[dimension `d`](hyp:d) preserves the Gram geometry used by the observed precision matrices. -/
theorem permMat_mul_transpose {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permMat σ * (permMat σ).transpose = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp only [Equiv.apply_symm_apply]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `permMat σ` is orthogonal: `(permMat σ)ᵀ * permMat σ = 1`. -/
theorem permMat_transpose_mul {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (permMat σ).transpose * permMat σ = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [σ.injective.eq_iff]
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

end Causalean.Discovery.LinearDisentanglement

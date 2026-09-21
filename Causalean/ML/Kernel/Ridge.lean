/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.InnerProductSpace.RKHS
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Regularized least squares — the representer theorem

The file defines `krrRisk` on a real inner-product space with a supplied
evaluation map and proves `representer_theorem`: under `λ > 0`, any global
minimizer is a finite linear combination of the sample representers `k(·, xᵢ)`
when evaluation satisfies the reproducing identity.
-/

@[expose] public section

namespace Causalean.ML

open BigOperators

/-- [Kernel-ridge empirical risk](goal) trades
[average squared error against a weighted squared function norm](step:1). It scores
[a candidate in a real inner-product space](hyp:H,f) through [its evaluation rule](hyp:feval) on
[covariates and responses](hyp:x,y) from [a sample of the specified size](hyp:n), with
[covariate space and regularization level](hyp:X,lam). -/
noncomputable def krrRisk {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feval : H → X → ℝ) {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (f : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (feval f (x i) - y i) ^ 2 + lam * ‖f‖ ^ 2

/-- [A kernel-ridge minimizer lies in the sampled representer span](goal), reducing an
infinite-dimensional optimization problem to sample
coefficients. The reduction applies to [the sampled covariates and responses](hyp:x,y) when
[evaluation has supplied Hilbert-space representers](hyp:hrkhs),
[the penalty is strictly positive](hyp:hlam), and [the candidate globally minimizes](hyp:hmin). -/
theorem representer_theorem {X H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {feval : H → X → ℝ} {representer : X → H}
    (hrkhs : HasReproducingRepresenters X H feval representer)
    {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam) {fhat : H}
    (hmin : ∀ g : H, krrRisk feval x y lam fhat ≤ krrRisk feval x y lam g) :
    ∃ α : Fin n → ℝ, fhat = ∑ i, α i • representer (x i) := by
  classical
  let M : Submodule ℝ H := Submodule.span ℝ (Set.range fun i : Fin n => representer (x i))
  have : FiniteDimensional ℝ M := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have : CompleteSpace M := by infer_instance
  let p : H := M.starProjection fhat
  have hp_mem : p ∈ M := M.starProjection_apply_mem fhat
  have hrep_mem : ∀ i : Fin n, representer (x i) ∈ M := by
    intro i
    exact Submodule.subset_span ⟨i, rfl⟩
  have heval_eq : ∀ i : Fin n, feval fhat (x i) = feval p (x i) := by
    intro i
    have horth : inner ℝ (fhat - p) (representer (x i)) = 0 := by
      exact Submodule.starProjection_inner_eq_zero (K := M) fhat
        (representer (x i)) (hrep_mem i)
    rw [hrkhs.reproducing fhat (x i), hrkhs.reproducing p (x i)]
    calc
      inner ℝ fhat (representer (x i))
          = inner ℝ ((fhat - p) + p) (representer (x i)) := by
              rw [sub_add_cancel]
      _ = inner ℝ (fhat - p) (representer (x i))
            + inner ℝ p (representer (x i)) := by
              rw [inner_add_left]
      _ = inner ℝ p (representer (x i)) := by
              rw [horth, zero_add]
  have hdata_eq :
      (∑ i, (feval fhat (x i) - y i) ^ 2)
        = ∑ i, (feval p (x i) - y i) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [heval_eq i]
  have hmin_p : krrRisk feval x y lam fhat ≤ krrRisk feval x y lam p := hmin p
  have hnorm_le : ‖fhat‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    have hmul_le : lam * ‖fhat‖ ^ 2 ≤ lam * ‖p‖ ^ 2 := by
      unfold krrRisk at hmin_p
      rw [hdata_eq] at hmin_p
      linarith
    nlinarith
  have hnorm_decomp :
      ‖fhat‖ ^ 2 = ‖p‖ ^ 2 + ‖(Mᗮ).starProjection fhat‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection fhat M
  have hperp_sq :
      ‖(Mᗮ).starProjection fhat‖ ^ 2 = 0 := by
    have hnonneg : 0 ≤ ‖(Mᗮ).starProjection fhat‖ ^ 2 :=
      sq_nonneg _
    nlinarith
  have hperp_zero : (Mᗮ).starProjection fhat = 0 := by
    apply norm_eq_zero.mp
    have hnonneg : 0 ≤ ‖(Mᗮ).starProjection fhat‖ :=
      norm_nonneg _
    nlinarith
  have hfhat_eq_p : fhat = p := by
    have hsplit := Submodule.starProjection_add_starProjection_orthogonal (K := M) fhat
    calc
      fhat = M.starProjection fhat + (Mᗮ).starProjection fhat := hsplit.symm
      _ = M.starProjection fhat + 0 := by rw [hperp_zero]
      _ = p := by rw [add_zero]
  have hfhat_mem : fhat ∈ M := by
    simpa [hfhat_eq_p] using hp_mem
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
      (v := fun i : Fin n => representer (x i)) (x := fhat)).mp hfhat_mem with ⟨α, hα⟩
  exact ⟨α, hα.symm⟩

end Causalean.ML

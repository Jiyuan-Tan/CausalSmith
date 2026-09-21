/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.LinearAlgebra.NormalEquations
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Closed-form series least squares and its hat matrix

This module supplies the finite-dimensional algebra used by the series prediction-rate theorem.
For a design matrix `Φ`, it defines the unweighted Gram matrix `ΦᵀΦ`, its inverse-Gram
least-squares coefficient map, and the projection hat matrix `H = Φ(ΦᵀΦ)⁻¹Φᵀ`.  When the Gram
matrix is invertible, the coefficient map satisfies the normal equations, fitted-value differences
are exactly linear in outcome differences, and `∑ᵢₖ Hᵢₖ²` equals the number of columns.
-/

@[expose] public section

open Causalean.Mathlib.LinearAlgebra.NormalEquations

namespace Causalean.Stat.Nonparametric.SeriesSieve

open Matrix
open scoped BigOperators

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Given [a finite series design matrix](hyp:Φ), the [series Gram matrix](goal) is the
column cross-product `ΦᵀΦ`. -/
noncomputable def seriesGram (Φ : Matrix (Fin N) ι ℝ) : Matrix ι ι ℝ :=
  Φᵀ * Φ

/-- Given [a finite series design matrix](hyp:Φ) and [a vector of responses](hyp:y), the
[closed-form series least-squares coefficient vector](goal) is `(ΦᵀΦ)⁻¹Φᵀy`. -/
noncomputable def seriesLSCoeff (Φ : Matrix (Fin N) ι ℝ) (y : Fin N → ℝ) : ι → ℝ :=
  (seriesGram Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)

/-- Given [a finite series design matrix](hyp:Φ), the [series hat matrix](goal) is the
fitted-value projection `Φ(ΦᵀΦ)⁻¹Φᵀ`. -/
noncomputable def seriesHatMatrix (Φ : Matrix (Fin N) ι ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Φ * (seriesGram Φ)⁻¹ * Φᵀ

/-- **Normal equations for the closed-form series fit.** If [the series Gram matrix is
invertible](hyp:hGram), then [the residual from the closed-form coefficient vector is orthogonal
to every design column](goal). -/
theorem seriesLSCoeff_normal_equations (Φ : Matrix (Fin N) ι ℝ) (y : Fin N → ℝ)
    (hGram : IsUnit (seriesGram Φ).det) :
    ∀ k : ι, ∑ i, lstsqResidual Φ y (seriesLSCoeff Φ y) i * Φ i k = 0 := by
  intro k
  let b : ι → ℝ := Φᵀ *ᵥ y
  have hnormal : Φᵀ *ᵥ (y - Φ *ᵥ seriesLSCoeff Φ y) = 0 := by
    calc
      Φᵀ *ᵥ (y - Φ *ᵥ seriesLSCoeff Φ y)
          = b - (seriesGram Φ) *ᵥ seriesLSCoeff Φ y := by
              rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
              rfl
      _ = b - (seriesGram Φ) *ᵥ ((seriesGram Φ)⁻¹ *ᵥ b) := by
              rfl
      _ = b - ((seriesGram Φ) * (seriesGram Φ)⁻¹) *ᵥ b := by
              rw [Matrix.mulVec_mulVec]
      _ = 0 := by
              rw [Matrix.mul_nonsing_inv _ hGram, Matrix.one_mulVec, sub_self]
  have hk := congrFun hnormal k
  simpa [lstsqResidual, Matrix.mulVec, Matrix.transpose_apply, dotProduct, sub_eq_add_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_comm, mul_left_comm, mul_assoc] using hk

/-- **Least-squares fitted-value linearity.** For [a design matrix `Φ`](hyp:Φ), [a baseline
response vector `f`](hyp:f), and [an additive error vector `ε`](hyp:ε), [the fitted-value
difference between the baseline fit and the fit to `f+ε` is `-Hε`, where `H` is the series hat
matrix](goal). -/
theorem seriesLS_fitted_sub_eq_neg_hat (Φ : Matrix (Fin N) ι ℝ)
    (f ε : Fin N → ℝ) :
    Φ *ᵥ (seriesLSCoeff Φ f - seriesLSCoeff Φ (f + ε))
      = -(seriesHatMatrix Φ *ᵥ ε) := by
  simp only [seriesLSCoeff, Matrix.mulVec_add, Matrix.mulVec_sub]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub]
  rw [seriesHatMatrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- **Hat-matrix Frobenius identity.** If [the series Gram matrix is invertible](hyp:hGram), then
[the sum of squares of all entries of the least-squares hat matrix equals the number of series
columns](goal). -/
theorem seriesHatMatrix_frobenius_sq (Φ : Matrix (Fin N) ι ℝ)
    (hGram : IsUnit (seriesGram Φ).det) :
    (∑ i, ∑ k, seriesHatMatrix Φ i k ^ 2) = (Fintype.card ι : ℝ) := by
  let G := seriesGram Φ
  let H := seriesHatMatrix Φ
  have hGsymm : Gᵀ = G := by
    simp [G, seriesGram, Matrix.transpose_mul]
  have hGinvSymm : G⁻¹ᵀ = G⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hGsymm]
  have hHsymm : Hᵀ = H := by
    simp [H, seriesHatMatrix, G, Matrix.transpose_mul, hGinvSymm, Matrix.mul_assoc]
  have hHidem : H * H = H := by
    calc
      H * H = Φ * G⁻¹ * (G * G⁻¹) * Φᵀ := by
        simp only [H, seriesHatMatrix, G, seriesGram]
        simp only [Matrix.mul_assoc]
      _ = H := by
        rw [Matrix.mul_nonsing_inv _ hGram]
        simp [H, seriesHatMatrix, G, Matrix.mul_assoc]
  calc
    (∑ i, ∑ k, seriesHatMatrix Φ i k ^ 2)
        = Matrix.trace (H * H) := by
            simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, H]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hs := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A k i) hHsymm
            simp only [Matrix.transpose_apply] at hs
            change H i k ^ 2 = H i k * H k i
            rw [← hs]
            ring
    _ = Matrix.trace H := by rw [hHidem]
    _ = Matrix.trace (G * G⁻¹) := by
          simp only [H, seriesHatMatrix, G, seriesGram]
          exact Matrix.trace_mul_cycle Φ (seriesGram Φ)⁻¹ Φᵀ
    _ = (Fintype.card ι : ℝ) := by
          rw [Matrix.mul_nonsing_inv _ hGram, Matrix.trace_one]

end Causalean.Stat.Nonparametric.SeriesSieve

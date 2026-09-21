/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT

/-!
# Predictable variance of the Hájek reveal martingale

This module identifies the predictable quadratic variation of the explicit finite-population
Hájek array.  The resulting formula is the starting point for the remaining concentration
estimate in the finite-population central limit theorem.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open Filter

/-- Given [row spaces](hyp:Ω), [their measurable structures](hyp:mΩ), [row
measures](hyp:μ), [a martingale-difference array](hyp:A), [deterministic row
scalars](hyp:c), and [a row](hyp:n), [scaling the array multiplies its predictable quadratic
variation by the square of the row scalar almost everywhere](goal). -/
theorem scaleMartingaleDifferenceArray_predictableQuadraticVariation_ae_eq
    {Ω : ℕ → Type*} [mΩ : (n : ℕ) → MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)}
    (A : MartingaleDifferenceArray Ω μ) (c : ℕ → ℝ) (n : ℕ) :
    (scaleMartingaleDifferenceArray A c).predictableQuadraticVariation n =ᵐ[μ n]
      fun ω => (c n) ^ 2 * A.predictableQuadraticVariation n ω := by
  have hall : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
      (μ n)[fun ω =>
          ((scaleMartingaleDifferenceArray A c).increment n k ω) ^ 2 |
        (scaleMartingaleDifferenceArray A c).filtration n k] ω =
        (c n) ^ 2 * (μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω := by
    apply (Finset.eventually_all _).mpr
    intro k _hk
    have hfun : (fun ω =>
        ((scaleMartingaleDifferenceArray A c).increment n k ω) ^ 2) =
        (c n) ^ 2 • fun ω => (A.increment n k ω) ^ 2 := by
      funext ω
      simp only [scaleMartingaleDifferenceArray, Pi.smul_apply, smul_eq_mul]
      ring
    have hlinear := condExp_smul (μ := μ n) ((c n) ^ 2)
      (fun ω => (A.increment n k ω) ^ 2) (A.filtration n k)
    rw [hfun]
    change (μ n)[(c n) ^ 2 • (fun ω => (A.increment n k ω) ^ 2) |
      A.filtration n k] =ᵐ[μ n] fun ω =>
        (c n) ^ 2 * (μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω
    filter_upwards [hlinear] with ω hω
    simpa only [Pi.smul_apply, smul_eq_mul] using hω
  filter_upwards [hall] with ω hω
  unfold MartingaleDifferenceArray.predictableQuadraticVariation
    scaleMartingaleDifferenceArray
  simp only [Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact hω k hk

/-- Given [sequences of population sizes](hyp:N), [proper positive sample
sizes](hyp:K,hKpos,hKlt), [finite-population outcomes](hyp:y), and [a row](hyp:n), [the
predictable quadratic variation of the explicit Hájek array is almost everywhere the sum of
the squared Hájek coefficients times the successive remaining-population variances](goal). -/
theorem srsPermutationHajekArray_predictableQuadraticVariation_ae_eq
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (n : ℕ) :
    (srsPermutationHajekArray N K hKpos hKlt y).predictableQuadraticVariation n
      =ᵐ[(uniformPermutationDesign (N n)).toMeasure] fun π =>
        ∑ k ∈ Finset.range (K n),
          if hk : k < K n then
            (hajekIncrementCoefficient (N n) (K n) (hKpos n) (hKlt n) k) ^ 2 *
              permutationNextVariance (y n) k (hk.trans (hKlt n)) π
          else 0 := by
  let μ := (uniformPermutationDesign (N n)).toMeasure
  have hall : ∀ᵐ π ∂μ, ∀ k ∈ Finset.range (K n),
      μ[fun ω =>
          ((srsPermutationHajekArray N K hKpos hKlt y).increment n k ω) ^ 2 |
        (srsPermutationHajekArray N K hKpos hKlt y).filtration n k] π =
        if hk : k < K n then
          (hajekIncrementCoefficient (N n) (K n) (hKpos n) (hKlt n) k) ^ 2 *
            permutationNextVariance (y n) k (hk.trans (hKlt n)) π
        else 0 := by
    apply (Finset.eventually_all _).mpr
    intro k hkRange
    have hk : k < K n := Finset.mem_range.mp hkRange
    have hinc : (fun ω =>
        ((srsPermutationHajekArray N K hKpos hKlt y).increment n k ω) ^ 2) =
        fun ω => (permutationHajekIncrement
          (K n) (hKpos n) (hKlt n) (y n) k hk ω) ^ 2 := by
      funext ω
      simp only [srsPermutationHajekArray, hk, dite_true]
    have hcond := permutationHajekIncrement_sq_condExp
      (K n) (hKpos n) (hKlt n) (y n) k hk
    rw [hinc]
    simp only [μ, srsPermutationHajekArray, hk, dite_true]
    filter_upwards [hcond] with ω hω
    exact hω
  filter_upwards [hall] with π hπ
  unfold MartingaleDifferenceArray.predictableQuadraticVariation
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact hπ k hk

/-- Given [sequences of population sizes](hyp:N), [proper positive sample
sizes](hyp:K,hKpos,hKlt), [finite-population outcomes](hyp:y) with [positive
variances](hyp:hvar), and [a row](hyp:n), [the standardized array's predictable quadratic
variation is the unstandardized predictable quadratic variation divided by the exact sample-mean
variance almost everywhere](goal). -/
theorem standardizedSrsPermutationHajekArray_predictableQuadraticVariation_ae_eq
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n)) (n : ℕ) :
    (standardizedSrsPermutationHajekArray N K hKpos hKlt y).predictableQuadraticVariation n
      =ᵐ[(uniformPermutationDesign (N n)).toMeasure] fun π =>
        (srsPermutationHajekArray N K hKpos hKlt y).predictableQuadraticVariation n π /
          srsSampleMeanVariance (N n) (K n) (y n) := by
  have hKR : (0 : ℝ) < K n := by exact_mod_cast hKpos n
  have hNR : (0 : ℝ) < N n := by exact_mod_cast (hKpos n).trans (hKlt n)
  have hspos : 0 < srsSampleMeanVariance (N n) (K n) (y n) :=
    srsSampleMeanVariance_pos (hKpos n) (hKlt n) (hvar n)
  have hscale := scaleMartingaleDifferenceArray_predictableQuadraticVariation_ae_eq
    (srsPermutationHajekArray N K hKpos hKlt y)
    (fun r => (Real.sqrt (srsSampleMeanVariance (N r) (K r) (y r)))⁻¹) n
  filter_upwards [hscale] with π hπ
  rw [show MartingaleDifferenceArray.predictableQuadraticVariation
      (standardizedSrsPermutationHajekArray N K hKpos hKlt y) n π =
        (Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))⁻¹ ^ 2 *
          MartingaleDifferenceArray.predictableQuadraticVariation
            (srsPermutationHajekArray N K hKpos hKlt y) n π by
        simpa [standardizedSrsPermutationHajekArray] using hπ]
  rw [inv_pow, Real.sq_sqrt hspos.le]
  ring

end Causalean.Experimentation.DesignBased

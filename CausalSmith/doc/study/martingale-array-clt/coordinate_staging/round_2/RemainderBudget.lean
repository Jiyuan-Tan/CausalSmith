/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Causalean.Stat.CLT.MartingaleArray.ConditionalTaylor

/-! # Row Taylor-remainder bounds from predictable budgets

This module converts almost-everywhere bounds on predictable variance and
conditional Lindeberg mass into a deterministic bound on the sum of integrated
quadratic characteristic-function remainders.
-/

namespace Causalean.Stat

open Complex Filter MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- If [the truncation threshold is positive](hyp:hη), [the frequency-threshold product is at
most one](hyp:htη), [both budgets are nonnegative](hyp:hK,hδ), [a row has predictable variance
at most `K`](hyp:hVariance), and [conditional Lindeberg mass at most `δ`](hyp:hLindeberg), then [the sum of its
integrated quadratic exponential remainders obeys the corresponding truncated
Taylor bound](goal). -/
theorem sum_integral_norm_expQuadraticRemainder_le_of_budgets
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) (t η K δ : ℝ)
    (hη : 0 < η) (htη : |t| * η ≤ 1) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hVariance : A.predictableQuadraticVariation n ≤ᵐ[μ n] fun _ => K)
    (hLindeberg : A.conditionalLindeberg η n ≤ᵐ[μ n] fun _ => δ) :
    (∑ k ∈ Finset.range (A.rowLength n),
        ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n)) ≤
      |t| ^ 3 * η * K +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ := by
  /- Sum `integral_norm_expQuadraticRemainder_le` over the active increments.
  Use `integral_condExp` to identify the two sums of unconditional moments with
  the integrals of predictable quadratic variation and conditional Lindeberg
  mass, then integrate the two a.e. budget bounds. -/
  have hVint : Integrable (A.predictableQuadraticVariation n) (μ n) := by
    unfold predictableQuadraticVariation
    rw [show (∑ k ∈ Finset.range (A.rowLength n),
        (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k]) =
      (fun ω => ∑ k ∈ Finset.range (A.rowLength n),
        (μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω) by
        funext ω
        simp only [Finset.sum_apply]]
    exact integrable_finsetSum (Finset.range (A.rowLength n))
      (fun k _ => (integrable_condExp : Integrable
        ((μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k]) (μ n)))
  have hLint : Integrable (A.conditionalLindeberg η n) (μ n) := by
    unfold conditionalLindeberg lindebergTerm
    rw [show (∑ k ∈ Finset.range (A.rowLength n),
        (μ n)[fun ω => if η < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0 | A.filtration n k]) =
      (fun ω => ∑ k ∈ Finset.range (A.rowLength n),
        (μ n)[fun ω => if η < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0 |
            A.filtration n k] ω) by
        funext ω
        simp only [Finset.sum_apply]]
    exact integrable_finsetSum (Finset.range (A.rowLength n))
      (fun k _ => (integrable_condExp : Integrable
        ((μ n)[fun ω => if η < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0 | A.filtration n k]) (μ n)))
  have hSecond :
      (∑ k ∈ Finset.range (A.rowLength n),
        ∫ ω, (A.increment n k ω) ^ 2 ∂(μ n)) =
        ∫ ω, A.predictableQuadraticVariation n ω ∂(μ n) := by
    unfold predictableQuadraticVariation
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_condExp : Integrable
      ((μ n)[fun ω => (A.increment n k ω) ^ 2 |
        A.filtration n k]) (μ n)))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_condExp ((A.filtration n).le k)).symm
  have hTail :
      (∑ k ∈ Finset.range (A.rowLength n),
        ∫ ω, (if η < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0) ∂(μ n)) =
        ∫ ω, A.conditionalLindeberg η n ω ∂(μ n) := by
    unfold conditionalLindeberg lindebergTerm
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_condExp : Integrable
      ((μ n)[fun ω => if η < |A.increment n k ω| then
        (A.increment n k ω) ^ 2 else 0 | A.filtration n k]) (μ n)))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_condExp ((A.filtration n).le k)).symm
  have hVbudget : ∫ ω, A.predictableQuadraticVariation n ω ∂(μ n) ≤ K := by
    calc
      (∫ ω, A.predictableQuadraticVariation n ω ∂(μ n)) ≤
          ∫ _ω, K ∂(μ n) :=
        integral_mono_ae hVint (integrable_const K) hVariance
      _ = K := by simp
  have hLbudget : ∫ ω, A.conditionalLindeberg η n ω ∂(μ n) ≤ δ := by
    calc
      (∫ ω, A.conditionalLindeberg η n ω ∂(μ n)) ≤
          ∫ _ω, δ ∂(μ n) :=
        integral_mono_ae hLint (integrable_const δ) hLindeberg
      _ = δ := by simp
  have hsmall : 0 ≤ |t| ^ 3 * η := mul_nonneg (by positivity) hη.le
  have hlarge : 0 ≤ 2 / η ^ 2 + |t| / η + t ^ 2 / 2 := by positivity
  calc
    (∑ k ∈ Finset.range (A.rowLength n),
        ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n)) ≤
      ∑ k ∈ Finset.range (A.rowLength n),
        (|t| ^ 3 * η * (∫ ω, (A.increment n k ω) ^ 2 ∂(μ n)) +
          (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
            (∫ ω, if η < |A.increment n k ω| then
              (A.increment n k ω) ^ 2 else 0 ∂(μ n))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact integral_norm_expQuadraticRemainder_le
        (A.increment n k) (A.squareIntegrable n k (Finset.mem_range.mp hk))
          t η hη htη
    _ = |t| ^ 3 * η *
          (∑ k ∈ Finset.range (A.rowLength n),
            ∫ ω, (A.increment n k ω) ^ 2 ∂(μ n)) +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
          (∑ k ∈ Finset.range (A.rowLength n),
            ∫ ω, if η < |A.increment n k ω| then
              (A.increment n k ω) ^ 2 else 0 ∂(μ n)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = |t| ^ 3 * η *
          (∫ ω, A.predictableQuadraticVariation n ω ∂(μ n)) +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
          (∫ ω, A.conditionalLindeberg η n ω ∂(μ n)) := by
      rw [hSecond, hTail]
    _ ≤ |t| ^ 3 * η * K +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hVbudget hsmall)
        (mul_le_mul_of_nonneg_left hLbudget hlarge)

end MartingaleDifferenceArray

end Causalean.Stat

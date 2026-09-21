/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Predictable variance bounds from conditional Lindeberg mass

This module supplies the local and row-wise estimates that make the predictable
variance mesh small under a conditional Lindeberg budget.  These are the
probabilistic accounting inputs for Gaussian-time interpolation.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- For [an active increment](hyp:hk) and [a positive threshold](hyp:hη), [its
conditional second moment is at most the squared threshold plus its conditional
Lindeberg term](goal). -/
theorem conditionalSecondMoment_le_sq_add_lindebergTerm
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) (η : ℝ) (hη : 0 < η) :
    (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ≤ᵐ[μ n]
      fun ω => η ^ 2 + A.lindebergTerm η n k ω := by
  /- Split `X²` into the events `|X| ≤ η` and `η < |X|`.  Bound the first
  part by the constant `η²`, apply conditional-expectation monotonicity, and
  identify the second part with `lindebergTerm`. -/
  have hX2 : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
    (A.squareIntegrable n k hk).integrable_sq
  have htrunc : Integrable (fun ω => if η < |A.increment n k ω| then
      (A.increment n k ω) ^ 2 else 0) (μ n) := by
    let X := (A.squareIntegrable n k hk).aestronglyMeasurable.mk
      (A.increment n k)
    have hX : A.increment n k =ᵐ[μ n] X :=
      (A.squareIntegrable n k hk).aestronglyMeasurable.ae_eq_mk
    have hXmeas : StronglyMeasurable X :=
      (A.squareIntegrable n k hk).aestronglyMeasurable.stronglyMeasurable_mk
    have hX2' : Integrable (fun ω => X ω ^ 2) (μ n) :=
      hX2.congr (hX.pow_const 2)
    have hs : MeasurableSet {ω | η < |X ω|} :=
      measurableSet_lt measurable_const hXmeas.measurable.norm
    have htruncX : Integrable
        (fun ω => if η < |X ω| then X ω ^ 2 else 0) (μ n) := by
      apply (hX2'.indicator hs).congr
      filter_upwards with ω
      rw [Set.indicator]
      rfl
    exact htruncX.congr (hX.mono fun ω hω => by simp [hω])
  have hmajor : Integrable (fun ω => η ^ 2 +
      if η < |A.increment n k ω| then (A.increment n k ω) ^ 2 else 0) (μ n) :=
    (integrable_const _).add htrunc
  have hpoint : (fun ω => (A.increment n k ω) ^ 2) ≤ᵐ[μ n]
      (fun ω => η ^ 2 +
        if η < |A.increment n k ω| then (A.increment n k ω) ^ 2 else 0) :=
    ae_of_all _ fun ω => by
      by_cases hω : η < |A.increment n k ω|
      · simp only [hω, ↓reduceIte]
        exact le_add_of_nonneg_left (sq_nonneg η)
      · simp only [hω, ↓reduceIte, add_zero]
        rw [← sq_abs (A.increment n k ω)]
        exact (sq_le_sq₀ (abs_nonneg _) hη.le).mpr (le_of_not_gt hω)
  have hmono := condExp_mono (m := A.filtration n k) hX2 hmajor hpoint
  have hadd := condExp_add (integrable_const (η ^ 2)) htrunc (A.filtration n k)
  have hadd' : (μ n)[fun ω => η ^ 2 +
      (if η < |A.increment n k ω| then (A.increment n k ω) ^ 2 else 0) |
        A.filtration n k] =ᵐ[μ n]
      (μ n)[fun _ => η ^ 2 | A.filtration n k] +
        (μ n)[fun ω => if η < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0 | A.filtration n k] := by
    convert hadd using 1 <;> ext ω <;> rfl
  have hconst := condExp_const (μ := μ n) ((A.filtration n).le k) (η ^ 2)
  filter_upwards [hmono, hadd'] with ω hmonoω haddω
  unfold lindebergTerm
  rw [haddω] at hmonoω
  simpa only [Pi.add_apply, congrFun hconst ω] using hmonoω

/-- If [the truncation threshold is positive](hyp:hη), [the row predictable quadratic variation is bounded](hyp:hVariance) and
[its conditional Lindeberg sum is bounded](hyp:hLindeberg), with [nonnegative
budgets](hyp:hK,hδ), then [the sum of squared conditional variance increments is
at most `(η² + δ)K`](goal). -/
theorem sum_sq_conditionalSecondMoment_le_of_budgets
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) (η K δ : ℝ)
    (hη : 0 < η) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hVariance : A.predictableQuadraticVariation n ≤ᵐ[μ n] fun _ => K)
    (hLindeberg : A.conditionalLindeberg η n ≤ᵐ[μ n] fun _ => δ) :
    (fun ω => ∑ k ∈ Finset.range (A.rowLength n),
        ((μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω) ^ 2) ≤ᵐ[μ n]
      fun _ => (η ^ 2 + δ) * K := by
  /- On one common full-measure set, every conditional variance and Lindeberg
  term is nonnegative.  The local lemma bounds each variance by `η² + δ`;
  hence `∑ v_k² ≤ (η²+δ) ∑ v_k ≤ (η²+δ)K`. -/
  have hlocal : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
      (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω ≤
        η ^ 2 + A.lindebergTerm η n k ω :=
    (Finset.eventually_all _).mpr fun k hk =>
      A.conditionalSecondMoment_le_sq_add_lindebergTerm n k
        (Finset.mem_range.mp hk) η hη
  have hvnonneg : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
      0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 |
        A.filtration n k] ω :=
    (Finset.eventually_all _).mpr fun k _ =>
      condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (A.increment n k ω))
  have hlnonneg : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
      0 ≤ A.lindebergTerm η n k ω :=
    (Finset.eventually_all _).mpr fun k _ => by
      apply condExp_nonneg
      filter_upwards with ω
      split_ifs <;> positivity
  filter_upwards [hlocal, hvnonneg, hlnonneg, hVariance, hLindeberg]
    with ω hlocalω hvω hlω hVω hLω
  have hB : 0 ≤ η ^ 2 + δ := add_nonneg (sq_nonneg η) hδ
  unfold predictableQuadraticVariation at hVω
  unfold conditionalLindeberg at hLω
  simp only [Finset.sum_apply] at hVω hLω
  calc
    (∑ k ∈ Finset.range (A.rowLength n),
        ((μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω) ^ 2) ≤
        ∑ k ∈ Finset.range (A.rowLength n),
          (η ^ 2 + δ) *
            (μ n)[fun ω => (A.increment n k ω) ^ 2 |
              A.filtration n k] ω := by
      apply Finset.sum_le_sum
      intro k hk
      have hlk : A.lindebergTerm η n k ω ≤ δ :=
        (Finset.single_le_sum (fun j hj => hlω j hj) hk).trans hLω
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right
        ((hlocalω k hk).trans (add_le_add_right hlk _)) (hvω k hk)
    _ = (η ^ 2 + δ) *
        (∑ k ∈ Finset.range (A.rowLength n),
          (μ n)[fun ω => (A.increment n k ω) ^ 2 |
            A.filtration n k] ω) := by rw [Finset.mul_sum]
    _ ≤ (η ^ 2 + δ) * K := mul_le_mul_of_nonneg_left hVω hB

end MartingaleDifferenceArray

end Causalean.Stat

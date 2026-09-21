/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic

/-! # Martingale-difference triangular arrays

This module packages a real-valued, square-integrable martingale-difference
triangular array whose rows may live on different probability spaces.  Row
lengths may vary with the row index.  It also defines row sums, predictable quadratic variation,
conditional Lindeberg sums, and conditional fourth-moment sums.

Increment `k` in row `n` is measurable with respect to filtration time `k + 1`
and has conditional mean zero at time `k`.  Thus the indexing directly models
the usual pair `F_{n,k-1} ⊆ F_{n,k}` without subtraction on natural numbers.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

/-- Given [one measure space for every row](hyp:Ω,μ), [a row-indexed family of real random
variables](hyp:Y) [converges in probability](goal) to [the target constant](hyp:c) when, at every positive
tolerance, the row probability of exceeding that tolerance tends to zero. -/
def TendstoInProbability
    (μ : (n : ℕ) → Measure (Ω n)) (Y : (n : ℕ) → Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - c|}) atTop (𝓝 0)

/-- Given [one probability space for every row](hyp:Ω,μ), [almost-everywhere measurable
row variables](hyp:Y,hY), and [a target probability law](hyp:Q), [convergence in
distribution to that law](goal) means weak convergence of the row pushforward laws. -/
def TendstoInDistribution
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Y : (n : ℕ) → Ω n → ℝ) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hY : ∀ n, AEMeasurable (Y n) (μ n)) : Prop :=
  Tendsto (β := ProbabilityMeasure ℝ)
    (fun n => ⟨(μ n).map (Y n), Measure.isProbabilityMeasure_map (hY n)⟩)
    atTop (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩)

/-- A martingale-difference triangular array consists of [finite row lengths](hyp:rowLength),
[real increments](hyp:increment), and [one filtration per row](hyp:filtration), such that
[each active increment is measurable at the next filtration time](hyp:adapted), [is square
integrable](hyp:squareIntegrable), and [has conditional mean zero given the preceding
filtration time](hyp:condExp_zero); these data together form the array. -/
structure MartingaleDifferenceArray (Ω : ℕ → Type*)
    [mΩ : (n : ℕ) → MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) where
  rowLength : ℕ → ℕ
  increment : (n k : ℕ) → Ω n → ℝ
  filtration : (n : ℕ) → Filtration ℕ (mΩ n)
  adapted : ∀ n k, k < rowLength n →
    StronglyMeasurable[filtration n (k + 1)] (increment n k)
  squareIntegrable : ∀ n k, k < rowLength n → MemLp (increment n k) 2 (μ n)
  condExp_zero : ∀ n k, k < rowLength n →
    (μ n)[increment n k | filtration n k] =ᵐ[μ n] 0

namespace MartingaleDifferenceArray

/-- The row sum is the sum of the increments whose indices are below that row's length. -/
noncomputable def rowSum (A : MartingaleDifferenceArray Ω μ) (n : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (A.rowLength n), A.increment n k

/-- For [a martingale-difference triangular array](hyp:A) and [one row](hyp:n), [its row
sum is almost-everywhere measurable under that row's probability measure](goal). -/
lemma rowSum_aemeasurable (A : MartingaleDifferenceArray Ω μ) (n : ℕ) :
    AEMeasurable (A.rowSum n) (μ n) := by
  unfold rowSum
  apply Finset.aemeasurable_sum
  intro k hk
  exact (A.squareIntegrable n k (Finset.mem_range.mp hk)).aemeasurable

/-- The predictable quadratic variation of a row is the sum of the conditional second
moments of its increments, each conditioned on the preceding filtration time. -/
noncomputable def predictableQuadraticVariation
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (A.rowLength n),
    (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k]

/-- A conditional Lindeberg term is the conditional second moment of one increment after
discarding values whose absolute size is at most the chosen threshold. -/
noncomputable def lindebergTerm
    (A : MartingaleDifferenceArray Ω μ) (ε : ℝ) (n k : ℕ) : Ω n → ℝ :=
  (μ n)[fun ω => if ε < |A.increment n k ω| then (A.increment n k ω) ^ 2 else 0 |
    A.filtration n k]

/-- The conditional Lindeberg sum for a row adds its conditional truncated second moments
over all increments in that row. -/
noncomputable def conditionalLindeberg
    (A : MartingaleDifferenceArray Ω μ) (ε : ℝ) (n : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (A.rowLength n), A.lindebergTerm ε n k

/-- The conditional fourth-moment sum for a row adds the conditional fourth moments of all
increments, each conditioned on the preceding filtration time. -/
noncomputable def conditionalFourthMoment
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (A.rowLength n),
    (μ n)[fun ω => (A.increment n k ω) ^ 4 | A.filtration n k]

/-- The unconditional fourth-moment sum is the deterministic sum of the fourth moments of
the increments in one row. -/
noncomputable def fourthMomentSum
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (A.rowLength n), ∫ ω, (A.increment n k ω) ^ 4 ∂(μ n)

end MartingaleDifferenceArray

end Causalean.Stat

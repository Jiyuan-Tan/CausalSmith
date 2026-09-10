/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Causalean.Stat.CLT.MartingaleArray.StoppedBudget
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Predictably stopped martingale-difference arrays

This module constructs a finite-row martingale array stopped before its
predictable variance or conditional Lindeberg budget is exceeded.  The stopping
multiplier is measurable at the preceding filtration time, so the stopped
increments remain martingale differences.  No independence is introduced.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- The predictable quadratic variation through index `k` is the sum of the
conditional second moments of the active row increments with indices at most
`k`. -/
noncomputable def predictableQuadraticVariationThrough
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ) : Ω n → ℝ :=
  ∑ j ∈ Finset.range (min (k + 1) (A.rowLength n)),
    (μ n)[fun ω => (A.increment n j ω) ^ 2 | A.filtration n j]

/-- The conditional Lindeberg mass through index `k` is the sum of the
conditional truncated second moments of the active row increments with indices
at most `k`. -/
noncomputable def conditionalLindebergThrough
    (A : MartingaleDifferenceArray Ω μ) (ε : ℝ) (n k : ℕ) : Ω n → ℝ :=
  ∑ j ∈ Finset.range (min (k + 1) (A.rowLength n)), A.lindebergTerm ε n j

/-- The predictable stopping multiplier for increment `k` is one exactly when
the original row's predictable variance and conditional Lindeberg mass through
`k` remain within the supplied budgets, and is zero otherwise. -/
noncomputable def stopMultiplier
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (n k : ℕ) : Ω n → ℝ :=
  fun ω => if A.predictableQuadraticVariationThrough n k ω ≤ K ∧
      A.conditionalLindebergThrough ε n k ω ≤ δ then 1 else 0

/-- For [an active row increment](hyp:hk), [its stopping multiplier is measurable
at the preceding filtration time](goal). -/
theorem stopMultiplier_stronglyMeasurable
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (n k : ℕ)
    (hk : k < A.rowLength n) :
    StronglyMeasurable[A.filtration n k] (A.stopMultiplier ε K δ n k) := by
  /- Conditional expectations are strongly measurable in their conditioning
  sigma-algebras.  Lift every term with filtration monotonicity (`j ≤ k`),
  close finite sums, then use measurability of the two closed inequalities and
  the piecewise-constant multiplier. -/
  have hV : StronglyMeasurable[A.filtration n k]
      (A.predictableQuadraticVariationThrough n k) := by
    unfold predictableQuadraticVariationThrough
    refine Finset.stronglyMeasurable_sum _ fun j hj => ?_
    exact stronglyMeasurable_condExp.mono ((A.filtration n).mono
      (Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _))))
  have hL : StronglyMeasurable[A.filtration n k]
      (A.conditionalLindebergThrough ε n k) := by
    unfold conditionalLindebergThrough lindebergTerm
    refine Finset.stronglyMeasurable_sum _ fun j hj => ?_
    exact stronglyMeasurable_condExp.mono ((A.filtration n).mono
      (Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _))))
  unfold stopMultiplier
  exact StronglyMeasurable.ite
    ((hV.measurable measurableSet_Iic).inter (hL.measurable measurableSet_Iic))
    stronglyMeasurable_const stronglyMeasurable_const

section FiniteMeasure

variable [∀ n, IsFiniteMeasure (μ n)]

/-- Given [a martingale-difference triangular array](hyp:A), [a truncation threshold](hyp:ε),
[a predictable-variance budget](hyp:K), and [a conditional-Lindeberg budget](hyp:δ),
[the predictably stopped array](goal) is another square-integrable martingale-difference
array with the same row lengths and filtrations. -/
noncomputable def stoppedArray
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) :
    MartingaleDifferenceArray Ω μ where
  rowLength := A.rowLength
  increment n k ω := A.stopMultiplier ε K δ n k ω * A.increment n k ω
  filtration := A.filtration
  adapted := by
    /- Lift the predictable multiplier from time `k` to `k+1`, multiply by
    the adapted increment, and unfold the stopped definitions. -/
    intro n k hk
    exact ((A.stopMultiplier_stronglyMeasurable ε K δ n k hk).mono
      ((A.filtration n).mono (Nat.le_succ k))).mul (A.adapted n k hk)
  squareIntegrable := by
    /- The multiplier only takes values zero and one, so bounded
    multiplication preserves the increment's `MemLp 2` property. -/
    intro n k hk
    refine (A.squareIntegrable n k hk).of_le
      (((A.stopMultiplier_stronglyMeasurable ε K δ n k hk).mono
        ((A.filtration n).le k)).aestronglyMeasurable.mul
          (A.squareIntegrable n k hk).aestronglyMeasurable) ?_
    filter_upwards with ω
    unfold stopMultiplier
    split_ifs <;> simp
  condExp_zero := by
    /- Pull the bounded time-`k` multiplier out of conditional expectation and
    apply `A.condExp_zero`; use commutativity if the pull-out lemma is oriented
    with the measurable factor on the other side. -/
    intro n k hk
    let M := A.stopMultiplier ε K δ n k
    have hM : StronglyMeasurable[A.filtration n k] M :=
      A.stopMultiplier_stronglyMeasurable ε K δ n k hk
    have hX : Integrable (A.increment n k) (μ n) :=
      (A.squareIntegrable n k hk).integrable (by norm_num)
    have hMX : Integrable (fun ω => M ω * A.increment n k ω) (μ n) := by
      refine hX.bdd_mul (c := 1)
        (hM.mono ((A.filtration n).le k)).aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [M]
      unfold stopMultiplier
      split_ifs <;> simp
    have hpull : (μ n)[fun ω => M ω * A.increment n k ω |
        A.filtration n k] =ᵐ[μ n]
        fun ω => M ω * (μ n)[A.increment n k | A.filtration n k] ω :=
      condExp_mul_of_stronglyMeasurable_left hM hMX hX
    filter_upwards [hpull, A.condExp_zero n k hk] with ω hpullω hzeroω
    simpa only [M, Pi.zero_apply, mul_zero] using hpullω.trans
      (congrArg (M ω * ·) hzeroω)

/-- Stopping does not change the row length. -/
@[simp] theorem stoppedArray_rowLength
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (n : ℕ) :
    (A.stoppedArray ε K δ).rowLength n = A.rowLength n := rfl

/-- A stopped increment is the original increment multiplied by the predictable
zero-one stopping multiplier. -/
@[simp] theorem stoppedArray_increment
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (n k : ℕ) :
    (A.stoppedArray ε K δ).increment n k =
      fun ω => A.stopMultiplier ε K δ n k ω * A.increment n k ω := rfl

/-- If [the truncation threshold is positive](hyp:hε) and the original final predictable
variance and conditional Lindeberg mass stay within their budgets, then [predictable stopping
leaves the row sum unchanged almost everywhere](goal). -/
theorem stoppedArray_rowSum_ae_eq_of_bounds
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∀ᵐ ω ∂(μ n), A.predictableQuadraticVariation n ω ≤ K →
      A.conditionalLindeberg ε n ω ≤ δ →
        (A.stoppedArray ε K δ).rowSum n ω = A.rowSum n ω := by
  /- On one full-measure set all conditional second moments and Lindeberg
  terms in this finite row are nonnegative.  Hence each through-`k` sum is at
  most the corresponding final sum, every multiplier is one, and the finite
  row sums agree term by term. -/
  have hx : ∀ᵐ ω ∂(μ n), ∀ k,
      0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  have hy : ∀ᵐ ω ∂(μ n), ∀ k, 0 ≤ A.lindebergTerm ε n k ω := by
    apply ae_all_iff.mpr
    intro k
    apply condExp_nonneg
    filter_upwards with ω
    split_ifs <;> positivity
  filter_upwards [hx, hy] with ω hxω hyω
  intro hV hL
  unfold rowSum
  simp only [stoppedArray_rowLength, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k < A.rowLength n := Finset.mem_range.mp hk
  have hVr : A.predictableQuadraticVariationThrough n k ω ≤
      A.predictableQuadraticVariation n ω := by
    unfold predictableQuadraticVariationThrough predictableQuadraticVariation
    simp only [Finset.sum_apply]
    rw [min_eq_left (Nat.succ_le_iff.mpr hkr)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_iff.mpr hkr))
      (fun i hi _ => hxω i)
  have hLr : A.conditionalLindebergThrough ε n k ω ≤
      A.conditionalLindeberg ε n ω := by
    unfold conditionalLindebergThrough conditionalLindeberg
    simp only [Finset.sum_apply]
    rw [min_eq_left (Nat.succ_le_iff.mpr hkr)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_iff.mpr hkr))
      (fun i hi _ => hyω i)
  have hmul : A.stopMultiplier ε K δ n k ω = 1 := by
    rw [stopMultiplier, if_pos]
    exact And.intro (hVr.trans hV) (hLr.trans hL)
  simp only [stoppedArray_increment, hmul, one_mul]

/-- With [nonnegative variance and Lindeberg budgets](hyp:hK,hδ), [the stopped
row's predictable quadratic variation never exceeds the variance budget almost
everywhere](goal). -/
theorem stoppedArray_predictableQuadraticVariation_le
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (n : ℕ) :
    (A.stoppedArray ε K δ).predictableQuadraticVariation n ≤ᵐ[μ n]
      fun _ => K := by
  /- First prove the conditional second moment of a stopped increment is the
  original conditional second moment times its zero-one predictable
  multiplier.  On the common nonnegativity set the original prefix sums are
  monotone, so active indices form an initial segment and the selected sum is
  bounded by the last original through-sum that is at most `K`. -/
  have hmoment (k : ℕ) (hk : k < A.rowLength n) :
      (μ n)[fun ω => ((A.stoppedArray ε K δ).increment n k ω) ^ 2 |
          (A.stoppedArray ε K δ).filtration n k] =ᵐ[μ n]
        fun ω => A.stopMultiplier ε K δ n k ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω := by
    let M := A.stopMultiplier ε K δ n k
    have hsm : StronglyMeasurable[A.filtration n k] M :=
      A.stopMultiplier_stronglyMeasurable ε K δ n k hk
    have hsq : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
      (A.squareIntegrable n k hk).integrable_sq
    have hprod : Integrable (fun ω => M ω * (A.increment n k ω) ^ 2) (μ n) := by
      refine hsq.bdd_mul (c := 1)
        (hsm.mono ((A.filtration n).le k)).aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [M]
      unfold stopMultiplier
      split_ifs <;> simp
    calc
      (μ n)[fun ω => ((A.stoppedArray ε K δ).increment n k ω) ^ 2 |
          (A.stoppedArray ε K δ).filtration n k] =ᵐ[μ n]
          (μ n)[fun ω => M ω * (A.increment n k ω) ^ 2 | A.filtration n k] := by
            apply condExp_congr_ae
            filter_upwards with ω
            dsimp only [M]
            simp only [stoppedArray_increment]
            unfold stopMultiplier
            split_ifs <;> simp
      _ =ᵐ[μ n] fun ω => M ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
        condExp_mul_of_stronglyMeasurable_left hsm hprod hsq
  have hmoment_all : ∀ᵐ ω ∂(μ n), ∀ k, k < A.rowLength n →
      (μ n)[fun ω => ((A.stoppedArray ε K δ).increment n k ω) ^ 2 |
          (A.stoppedArray ε K δ).filtration n k] ω =
        A.stopMultiplier ε K δ n k ω *
          (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k < A.rowLength n
    · exact (hmoment k hk).mono fun ω hω _ => hω
    · exact ae_of_all _ fun _ h => (hk h).elim
  have hx : ∀ᵐ ω ∂(μ n), ∀ k,
      0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  have hy : ∀ᵐ ω ∂(μ n), ∀ k, 0 ≤ A.lindebergTerm ε n k ω := by
    apply ae_all_iff.mpr
    intro k
    apply condExp_nonneg
    filter_upwards with ω
    split_ifs <;> positivity
  filter_upwards [hmoment_all, hx, hy] with ω hmω hxω hyω
  unfold predictableQuadraticVariation
  simp only [Finset.sum_apply, stoppedArray_rowLength]
  calc
    (∑ k ∈ Finset.range (A.rowLength n),
        (μ n)[fun ω => ((A.stoppedArray ε K δ).increment n k ω) ^ 2 |
          (A.stoppedArray ε K δ).filtration n k] ω) =
        ∑ k ∈ Finset.range (A.rowLength n),
          budgetMultiplier
            (fun j => (μ n)[fun ω => (A.increment n j ω) ^ 2 |
              A.filtration n j] ω)
            (fun j => A.lindebergTerm ε n j ω) K δ k *
              (μ n)[fun ω => (A.increment n k ω) ^ 2 |
                A.filtration n k] ω := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hmω k (Finset.mem_range.mp hk)]
      congr 1
      unfold stopMultiplier budgetMultiplier predictableQuadraticVariationThrough
        conditionalLindebergThrough
      simp only [Finset.sum_apply]
      rw [min_eq_left (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))]
    _ ≤ K := (budgetWeightedSums_le
      (fun j => (μ n)[fun ω => (A.increment n j ω) ^ 2 | A.filtration n j] ω)
      (fun j => A.lindebergTerm ε n j ω) K δ (A.rowLength n)
      (fun k _ => hxω k) (fun k _ => hyω k) hK hδ).1

/-- With [a positive truncation threshold](hyp:hε) and [nonnegative variance
and Lindeberg budgets](hyp:hK,hδ), [the stopped row's conditional Lindeberg sum
at that threshold never exceeds its budget almost everywhere](goal). -/
theorem stoppedArray_conditionalLindeberg_le
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ)
    (hε : 0 < ε) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (n : ℕ) :
    (A.stoppedArray ε K δ).conditionalLindeberg ε n ≤ᵐ[μ n]
      fun _ => δ := by
  /- For `ε > 0`, truncating a zero-one multiple gives that multiplier times
  the original truncated square.  Pull it through conditional expectation;
  the same initial-segment argument as for predictable variance bounds the
  resulting selected Lindeberg sum by `δ`. -/
  have hmoment (k : ℕ) (hk : k < A.rowLength n) :
      (A.stoppedArray ε K δ).lindebergTerm ε n k =ᵐ[μ n]
        fun ω => A.stopMultiplier ε K δ n k ω * A.lindebergTerm ε n k ω := by
    let M := A.stopMultiplier ε K δ n k
    let g := fun ω => if ε < |A.increment n k ω| then
      (A.increment n k ω) ^ 2 else 0
    have hsm : StronglyMeasurable[A.filtration n k] M :=
      A.stopMultiplier_stronglyMeasurable ε K δ n k hk
    have hinc : StronglyMeasurable (A.increment n k) :=
      (A.adapted n k hk).mono ((A.filtration n).le (k + 1))
    have hgsm : StronglyMeasurable g := by
      apply StronglyMeasurable.ite
        (hinc.norm.measurable measurableSet_Ioi)
        (hinc.pow 2) stronglyMeasurable_const
    have hsq : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
      (A.squareIntegrable n k hk).integrable_sq
    have hg : Integrable g (μ n) := by
      refine hsq.mono hgsm.aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [g]
      split_ifs <;> simp [sq_nonneg]
    have hprod : Integrable (fun ω => M ω * g ω) (μ n) := by
      refine hg.bdd_mul (c := 1)
        (hsm.mono ((A.filtration n).le k)).aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [M]
      unfold stopMultiplier
      split_ifs <;> simp
    unfold lindebergTerm
    calc
      (μ n)[fun ω => if ε < |(A.stoppedArray ε K δ).increment n k ω| then
          ((A.stoppedArray ε K δ).increment n k ω) ^ 2 else 0 |
          (A.stoppedArray ε K δ).filtration n k] =ᵐ[μ n]
          (μ n)[fun ω => M ω * g ω | A.filtration n k] := by
            apply condExp_congr_ae
            filter_upwards with ω
            dsimp only [M, g]
            simp only [stoppedArray_increment]
            unfold stopMultiplier
            split_ifs <;> simp_all
      _ =ᵐ[μ n] fun ω => M ω * (μ n)[g | A.filtration n k] ω :=
        condExp_mul_of_stronglyMeasurable_left hsm hprod hg
  have hmoment_all : ∀ᵐ ω ∂(μ n), ∀ k, k < A.rowLength n →
      (A.stoppedArray ε K δ).lindebergTerm ε n k ω =
        A.stopMultiplier ε K δ n k ω * A.lindebergTerm ε n k ω := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k < A.rowLength n
    · exact (hmoment k hk).mono fun ω hω _ => hω
    · exact ae_of_all _ fun _ h => (hk h).elim
  have hx : ∀ᵐ ω ∂(μ n), ∀ k,
      0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k] ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  have hy : ∀ᵐ ω ∂(μ n), ∀ k, 0 ≤ A.lindebergTerm ε n k ω := by
    apply ae_all_iff.mpr
    intro k
    apply condExp_nonneg
    filter_upwards with ω
    split_ifs <;> positivity
  filter_upwards [hmoment_all, hx, hy] with ω hmω hxω hyω
  unfold conditionalLindeberg
  simp only [Finset.sum_apply, stoppedArray_rowLength]
  calc
    (∑ k ∈ Finset.range (A.rowLength n),
        (A.stoppedArray ε K δ).lindebergTerm ε n k ω) =
        ∑ k ∈ Finset.range (A.rowLength n),
          budgetMultiplier
            (fun j => (μ n)[fun ω => (A.increment n j ω) ^ 2 |
              A.filtration n j] ω)
            (fun j => A.lindebergTerm ε n j ω) K δ k *
              A.lindebergTerm ε n k ω := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hmω k (Finset.mem_range.mp hk)]
      congr 1
      unfold stopMultiplier budgetMultiplier predictableQuadraticVariationThrough
        conditionalLindebergThrough
      simp only [Finset.sum_apply]
      rw [min_eq_left (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))]
    _ ≤ δ := (budgetWeightedSums_le
      (fun j => (μ n)[fun ω => (A.increment n j ω) ^ 2 | A.filtration n j] ω)
      (fun j => A.lindebergTerm ε n j ω) K δ (A.rowLength n)
      (fun k _ => hxω k) (fun k _ => hyω k) hK hδ).2

/-- For [a positive truncation threshold](hyp:hε), [the probability that
stopping changes a row sum is bounded by the probability that the original
row exceeds either stopping budget](goal). -/
theorem measure_stoppedArray_rowSum_ne_le
    (A : MartingaleDifferenceArray Ω μ) (ε K δ : ℝ) (hε : 0 < ε) (n : ℕ) :
    (μ n) {ω | (A.stoppedArray ε K δ).rowSum n ω ≠ A.rowSum n ω} ≤
      (μ n) {ω | K < A.predictableQuadraticVariation n ω ∨
        δ < A.conditionalLindeberg ε n ω} := by
  /- Convert `stoppedArray_rowSum_ae_eq_of_bounds` to an a.e. inclusion of the
  disagreement event in the union of the two strict budget violations, then
  apply `measure_mono_ae`. -/
  apply measure_mono_ae
  filter_upwards [A.stoppedArray_rowSum_ae_eq_of_bounds ε K δ hε n] with ω hω
  intro hne
  by_contra hbudgets
  change ¬(K < A.predictableQuadraticVariation n ω ∨
    δ < A.conditionalLindeberg ε n ω) at hbudgets
  simp only [not_or, not_lt] at hbudgets
  change (A.stoppedArray ε K δ).rowSum n ω ≠ A.rowSum n ω at hne
  exact hne (hω hbudgets.1 hbudgets.2)

end FiniteMeasure

end MartingaleDifferenceArray

end Causalean.Stat

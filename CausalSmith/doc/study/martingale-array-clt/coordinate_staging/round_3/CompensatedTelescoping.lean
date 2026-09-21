/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.CompensatedStep
import Causalean.Stat.CLT.MartingaleArray.PredictableVarianceBounds
import Causalean.Stat.CLT.MartingaleArray.RemainderBudget

/-! # Finite-row compensated Gaussian telescoping

This module telescopes the one-step compensated characteristic-function bound.
It also removes the terminal random Gaussian correction by an explicit expected
absolute predictable-variance error.  These are deterministic finite-row
bounds; the asymptotic stopping argument remains in `CharacteristicFunction`.
-/

namespace Causalean.Stat

open Complex Filter MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- If [the truncation threshold is positive](hyp:hη), [the frequency-threshold product is at
most one](hyp:htη), [both budgets are nonnegative](hyp:hK,hδ), [a row's predictable quadratic
variation is at most `K`](hyp:hVariance), and [its conditional Lindeberg mass at threshold
`η` is at most `δ`](hyp:hLindeberg),
then [the integrated compensated row characteristic function differs from the
standard Gaussian characteristic function by the displayed Taylor and
predictable-mesh budget](goal). -/
theorem norm_integral_compensatedWeight_rowSum_sub_gaussian_le_of_budgets
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) (t η K δ : ℝ)
    (hη : 0 < η) (htη : |t| * η ≤ 1) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hVariance : A.predictableQuadraticVariation n ≤ᵐ[μ n] fun _ => K)
    (hLindeberg : A.conditionalLindeberg η n ≤ᵐ[μ n] fun _ => δ) :
    ‖(∫ ω, A.compensatedWeight n (A.rowLength n) t ω ∂(μ n)) -
        ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      Real.exp ((t ^ 2 / 2) * K) *
        (|t| ^ 3 * η * K +
          (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ +
          ((t ^ 2 / 2) ^ 2 / 2) * ((η ^ 2 + δ) * K)) := by
  /- Telescope `norm_integral_compensatedWeight_succ_sub_le`.  Nonnegativity of
  conditional second moments makes every partial predictable variation at most
  the final one.  Sum the one-step bounds, then invoke the closed row remainder
  and squared-mesh budget lemmas.  The time-zero weight integrates to
  `exp (-(t^2/2))`. -/
  let F : ℕ → ℂ := fun r =>
    ∫ ω, A.compensatedWeight n r t ω ∂(μ n)
  let R : ℕ → ℝ := fun k =>
    ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n)
  let V₂ : ℕ → ℝ := fun k =>
    ∫ ω, (A.conditionalSecondMoment n k ω) ^ 2 ∂(μ n)
  let c : ℝ := t ^ 2 / 2
  have hvNonneg : ∀ᵐ ω ∂(μ n), ∀ k,
      0 ≤ A.conditionalSecondMoment n k ω :=
    ae_all_iff.mpr fun k => by
      unfold conditionalSecondMoment
      exact condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (A.increment n k ω))
  have hPartial : ∀ k < A.rowLength n,
      A.partialPredictableQuadraticVariation n (k + 1) ≤ᵐ[μ n]
        fun _ => K := by
    intro k hk
    filter_upwards [hvNonneg, hVariance] with ω hvω hVarianceω
    apply le_trans _ hVarianceω
    unfold partialPredictableQuadraticVariation predictableQuadraticVariation
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hk)]
    simp only [Finset.sum_apply]
    change (∑ j ∈ Finset.range (k + 1),
      A.conditionalSecondMoment n j ω) ≤
      ∑ j ∈ Finset.range (A.rowLength n),
        A.conditionalSecondMoment n j ω
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_of_lt hk))
    intro j _ _
    exact hvω j
  have hstep : ∀ k < A.rowLength n,
      ‖F (k + 1) - F k‖ ≤
        Real.exp (c * K) * (R k + (c ^ 2 / 2) * V₂ k) := by
    intro k hk
    simpa only [F, R, V₂, c] using
      A.norm_integral_compensatedWeight_succ_sub_le
        n k hk t K hK (hPartial k hk)
  have hF0 : F 0 = ((Real.exp (-c) : ℝ) : ℂ) := by
    simp [F, compensatedWeight, partialRowSum,
      partialPredictableQuadraticVariation, c]
  have hRem := A.sum_integral_norm_expQuadraticRemainder_le_of_budgets
    n t η K δ hη htη hK hδ hVariance hLindeberg
  have hV₂ := A.sum_sq_conditionalSecondMoment_le_of_budgets
    n η K δ hη hK hδ hVariance hLindeberg
  have hV₂int : (∑ k ∈ Finset.range (A.rowLength n), V₂ k) ≤
      (η ^ 2 + δ) * K := by
    have hEach : ∀ k ∈ Finset.range (A.rowLength n),
        Integrable (fun ω => (A.conditionalSecondMoment n k ω) ^ 2) (μ n) := by
      intro k hk
      have hce : Integrable (A.conditionalSecondMoment n k) (μ n) :=
        integrable_condExp
      have hbound : A.conditionalSecondMoment n k ≤ᵐ[μ n] fun _ => K := by
        filter_upwards [hvNonneg, hPartial k (Finset.mem_range.mp hk)]
          with ω hvω hpω
        have hsucc := congrFun
          (A.partialPredictableQuadraticVariation_succ n k
            (Finset.mem_range.mp hk)) ω
        simp only [Pi.add_apply] at hsucc
        have hpartialNonneg :
            0 ≤ A.partialPredictableQuadraticVariation n k ω := by
          unfold partialPredictableQuadraticVariation
          simp only [Finset.sum_apply]
          exact Finset.sum_nonneg fun j _ => hvω j
        linarith
      refine Integrable.mono' (integrable_const (K ^ 2))
        (hce.aestronglyMeasurable.pow 2) ?_
      filter_upwards [hvNonneg, hbound] with ω hvω hboundω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hboundω)
        (add_nonneg hK (hvω k))]
    calc
      (∑ k ∈ Finset.range (A.rowLength n), V₂ k) =
          ∫ ω, ∑ k ∈ Finset.range (A.rowLength n),
            (A.conditionalSecondMoment n k ω) ^ 2 ∂(μ n) := by
        rw [integral_finsetSum _ hEach]
      _ ≤ ∫ _ω, (η ^ 2 + δ) * K ∂(μ n) := by
        apply integral_mono_ae
        · exact integrable_finsetSum _ hEach
        · exact integrable_const _
        · exact hV₂
      _ = (η ^ 2 + δ) * K := by simp
  have htel : F (A.rowLength n) - F 0 =
      ∑ k ∈ Finset.range (A.rowLength n), (F (k + 1) - F k) := by
    rw [Finset.sum_range_sub]
  rw [hF0] at htel
  change ‖F (A.rowLength n) - ((Real.exp (-c) : ℝ) : ℂ)‖ ≤ _
  rw [htel]
  calc
    ‖∑ k ∈ Finset.range (A.rowLength n), (F (k + 1) - F k)‖ ≤
        ∑ k ∈ Finset.range (A.rowLength n), ‖F (k + 1) - F k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (A.rowLength n),
        Real.exp (c * K) * (R k + (c ^ 2 / 2) * V₂ k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hstep k (Finset.mem_range.mp hk)
    _ = Real.exp (c * K) *
        ((∑ k ∈ Finset.range (A.rowLength n), R k) +
          (c ^ 2 / 2) * ∑ k ∈ Finset.range (A.rowLength n), V₂ k) := by
      calc
        (∑ k ∈ Finset.range (A.rowLength n),
            Real.exp (c * K) * (R k + (c ^ 2 / 2) * V₂ k)) =
            (∑ k ∈ Finset.range (A.rowLength n),
              Real.exp (c * K) * R k) +
            ∑ k ∈ Finset.range (A.rowLength n),
              Real.exp (c * K) * ((c ^ 2 / 2) * V₂ k) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = Real.exp (c * K) *
              (∑ k ∈ Finset.range (A.rowLength n), R k) +
            Real.exp (c * K) *
              (∑ k ∈ Finset.range (A.rowLength n),
                (c ^ 2 / 2) * V₂ k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := by
          have hscale :
              (∑ k ∈ Finset.range (A.rowLength n),
                (c ^ 2 / 2) * V₂ k) =
              (c ^ 2 / 2) *
                ∑ k ∈ Finset.range (A.rowLength n), V₂ k := by
            rw [Finset.mul_sum]
          rw [hscale]
          ring
    _ ≤ Real.exp (c * K) *
        ((|t| ^ 3 * η * K +
          (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ) +
          (c ^ 2 / 2) * ((η ^ 2 + δ) * K)) := by
      gcongr
    _ = _ := by rfl

/-- If [the truncation threshold is positive](hyp:hη), [the frequency-threshold product is at
most one](hyp:htη), [both budgets are nonnegative](hyp:hK,hδ), [a row's predictable quadratic
variation is at most `K`](hyp:hVariance), and [its conditional Lindeberg mass at threshold
`η` is at most `δ`](hyp:hLindeberg),
then [its ordinary characteristic function differs from the standard Gaussian
characteristic function by the compensated budget plus a constant times the
expected distance of predictable quadratic variation from one](goal). -/
theorem norm_integral_cexp_rowSum_sub_gaussian_le_of_budgets
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) (t η K δ : ℝ)
    (hη : 0 < η) (htη : |t| * η ≤ 1) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hVariance : A.predictableQuadraticVariation n ≤ᵐ[μ n] fun _ => K)
    (hLindeberg : A.conditionalLindeberg η n ≤ᵐ[μ n] fun _ => δ) :
    ‖(∫ ω, Complex.exp (Complex.I *
          ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
        ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      Real.exp ((t ^ 2 / 2) * K) *
          (|t| ^ 3 * η * K +
            (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ +
            ((t ^ 2 / 2) ^ 2 / 2) * ((η ^ 2 + δ) * K)) +
        Real.exp ((t ^ 2 / 2) * max K 1) * (t ^ 2 / 2) *
          ∫ ω, |A.predictableQuadraticVariation n ω - 1| ∂(μ n) := by
  /- Insert the compensated terminal integral and use the preceding theorem.
  The unit-modulus characteristic weight removes from the other difference;
  apply `abs_exp_varianceCorrection_sub_one_le` pointwise and integrate. -/
  let c : ℝ := t ^ 2 / 2
  let V : Ω n → ℝ := A.predictableQuadraticVariation n
  let g : Ω n → ℂ := fun ω =>
    Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ))
  let q : Ω n → ℂ := fun ω =>
    ((Real.exp (c * (V ω - 1)) : ℝ) : ℂ)
  let W : Ω n → ℂ := fun ω => g ω * q ω
  let C : ℝ := Real.exp (c * max K 1) * c
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hVInt : Integrable V (μ n) := by
    dsimp [V]
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
  have hVNonneg : 0 ≤ᵐ[μ n] V := by
    have hall : ∀ᵐ ω ∂(μ n), ∀ k,
        0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 2 |
          A.filtration n k] ω :=
      ae_all_iff.mpr fun k =>
        condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (A.increment n k ω))
    filter_upwards [hall] with ω hω
    dsimp [V]
    unfold predictableQuadraticVariation
    simp only [Finset.sum_apply]
    exact Finset.sum_nonneg fun k _ => hω k
  have hgMeas : AEStronglyMeasurable g (μ n) := by
    have hrow := A.rowSum_aemeasurable n
    dsimp [g]
    fun_prop
  have hgInt : Integrable g (μ n) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hgMeas ?_
    filter_upwards with ω
    dsimp [g]
    rw [Complex.norm_exp]
    simp
  have hWMeas : AEStronglyMeasurable W (μ n) := by
    have hqMeas : AEStronglyMeasurable q (μ n) := by
      have hVm := hVInt.aestronglyMeasurable
      dsimp [q]
      fun_prop
    exact hgMeas.mul hqMeas
  have hWBound : ∀ᵐ ω ∂(μ n), ‖W ω‖ ≤ Real.exp (c * K) := by
    filter_upwards [hVariance] with ω hVω
    have harg : c * (V ω - 1) ≤ c * K := by
      apply mul_le_mul_of_nonneg_left _ hc
      dsimp [V]
      linarith
    calc
      ‖W ω‖ = Real.exp (c * (V ω - 1)) := by
        dsimp [W, g, q]
        rw [norm_mul, Complex.norm_exp, Complex.norm_real]
        simp
      _ ≤ Real.exp (c * K) := Real.exp_le_exp.mpr harg
  have hWInt : Integrable W (μ n) :=
    Integrable.mono' (integrable_const (Real.exp (c * K))) hWMeas hWBound
  have hAbsVInt : Integrable (fun ω => |V ω - 1|) (μ n) :=
    (hVInt.sub (integrable_const 1)).abs
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hNormDiff : ∀ ω, ‖g ω - W ω‖ =
      |Real.exp (c * (V ω - 1)) - 1| := by
    intro ω
    dsimp [W, g, q]
    rw [show Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) *
          ((Real.exp (c * (V ω - 1)) : ℝ) : ℂ) =
        Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) *
          (1 - ((Real.exp (c * (V ω - 1)) : ℝ) : ℂ)) by ring]
    rw [norm_mul]
    have hchar : ‖Complex.exp
        (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hchar, one_mul]
    rw [show (1 : ℂ) - ((Real.exp (c * (V ω - 1)) : ℝ) : ℂ) =
        (((1 - Real.exp (c * (V ω - 1))) : ℝ) : ℂ) by
          rw [Complex.ofReal_sub, Complex.ofReal_one]]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hDiff : ‖(∫ ω, g ω ∂(μ n)) - ∫ ω, W ω ∂(μ n)‖ ≤
      C * ∫ ω, |V ω - 1| ∂(μ n) := by
    rw [← integral_sub hgInt hWInt]
    calc
      ‖∫ ω, g ω - W ω ∂(μ n)‖ ≤
          ∫ ω, ‖g ω - W ω‖ ∂(μ n) :=
        norm_integral_le_integral_norm _
      _ = ∫ ω, |Real.exp (c * (V ω - 1)) - 1| ∂(μ n) := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hNormDiff ω
      _ ≤ ∫ ω, C * |V ω - 1| ∂(μ n) := by
        apply integral_mono_ae
        · exact (hgInt.sub hWInt).norm.congr (ae_of_all _ hNormDiff)
        · exact hAbsVInt.const_mul C
        · filter_upwards [hVNonneg, hVariance] with ω hV0 hVK
          dsimp [C]
          exact abs_exp_varianceCorrection_sub_one_le c (V ω) K hc hV0
            (by simpa only [V] using hVK)
      _ = C * ∫ ω, |V ω - 1| ∂(μ n) := integral_const_mul _ _
  have hTerminal : A.compensatedWeight n (A.rowLength n) t = W := by
    funext ω
    dsimp [W, g, q, V, c, compensatedWeight]
    simp [partialRowSum, rowSum, partialPredictableQuadraticVariation,
      predictableQuadraticVariation, conditionalSecondMoment]
  have hComp :=
    A.norm_integral_compensatedWeight_rowSum_sub_gaussian_le_of_budgets
      n t η K δ hη htη hK hδ hVariance hLindeberg
  rw [hTerminal] at hComp
  change ‖(∫ ω, g ω ∂(μ n)) -
      ((Real.exp (-c) : ℝ) : ℂ)‖ ≤ _
  calc
    ‖(∫ ω, g ω ∂(μ n)) - ((Real.exp (-c) : ℝ) : ℂ)‖ =
        ‖((∫ ω, g ω ∂(μ n)) - ∫ ω, W ω ∂(μ n)) +
          ((∫ ω, W ω ∂(μ n)) - ((Real.exp (-c) : ℝ) : ℂ))‖ := by
      congr 1
      ring
    _ ≤ ‖(∫ ω, g ω ∂(μ n)) - ∫ ω, W ω ∂(μ n)‖ +
        ‖(∫ ω, W ω ∂(μ n)) - ((Real.exp (-c) : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ C * ∫ ω, |V ω - 1| ∂(μ n) +
        Real.exp (c * K) *
          (|t| ^ 3 * η * K +
            (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * δ +
            (c ^ 2 / 2) * ((η ^ 2 + δ) * K)) :=
      add_le_add hDiff (by simpa only [c] using hComp)
    _ = _ := by
      dsimp [C, V, c]
      ring

end MartingaleDifferenceArray

end Causalean.Stat

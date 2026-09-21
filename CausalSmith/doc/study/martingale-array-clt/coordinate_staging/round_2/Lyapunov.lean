/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Reusable sufficient conditions for martingale-array CLTs

This module provides bridges from deterministic predictable variance and from
fourth-moment Lyapunov conditions to the convergence-in-probability hypotheses
of the martingale-array central limit theorem.  No independence between
increments is assumed.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

/-- If [the predictable quadratic variation equals a deterministic scalar in every
row](hyp:hEq) and [those scalars converge to one](hyp:hv), then [the predictable quadratic
variation converges in probability to one](goal). -/
theorem predictableQuadraticVariation_tendstoInProbability_of_ae_eq
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (v : ℕ → ℝ)
    (hEq : ∀ n, A.predictableQuadraticVariation n =ᵐ[μ n] fun _ => v n)
    (hv : Tendsto v atTop (𝓝 1)) :
    TendstoInProbability μ A.predictableQuadraticVariation 1 := by
  intro ε hε
  have hAbs : Tendsto (fun n => |v n - 1|) atTop (𝓝 0) := by
    simpa using
      (hv.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs
  have hEventually : ∀ᶠ n in atTop, |v n - 1| < ε :=
    ((tendsto_order.1 hAbs).2 ε hε)
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hEventually] with n hn
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hEq n] with ω hω
  rw [hω]
  exact not_le_of_gt hn

/-- If [every increment has a finite fourth moment](hyp:hFourth) and [the conditional
fourth-moment row sums converge in probability to zero](hyp:hFourthConditional), then [the
conditional Lindeberg condition holds at every positive threshold](goal). -/
theorem conditionalLindeberg_of_conditionalFourthMoment
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthConditional :
      TendstoInProbability μ A.conditionalFourthMoment 0) :
    ∀ ε : ℝ, 0 < ε →
      TendstoInProbability μ (A.conditionalLindeberg ε) 0 := by
  /-
  Proof route: pointwise, on `ε < |x|`, one has
  `x^2 ≤ ε⁻² * x^4`.  Apply conditional-expectation monotonicity term by
  term, sum the resulting a.e. inequalities, and use the squeeze property for
  convergence in measure.  `hFourth` supplies integrability on both sides.
  -/
  intro ε hε
  let c : ℝ := ε⁻¹ ^ 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hFourthIntegrable : ∀ n k, k < A.rowLength n →
      Integrable (fun ω => (A.increment n k ω) ^ 4) (μ n) := by
    intro n k hk
    have hi := (hFourth n k hk).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : 0 ≤ A.increment n k _ ^ 4)] using hi
  have hTruncatedIntegrable : ∀ n k, k < A.rowLength n →
      Integrable (fun ω => if ε < |A.increment n k ω| then
        (A.increment n k ω) ^ 2 else 0) (μ n) := by
    intro n k hk
    have h2 := A.squareIntegrable n k hk
    have hsquare : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
      (memLp_two_iff_integrable_sq h2.aestronglyMeasurable).mp h2
    have hset : NullMeasurableSet {ω | ε < |A.increment n k ω|} (μ n) :=
      aestronglyMeasurable_const.nullMeasurableSet_lt h2.aestronglyMeasurable.norm
    apply (hsquare.indicator₀ hset).congr
    filter_upwards [] with ω
    by_cases hω : ε < |A.increment n k ω| <;> simp [Set.indicator, hω]
  have hPointwise : ∀ n k, k < A.rowLength n →
      (fun ω => if ε < |A.increment n k ω| then
        (A.increment n k ω) ^ 2 else 0) ≤ᵐ[μ n]
      (fun ω => c * (A.increment n k ω) ^ 4) := by
    intro n k hk
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [c]
      by_cases hω : ε < |A.increment n k ω|
      · rw [if_pos hω]
        have he2 : ε ^ 2 ≤ (A.increment n k ω) ^ 2 := by
          rw [sq_le_sq]
          simpa [abs_of_pos hε] using hω.le
        have hc' : 0 ≤ ε⁻¹ ^ 2 := sq_nonneg _
        calc
          (A.increment n k ω) ^ 2 =
              ε⁻¹ ^ 2 * (ε ^ 2 * (A.increment n k ω) ^ 2) := by field_simp
          _ ≤ ε⁻¹ ^ 2 * ((A.increment n k ω) ^ 2 *
              (A.increment n k ω) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right he2 (sq_nonneg _)) hc'
          _ = ε⁻¹ ^ 2 * (A.increment n k ω) ^ 4 := by ring
      · rw [if_neg hω]
        positivity
  have hTermBound : ∀ n k, k < A.rowLength n →
      A.lindebergTerm ε n k ≤ᵐ[μ n]
        fun ω => c * (μ n)[fun ω => (A.increment n k ω) ^ 4 |
          A.filtration n k] ω := by
    intro n k hk
    have hpointwise' : (fun ω => if ε < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0) ≤ᵐ[μ n]
        c • (fun ω => (A.increment n k ω) ^ 4) :=
      (hPointwise n k hk).mono fun ω hω => by
        simpa only [Pi.smul_apply, smul_eq_mul] using hω
    have hmono := condExp_mono (m := A.filtration n k) (hTruncatedIntegrable n k hk)
      ((hFourthIntegrable n k hk).smul c) hpointwise'
    have hlinear := condExp_smul (μ := μ n) c (fun ω => (A.increment n k ω) ^ 4)
      (A.filtration n k)
    filter_upwards [hmono, hlinear] with ω hmonoω hlinearω
    unfold MartingaleDifferenceArray.lindebergTerm
    calc
      (μ n)[fun ω => if ε < |A.increment n k ω| then
          (A.increment n k ω) ^ 2 else 0 | A.filtration n k] ω
          ≤ (μ n)[c • fun ω => (A.increment n k ω) ^ 4 |
              A.filtration n k] ω := hmonoω
      _ = c * (μ n)[fun ω => (A.increment n k ω) ^ 4 |
              A.filtration n k] ω := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hlinearω
  have hLNonneg : ∀ n, 0 ≤ᵐ[μ n] A.conditionalLindeberg ε n := by
    intro n
    have hall : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
        0 ≤ A.lindebergTerm ε n k ω :=
      (Finset.eventually_all _).mpr fun k hk =>
        condExp_nonneg (Filter.Eventually.of_forall fun ω => by
          change (0 : ℝ) ≤ if ε < |A.increment n k ω| then
            (A.increment n k ω) ^ 2 else 0
          split_ifs <;> positivity)
    filter_upwards [hall] with ω hω
    unfold MartingaleDifferenceArray.conditionalLindeberg
    simp only [Pi.zero_apply, Finset.sum_apply]
    exact Finset.sum_nonneg fun k hk => hω k hk
  have hFNonneg : ∀ n, 0 ≤ᵐ[μ n] A.conditionalFourthMoment n := by
    intro n
    have hall : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
        0 ≤ (μ n)[fun ω => (A.increment n k ω) ^ 4 | A.filtration n k] ω :=
      (Finset.eventually_all _).mpr fun k hk =>
        condExp_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
    filter_upwards [hall] with ω hω
    unfold MartingaleDifferenceArray.conditionalFourthMoment
    simp only [Pi.zero_apply, Finset.sum_apply]
    exact Finset.sum_nonneg fun k hk => hω k hk
  have hBound : ∀ n, A.conditionalLindeberg ε n ≤ᵐ[μ n]
      fun ω => c * A.conditionalFourthMoment n ω := by
    intro n
    have hall : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
        A.lindebergTerm ε n k ω ≤
          c * (μ n)[fun ω => (A.increment n k ω) ^ 4 | A.filtration n k] ω :=
      (Finset.eventually_all _).mpr fun k hk =>
        hTermBound n k (Finset.mem_range.mp hk)
    filter_upwards [hall] with ω hω
    unfold MartingaleDifferenceArray.conditionalLindeberg
      MartingaleDifferenceArray.conditionalFourthMoment
    rw [Finset.sum_apply, Finset.sum_apply]
    calc
      ∑ k ∈ Finset.range (A.rowLength n), A.lindebergTerm ε n k ω
          ≤ ∑ k ∈ Finset.range (A.rowLength n),
              c * (μ n)[fun ω => (A.increment n k ω) ^ 4 |
                A.filtration n k] ω := Finset.sum_le_sum fun k hk => hω k hk
      _ = c * ∑ k ∈ Finset.range (A.rowLength n),
              (μ n)[fun ω => (A.increment n k ω) ^ 4 |
                A.filtration n k] ω := by rw [Finset.mul_sum]
  intro δ hδ
  have hUpper := hFourthConditional (δ / c) (div_pos hδ hc)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => bot_le) (fun n => measure_mono_ae <| by
      filter_upwards [hLNonneg n, hFNonneg n, hBound n] with ω hL hF hLF
      intro hω
      change δ ≤ |A.conditionalLindeberg ε n ω - 0| at hω
      change δ / c ≤ |A.conditionalFourthMoment n ω - 0|
      rw [sub_zero, abs_of_nonneg hL] at hω
      rw [sub_zero, abs_of_nonneg hF]
      apply (div_le_iff₀ hc).mpr
      simpa only [mul_comm] using hω.trans hLF)

/-- If [every increment has a finite fourth moment](hyp:hFourth) and [the deterministic
sum of unconditional fourth moments tends to zero](hyp:hFourthSum), then [the conditional
fourth-moment row sums converge in probability to zero](goal). -/
theorem conditionalFourthMoment_tendstoInProbability_of_fourthMomentSum
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthSum : Tendsto A.fourthMomentSum atTop (𝓝 0)) :
    TendstoInProbability μ A.conditionalFourthMoment 0 := by
  /-
  Proof route: the conditional fourth-moment sum is nonnegative a.e. and its
  integral is `fourthMomentSum A n` by the conditional-expectation integral
  identity.  Markov's inequality then bounds its upper tail by that
  deterministic expectation, which tends to zero.
  -/
  intro δ hδ
  have hNonneg : ∀ n, 0 ≤ᵐ[μ n] A.conditionalFourthMoment n := by
    intro n
    unfold MartingaleDifferenceArray.conditionalFourthMoment
    induction Finset.range (A.rowLength n) using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall fun _ => by simp
    | @insert k s hk ih =>
        have hk_nonneg : 0 ≤ᵐ[μ n]
            (μ n)[fun ω => (A.increment n k ω) ^ 4 | A.filtration n k] :=
          condExp_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
        filter_upwards [ih, hk_nonneg] with ω hsum hterm
        simpa [hk] using add_nonneg hterm hsum
  have hIntegrable : ∀ n, Integrable (A.conditionalFourthMoment n) (μ n) := by
    intro n
    unfold MartingaleDifferenceArray.conditionalFourthMoment
    rw [Finset.sum_fn]
    apply integrable_finsetSum
    intro k hk
    exact integrable_condExp
  have hFourthIntegrable : ∀ n k, k < A.rowLength n →
      Integrable (fun ω => (A.increment n k ω) ^ 4) (μ n) := by
    intro n k hk
    have hi := (hFourth n k hk).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : 0 ≤ A.increment n k _ ^ 4)] using hi
  have hIntegral : ∀ n, ∫ ω, A.conditionalFourthMoment n ω ∂(μ n) =
      A.fourthMomentSum n := by
    intro n
    unfold MartingaleDifferenceArray.conditionalFourthMoment
      MartingaleDifferenceArray.fourthMomentSum
    rw [Finset.sum_fn]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      simpa only [setIntegral_univ] using
        setIntegral_condExp (A.filtration n |>.le k)
          (hFourthIntegrable n k (Finset.mem_range.mp hk)) MeasurableSet.univ
    · intro k hk
      exact integrable_condExp
  apply (ENNReal.tendsto_toReal_zero_iff).mp
  refine squeeze_zero (g := fun n => A.fourthMomentSum n / δ)
    (fun _ => measureReal_nonneg) ?_ ?_
  · intro n
    have hEvents : {ω | δ ≤ |A.conditionalFourthMoment n ω - 0|} =ᵐ[μ n]
        {ω | δ ≤ A.conditionalFourthMoment n ω} := by
      filter_upwards [hNonneg n] with ω hω
      change 0 ≤ A.conditionalFourthMoment n ω at hω
      apply propext
      change (δ ≤ |A.conditionalFourthMoment n ω - 0| ↔
        δ ≤ A.conditionalFourthMoment n ω)
      rw [sub_zero, abs_of_nonneg hω]
    change ((μ n) {ω | δ ≤ |A.conditionalFourthMoment n ω - 0|}).toReal ≤ _
    rw [measure_congr hEvents, ← measureReal_def]
    apply (le_div_iff₀ hδ).2
    calc
      Measure.real (μ n) {ω | δ ≤ A.conditionalFourthMoment n ω} * δ =
          δ * Measure.real (μ n) {ω | δ ≤ A.conditionalFourthMoment n ω} :=
        mul_comm _ _
      _ ≤ ∫ ω, A.conditionalFourthMoment n ω ∂(μ n) :=
        mul_meas_ge_le_integral_of_nonneg (hNonneg n) (hIntegrable n) δ
      _ = A.fourthMomentSum n := hIntegral n
  · simpa using hFourthSum.div_const δ

/-- If [every increment has a finite fourth moment](hyp:hFourth) and [the deterministic
sum of unconditional fourth moments tends to zero](hyp:hFourthSum), then [the conditional
Lindeberg condition holds at every positive threshold](goal). -/
theorem conditionalLindeberg_of_fourthMomentSum
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthSum : Tendsto A.fourthMomentSum atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      TendstoInProbability μ (A.conditionalLindeberg ε) 0 := by
  apply conditionalLindeberg_of_conditionalFourthMoment A hFourth
  exact conditionalFourthMoment_tendstoInProbability_of_fourthMomentSum
    A hFourth hFourthSum

end Causalean.Stat

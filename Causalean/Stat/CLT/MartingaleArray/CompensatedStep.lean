/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.ConditionalTelescoping
import Causalean.Stat.CLT.MartingaleArray.GaussianBounds

/-! # One-step compensated characteristic-function bounds

This module introduces the predictable-variance compensation used in the
martingale-array CLT.  It proves the exact conditional update and its one-step
error bound before any finite-row telescoping or asymptotic argument.
-/

namespace Causalean.Stat

open Complex Filter MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- The conditional second moment of one increment, given the filtration just
before that increment, is its one-step predictable variance. -/
noncomputable def conditionalSecondMoment
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ) : Ω n → ℝ :=
  (μ n)[fun ω => (A.increment n k ω) ^ 2 | A.filtration n k]

/-- The partial predictable quadratic variation through time `r` sums the
one-step predictable variances of the first `r` active increments. -/
noncomputable def partialPredictableQuadraticVariation
    (A : MartingaleDifferenceArray Ω μ) (n r : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (min r (A.rowLength n)), A.conditionalSecondMoment n k

/-- The partial predictable quadratic variation at time zero is zero. -/
@[simp] theorem partialPredictableQuadraticVariation_zero
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) :
    A.partialPredictableQuadraticVariation n 0 = 0 := by
  simp [partialPredictableQuadraticVariation]

/-- For [an active increment](hyp:hk), [the next partial predictable quadratic
variation is the current one plus that increment's conditional second
moment](goal). -/
theorem partialPredictableQuadraticVariation_succ
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) :
    A.partialPredictableQuadraticVariation n (k + 1) =
      A.partialPredictableQuadraticVariation n k + A.conditionalSecondMoment n k := by
  /- Rewrite both capped ranges using `hk`, then apply
  `Finset.sum_range_succ` pointwise. -/
  unfold partialPredictableQuadraticVariation
  rw [Nat.min_eq_left (Nat.succ_le_of_lt hk)]
  rw [Nat.min_eq_left (le_trans (Nat.le_succ k) (Nat.succ_le_of_lt hk))]
  exact Finset.sum_range_succ _ _

/-- The partial predictable quadratic variation through time `r` is measurable
with respect to the row filtration at time `r`. -/
theorem partialPredictableQuadraticVariation_stronglyMeasurable
    (A : MartingaleDifferenceArray Ω μ) (n r : ℕ) :
    StronglyMeasurable[A.filtration n r]
      (A.partialPredictableQuadraticVariation n r) := by
  /- Each conditional second moment is strongly measurable at its conditioning
  time.  Lift it to time `r` using filtration monotonicity and close the finite
  sum. -/
  unfold partialPredictableQuadraticVariation conditionalSecondMoment
  apply Finset.stronglyMeasurable_sum
  intro k hk
  exact stronglyMeasurable_condExp.mono ((A.filtration n).mono
    (le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) (min_le_left _ _)))

/-- The compensated characteristic-function weight at time `r` is the ordinary
characteristic-function weight multiplied by the Gaussian correction generated
by the partial predictable quadratic variation. -/
noncomputable def compensatedWeight
    (A : MartingaleDifferenceArray Ω μ) (n r : ℕ) (t : ℝ) : Ω n → ℂ :=
  fun ω => Complex.exp (Complex.I *
      ((t * A.partialRowSum n r ω : ℝ) : ℂ)) *
    ((Real.exp ((t ^ 2 / 2) *
      (A.partialPredictableQuadraticVariation n r ω - 1)) : ℝ) : ℂ)

/-- For [an active martingale increment](hyp:hk), when [the compensated
predictable variance after that step is almost surely bounded](hyp:hQ), [the
integral of the next compensated weight equals the integral of the current
weight times the exact conditionally centered quadratic update](goal). -/
theorem integral_compensatedWeight_succ
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) (t K : ℝ)
    (hQ : A.partialPredictableQuadraticVariation n (k + 1) ≤ᵐ[μ n]
      fun _ => K) :
    (∫ ω, A.compensatedWeight n (k + 1) t ω ∂(μ n)) =
      ∫ ω, A.compensatedWeight n k t ω *
        (((Real.exp ((t ^ 2 / 2) * A.conditionalSecondMoment n k ω) : ℝ) : ℂ) *
          (1 - (((t ^ 2 / 2) * A.conditionalSecondMoment n k ω : ℝ) : ℂ) +
            (μ n)[(fun ω => expQuadraticRemainder
              (t * A.increment n k ω)) | A.filtration n k] ω)) ∂(μ n) := by
  /- Split the successor partial sum and predictable variation.  The weight
  through time `k`, multiplied by `exp ((t²/2) v_k)`, is predictable and is
  bounded using `hQ`; apply
  `integral_mul_condExp_eq_integral_mul_of_ae_bound`, then substitute
  `condExp_cexp_ae_eq_quadratic_add_remainder`.  The explicit bound is needed:
  finite second moments alone do not make an exponential predictable weight
  integrable. -/
  let c : ℝ := t ^ 2 / 2
  let f : Ω n → ℂ := fun ω =>
    Complex.exp (Complex.I * ((t * A.increment n k ω : ℝ) : ℂ))
  let g : Ω n → ℂ := fun ω =>
    A.compensatedWeight n k t ω *
      ((Real.exp (c * A.conditionalSecondMoment n k ω) : ℝ) : ℂ)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hfMeas : AEStronglyMeasurable f (μ n) := by
    have hX := (A.squareIntegrable n k hk).aestronglyMeasurable
    dsimp [f]
    fun_prop
  have hf : Integrable f (μ n) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfMeas ?_
    filter_upwards with ω
    dsimp [f]
    rw [Complex.norm_exp]
    simp
  have hv : StronglyMeasurable[A.filtration n k]
      (A.conditionalSecondMoment n k) := by
    exact stronglyMeasurable_condExp
  have hg : StronglyMeasurable[A.filtration n k] g := by
    have hS := A.partialRowSum_stronglyMeasurable n k
    have hQk := A.partialPredictableQuadraticVariation_stronglyMeasurable n k
    dsimp [g, compensatedWeight]
    fun_prop
  have hgBound : ∀ᵐ ω ∂(μ n), ‖g ω‖ ≤ Real.exp (c * K) := by
    filter_upwards [hQ] with ω hQω
    have hstep := congrFun (A.partialPredictableQuadraticVariation_succ n k hk) ω
    simp only [Pi.add_apply] at hstep
    have hexpArg :
        c * (A.partialPredictableQuadraticVariation n k ω - 1) +
            c * A.conditionalSecondMoment n k ω ≤ c * K := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hc
      linarith
    calc
      ‖g ω‖ = Real.exp
          (c * (A.partialPredictableQuadraticVariation n k ω - 1) +
            c * A.conditionalSecondMoment n k ω) := by
        dsimp [g, compensatedWeight]
        rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
          Complex.norm_real]
        simp [c, ← Real.exp_add]
      _ ≤ Real.exp (c * K) := Real.exp_le_exp.mpr hexpArg
  have htaylor : (μ n)[f | A.filtration n k] =ᵐ[μ n] fun ω =>
      1 - ((c : ℂ) * ((A.conditionalSecondMoment n k ω : ℝ) : ℂ)) +
        (μ n)[(fun ω => expQuadraticRemainder
          (t * A.increment n k ω)) | A.filtration n k] ω := by
    simpa only [f, c, conditionalSecondMoment] using
      condExp_cexp_ae_eq_quadratic_add_remainder
        (mΩ := mΩ n) (μ := μ n)
          ((A.filtration n).le k) (A.increment n k)
          (A.squareIntegrable n k hk) (A.condExp_zero n k hk) t
  have hsplit : A.compensatedWeight n (k + 1) t = fun ω => g ω * f ω := by
    funext ω
    have hQstep := congrFun (A.partialPredictableQuadraticVariation_succ n k hk) ω
    simp only [Pi.add_apply] at hQstep
    dsimp [g, f, c, compensatedWeight]
    unfold partialRowSum
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hk)]
    rw [Nat.min_eq_left (le_trans (Nat.le_succ k) (Nat.succ_le_of_lt hk))]
    rw [Finset.sum_range_succ, hQstep]
    simp only [Pi.add_apply, Finset.sum_apply]
    have hchar : Complex.exp (Complex.I *
          ((t * ((∑ x ∈ Finset.range k, A.increment n x ω) +
            A.increment n k ω) : ℝ) : ℂ)) =
        Complex.exp (Complex.I *
          ((t * (∑ x ∈ Finset.range k, A.increment n x ω) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((t * A.increment n k ω : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hgauss : Real.exp (t ^ 2 / 2 *
          (A.partialPredictableQuadraticVariation n k ω +
            A.conditionalSecondMoment n k ω - 1)) =
        Real.exp (t ^ 2 / 2 *
          (A.partialPredictableQuadraticVariation n k ω - 1)) *
        Real.exp (t ^ 2 / 2 * A.conditionalSecondMoment n k ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hchar, hgauss]
    push_cast
    ring
  rw [hsplit]
  calc
    (∫ ω, g ω * f ω ∂(μ n)) =
        ∫ ω, g ω * (μ n)[f | A.filtration n k] ω ∂(μ n) :=
      (integral_mul_condExp_eq_integral_mul_of_ae_bound
        ((A.filtration n).le k) f g hf hg (Real.exp (c * K)) hgBound).symm
    _ = ∫ ω, g ω *
        (1 - ((c : ℂ) * ((A.conditionalSecondMoment n k ω : ℝ) : ℂ)) +
          (μ n)[(fun ω => expQuadraticRemainder
            (t * A.increment n k ω)) | A.filtration n k] ω) ∂(μ n) := by
      apply integral_congr_ae
      filter_upwards [htaylor] with ω hω
      exact congrArg (g ω * ·) hω
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [g, c]
      push_cast
      ring

/-- For [an active martingale increment](hyp:hk), if [the variance budget is nonnegative](hyp:hK)
and [the compensated predictable variance after that step is at most `K`](hyp:hQ), then [the change
in the integrated compensated weight is bounded by the integrated Taylor
remainder and the squared one-step predictable variance](goal). -/
theorem norm_integral_compensatedWeight_succ_sub_le
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) (t K : ℝ) (hK : 0 ≤ K)
    (hQ : A.partialPredictableQuadraticVariation n (k + 1) ≤ᵐ[μ n]
      fun _ => K) :
    ‖(∫ ω, A.compensatedWeight n (k + 1) t ω ∂(μ n)) -
        ∫ ω, A.compensatedWeight n k t ω ∂(μ n)‖ ≤
      Real.exp ((t ^ 2 / 2) * K) *
        ((∫ ω, ‖expQuadraticRemainder
            (t * A.increment n k ω)‖ ∂(μ n)) +
          ((t ^ 2 / 2) ^ 2 / 2) *
            ∫ ω, (A.conditionalSecondMoment n k ω) ^ 2 ∂(μ n)) := by
  /- Use `integral_compensatedWeight_succ` and
  `norm_exp_mul_quadraticFactor_sub_one_le` pointwise.  The product of the old
  correction and `exp(c v_k)` is bounded by `exp(c K)` via `hQ`; control the
  conditional remainder with `norm_integral_mul_condExp_le_of_ae_bound`. -/
  let c : ℝ := t ^ 2 / 2
  let v : Ω n → ℝ := A.conditionalSecondMoment n k
  let rem : Ω n → ℂ := fun ω =>
    expQuadraticRemainder (t * A.increment n k ω)
  let w : Ω n → ℂ := A.compensatedWeight n k t
  let g : Ω n → ℂ := fun ω =>
    w ω * ((Real.exp (c * v ω) : ℝ) : ℂ)
  let euler : Ω n → ℂ := fun ω =>
    w ω * (((Real.exp (c * v ω) : ℝ) : ℂ) *
      (1 - (((c * v ω : ℝ) : ℂ))) - 1)
  let B : ℝ := Real.exp (c * K)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hv : StronglyMeasurable[A.filtration n k] v := by
    exact stronglyMeasurable_condExp
  have hvNonneg : 0 ≤ᵐ[μ n] v := by
    dsimp [v, conditionalSecondMoment]
    exact condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (A.increment n k ω))
  have hQkNonneg : 0 ≤ᵐ[μ n]
      A.partialPredictableQuadraticVariation n k := by
    have hall : ∀ᵐ ω ∂(μ n), ∀ j,
        0 ≤ A.conditionalSecondMoment n j ω :=
      ae_all_iff.mpr fun j => by
        dsimp [conditionalSecondMoment]
        exact condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (A.increment n j ω))
    filter_upwards [hall] with ω hω
    unfold partialPredictableQuadraticVariation
    simp only [Pi.zero_apply, Finset.sum_apply]
    exact Finset.sum_nonneg fun j hj => hω j
  have hvBound : v ≤ᵐ[μ n] fun _ => K := by
    filter_upwards [hQ, hQkNonneg] with ω hQω hQkω
    have hstep := congrFun (A.partialPredictableQuadraticVariation_succ n k hk) ω
    simp only [Pi.add_apply] at hstep
    simp only [Pi.zero_apply] at hQkω
    dsimp [v]
    linarith
  have hg : StronglyMeasurable[A.filtration n k] g := by
    have hS := A.partialRowSum_stronglyMeasurable n k
    have hQk := A.partialPredictableQuadraticVariation_stronglyMeasurable n k
    dsimp [g, w, compensatedWeight]
    fun_prop
  have hgBound : ∀ᵐ ω ∂(μ n), ‖g ω‖ ≤ B := by
    filter_upwards [hQ] with ω hQω
    have hstep := congrFun (A.partialPredictableQuadraticVariation_succ n k hk) ω
    simp only [Pi.add_apply] at hstep
    have hexpArg :
        c * (A.partialPredictableQuadraticVariation n k ω - 1) + c * v ω ≤ c * K := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hc
      dsimp [v]
      linarith
    calc
      ‖g ω‖ = Real.exp
          (c * (A.partialPredictableQuadraticVariation n k ω - 1) + c * v ω) := by
        dsimp [g, w, compensatedWeight]
        rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
          Complex.norm_real]
        simp [c, v, ← Real.exp_add]
      _ ≤ B := by
        dsimp [B]
        exact Real.exp_le_exp.mpr hexpArg
  have hw : StronglyMeasurable[A.filtration n k] w := by
    have hS := A.partialRowSum_stronglyMeasurable n k
    have hQk := A.partialPredictableQuadraticVariation_stronglyMeasurable n k
    dsimp only [w]
    unfold compensatedWeight
    fun_prop
  have hwBound : ∀ᵐ ω ∂(μ n), ‖w ω‖ ≤ B := by
    filter_upwards [hQ, hvNonneg] with ω hQω hvω
    have hstep := congrFun (A.partialPredictableQuadraticVariation_succ n k hk) ω
    simp only [Pi.add_apply] at hstep
    have hQk : A.partialPredictableQuadraticVariation n k ω ≤ K := by
      dsimp [v] at hvω
      linarith
    have hexpArg : c * (A.partialPredictableQuadraticVariation n k ω - 1) ≤ c * K :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    calc
      ‖w ω‖ = Real.exp
          (c * (A.partialPredictableQuadraticVariation n k ω - 1)) := by
        dsimp [w, compensatedWeight]
        rw [norm_mul, Complex.norm_exp, Complex.norm_real]
        simp [c]
      _ ≤ B := by
        dsimp [B]
        exact Real.exp_le_exp.mpr hexpArg
  have hwInt : Integrable w (μ n) :=
    Integrable.mono' (integrable_const B)
      (hw.mono ((A.filtration n).le k)).aestronglyMeasurable hwBound
  have hv2Meas : AEStronglyMeasurable (fun ω => (v ω) ^ 2) (μ n) := by
    exact (hv.mono ((A.filtration n).le k)).pow 2 |>.aestronglyMeasurable
  have hv2Int : Integrable (fun ω => (v ω) ^ 2) (μ n) := by
    refine Integrable.mono' (integrable_const (K ^ 2)) hv2Meas ?_
    filter_upwards [hvNonneg, hvBound] with ω hv0 hvK
    simp only [Pi.zero_apply] at hv0
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (K - v ω)]
  have hrem : Integrable rem (μ n) := by
    have hX := (A.squareIntegrable n k hk).integrable (by norm_num)
    have hX2 := (A.squareIntegrable n k hk).integrable_sq
    have hexp : Integrable (fun ω => Complex.exp (Complex.I *
        ((t * A.increment n k ω : ℝ) : ℂ))) (μ n) := by
      have hmeas : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I *
          ((t * A.increment n k ω : ℝ) : ℂ))) (μ n) := by
        have := hX.aestronglyMeasurable
        fun_prop
      refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
      filter_upwards with ω
      rw [Complex.norm_exp]
      simp
    have hlin : Integrable (fun ω =>
        (Complex.I * (t : ℂ)) * (A.increment n k ω : ℂ)) (μ n) :=
      hX.ofReal.const_mul _
    have hquad : Integrable (fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
        (((A.increment n k ω) ^ 2 : ℝ) : ℂ)) (μ n) :=
      hX2.ofReal.const_mul _
    apply (((hexp.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).congr
    filter_upwards with ω
    dsimp [rem]
    rw [expQuadraticRemainder]
    push_cast
    ring
  have hceInt : Integrable ((μ n)[rem | A.filtration n k]) (μ n) :=
    integrable_condExp
  have hgAmbient := hg.mono ((A.filtration n).le k)
  have hgceInt : Integrable
      (fun ω => g ω * (μ n)[rem | A.filtration n k] ω) (μ n) :=
    hceInt.bdd_mul hgAmbient.aestronglyMeasurable hgBound
  have heulerMeas : AEStronglyMeasurable euler (μ n) := by
    have hwAmbient : StronglyMeasurable w := hw.mono ((A.filtration n).le k)
    have hvAmbient : StronglyMeasurable v := hv.mono ((A.filtration n).le k)
    dsimp [euler]
    fun_prop
  have heulerMajor : ∀ᵐ ω ∂(μ n),
      ‖euler ω‖ ≤ B * (c ^ 2 / 2 * v ω ^ 2) := by
    filter_upwards [hvNonneg, hgBound] with ω hvω hgω
    have hdet := norm_exp_mul_quadraticFactor_sub_one_le c (v ω) 0 hc hvω
    have hfactor : ‖((Real.exp (c * v ω) : ℝ) : ℂ) *
          (1 - (((c * v ω : ℝ) : ℂ))) - 1‖ ≤
        Real.exp (c * v ω) * ((c * v ω) ^ 2 / 2) := by
      simpa using hdet
    calc
      ‖euler ω‖ = ‖w ω‖ * ‖((Real.exp (c * v ω) : ℝ) : ℂ) *
          (1 - (((c * v ω : ℝ) : ℂ))) - 1‖ := by
        dsimp [euler]
        rw [norm_mul]
      _ ≤ ‖w ω‖ * (Real.exp (c * v ω) * ((c * v ω) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = ‖g ω‖ * (c ^ 2 / 2 * v ω ^ 2) := by
        dsimp [g]
        rw [norm_mul, Complex.norm_real]
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ B * (c ^ 2 / 2 * v ω ^ 2) := by
        exact mul_le_mul_of_nonneg_right hgω (by positivity)
  have heulerInt : Integrable euler (μ n) := by
    apply Integrable.mono' (hv2Int.const_mul (B * (c ^ 2 / 2))) heulerMeas
    filter_upwards [heulerMajor] with ω hω
    simpa only [mul_assoc] using hω
  have heulerNorm : ‖∫ ω, euler ω ∂(μ n)‖ ≤
      B * (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n) := by
    calc
      ‖∫ ω, euler ω ∂(μ n)‖ ≤ ∫ ω, ‖euler ω‖ ∂(μ n) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, B * (c ^ 2 / 2 * v ω ^ 2) ∂(μ n) := by
        rw [show (fun ω => B * (c ^ 2 / 2 * v ω ^ 2)) =
            (fun ω => (B * (c ^ 2 / 2)) * v ω ^ 2) by
          funext ω
          ring]
        apply integral_mono_ae heulerInt.norm
          (hv2Int.const_mul (B * (c ^ 2 / 2)))
        filter_upwards [heulerMajor] with ω hω
        simpa only [mul_assoc] using hω
      _ = B * (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n) := by
        rw [show (fun ω => B * (c ^ 2 / 2 * v ω ^ 2)) =
            (fun ω => (B * (c ^ 2 / 2)) * v ω ^ 2) by funext ω; ring]
        exact integral_const_mul _ _
  have hremNorm : ‖∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)‖ ≤
      B * ∫ ω, ‖rem ω‖ ∂(μ n) :=
    norm_integral_mul_condExp_le_of_ae_bound ((A.filtration n).le k)
      rem g hrem hg B hB hgBound
  rw [A.integral_compensatedWeight_succ n k hk t K hQ]
  change ‖(∫ ω, w ω * (((Real.exp (c * v ω) : ℝ) : ℂ) *
        (1 - (((c * v ω : ℝ) : ℂ)) +
          (μ n)[rem | A.filtration n k] ω)) ∂(μ n)) -
      ∫ ω, w ω ∂(μ n)‖ ≤
    B * ((∫ ω, ‖rem ω‖ ∂(μ n)) +
      (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n))
  rw [show (fun ω => w ω * (((Real.exp (c * v ω) : ℝ) : ℂ) *
      (1 - (((c * v ω : ℝ) : ℂ)) +
        (μ n)[rem | A.filtration n k] ω))) =
      (fun ω => w ω + euler ω +
        g ω * (μ n)[rem | A.filtration n k] ω) by
      funext ω
      dsimp [euler, g]
      ring]
  change ‖(∫ ω, (w + euler) ω +
      (fun ω => g ω * (μ n)[rem | A.filtration n k] ω) ω ∂(μ n)) -
      ∫ ω, w ω ∂(μ n)‖ ≤
    B * ((∫ ω, ‖rem ω‖ ∂(μ n)) +
      (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n))
  rw [integral_add (hwInt.add heulerInt) hgceInt]
  have hwEuler : (∫ ω, (w + euler) ω ∂(μ n)) =
      (∫ ω, w ω ∂(μ n)) + ∫ ω, euler ω ∂(μ n) := by
    simpa only [Pi.add_apply] using integral_add hwInt heulerInt
  rw [hwEuler]
  have hcancel :
      ((∫ ω, w ω ∂(μ n)) + (∫ ω, euler ω ∂(μ n)) +
          ∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)) -
        ∫ ω, w ω ∂(μ n) =
      (∫ ω, euler ω ∂(μ n)) +
        ∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n) := by
    ring
  rw [hcancel]
  calc
    ‖(∫ ω, euler ω ∂(μ n)) +
        ∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)‖ ≤
      ‖∫ ω, euler ω ∂(μ n)‖ +
        ‖∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)‖ :=
      norm_add_le _ _
    _ ≤ B * (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n) +
        B * ∫ ω, ‖rem ω‖ ∂(μ n) := add_le_add heulerNorm hremNorm
    _ = B * ((∫ ω, ‖rem ω‖ ∂(μ n)) +
        (c ^ 2 / 2) * ∫ ω, v ω ^ 2 ∂(μ n)) := by ring

end MartingaleDifferenceArray

end Causalean.Stat

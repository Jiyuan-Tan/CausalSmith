/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Localized empirical-Gram deterministic and moment tools

This module supplies the deterministic entrywise-to-quadratic argument and the
order-`p` moment estimates for bounded localized Gram coordinates.  Together
they are the non-probabilistic and one-observation ingredients of the localized
Bernstein coercivity result.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory

/-- A [measurable local weight](hyp:hqmeas) [between zero and one almost everywhere](hyp:hq)
is [integrable under the probability law](goal). -/
theorem localWeight_integrable {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ) (hqmeas : Measurable q)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) : Integrable q P := by
  refine (integrable_const (μ := P) (1 : ℝ)).mono' hqmeas.aestronglyMeasurable ?_
  filter_upwards [hq] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- A local weight [between zero and one almost everywhere](hyp:hq), with [the stated population
mean](hyp:hp), [differs from that mean by at most one almost everywhere](goal). -/
theorem localWeight_centered_envelope {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) {p : ℝ}
    (hp : ∫ x, q x ∂P = p) : ∀ᵐ x ∂P, |q x - p| ≤ 1 := by
  have hp_bounds : 0 ≤ p ∧ p ≤ 1 := by
    rw [← hp]
    constructor
    · exact integral_nonneg_of_ae (hq.mono fun x hx ↦ hx.1)
    · by_cases hqint : Integrable q P
      · calc
          ∫ x, q x ∂P ≤ ∫ _ : X, (1 : ℝ) ∂P :=
            integral_mono_ae hqint (integrable_const (μ := P) (1 : ℝ))
              (hq.mono fun x hx ↦ hx.2)
          _ = 1 := by simp
      · rw [integral_undef hqint]
        norm_num
  filter_upwards [hq] with x hx
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hp_bounds.1, hp_bounds.2]

/-- A [measurable local weight](hyp:hqmeas) [between zero and one almost everywhere](hyp:hq),
with [the stated population mean](hyp:hp), has [centered second moment at most that local
mass](goal). -/
-- Proof route: use `E[(q-Eq)^2] = E[q^2]-(Eq)^2 ≤ E[q^2]` and `q^2 ≤ q`.
theorem localWeight_centered_secondMoment_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ) (hqmeas : Measurable q)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) {p : ℝ}
    (hp : ∫ x, q x ∂P = p) :
    ∫ x, (q x - ∫ y, q y ∂P) ^ 2 ∂P ≤ p := by
  have hqint : Integrable q P := localWeight_integrable P q hqmeas hq
  have hqLp : MemLp q 2 P :=
    memLp_of_bounded hq hqmeas.aestronglyMeasurable 2
  have hq_sq_le : ∀ᵐ x ∂P, q x ^ 2 ≤ q x := by
    filter_upwards [hq] with x hx
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  calc
    ∫ x, (q x - ∫ y, q y ∂P) ^ 2 ∂P = variance q P :=
      (variance_eq_integral hqmeas.aemeasurable).symm
    _ = ∫ x, q x ^ 2 ∂P - (∫ x, q x ∂P) ^ 2 := by
      simpa only [Pi.pow_apply] using variance_eq_sub hqLp
    _ ≤ ∫ x, q x ^ 2 ∂P := by
      nlinarith [sq_nonneg (∫ x, q x ∂P)]
    _ ≤ ∫ x, q x ∂P := integral_mono_ae hqLp.integrable_sq hqint hq_sq_le
    _ = p := hp

/-- A localized Gram coordinate with [a local weight between zero and one](hyp:hq) and
[features bounded by a nonnegative envelope](hyp:hB,hphi) [differs from its population mean by
at most twice the squared envelope almost everywhere](goal). -/
theorem localGram_centered_envelope {X κ : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ) (phi : κ → X → ℝ)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hphi : ∀ j, ∀ᵐ x ∂P, |phi j x| ≤ B) (j k : κ) :
    ∀ᵐ x ∂P,
      |q x * phi j x * phi k x - ∫ y, q y * phi j y * phi k y ∂P| ≤ 2 * B ^ 2 := by
  have hcoord_bound : ∀ᵐ x ∂P, |q x * phi j x * phi k x| ≤ B ^ 2 := by
    filter_upwards [hq, hphi j, hphi k] with x hx hphi_j hphi_k
    have hprod : |phi j x| * |phi k x| ≤ B * B :=
      mul_le_mul hphi_j hphi_k (abs_nonneg _) hB
    calc
      |q x * phi j x * phi k x| = q x * (|phi j x| * |phi k x|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx.1]
        ring
      _ ≤ 1 * (B * B) :=
        mul_le_mul hx.2 hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = B ^ 2 := by ring
  have hmean_bound : |∫ y, q y * phi j y * phi k y ∂P| ≤ B ^ 2 := by
    by_cases hcoord_int : Integrable (fun y ↦ q y * phi j y * phi k y) P
    · calc
        |∫ y, q y * phi j y * phi k y ∂P| ≤
            ∫ y, |q y * phi j y * phi k y| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _ : X, B ^ 2 ∂P :=
          integral_mono_ae hcoord_int.abs (integrable_const (μ := P) (B ^ 2)) hcoord_bound
        _ = B ^ 2 := by simp
    · rw [integral_undef hcoord_int, abs_zero]
      positivity
  filter_upwards [hcoord_bound] with x hx
  calc
    |q x * phi j x * phi k x - ∫ y, q y * phi j y * phi k y ∂P| ≤
        |q x * phi j x * phi k x| + |∫ y, q y * phi j y * phi k y ∂P| := abs_sub _ _
    _ ≤ B ^ 2 + B ^ 2 := add_le_add hx hmean_bound
    _ = 2 * B ^ 2 := by ring

/-- A localized Gram coordinate from [measurable functions](hyp:hqmeas,hphimeas), a
[unit-interval local weight](hyp:hq), [bounded features](hyp:hB,hphi), and [the stated local
mass](hyp:hp) has [centered second moment bounded by envelope-to-the-fourth times local
mass](goal). -/
-- Proof route: discard the nonnegative squared mean from the variance identity, then use
-- `(q φ_j φ_k)^2 ≤ B^4 q`, which follows from `q^2 ≤ q`.
theorem localGram_centered_secondMoment_le {X κ : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ) (phi : κ → X → ℝ)
    (hqmeas : Measurable q) (hphimeas : ∀ j, Measurable (phi j))
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) {B p : ℝ} (hB : 0 ≤ B)
    (hphi : ∀ j, ∀ᵐ x ∂P, |phi j x| ≤ B) (hp : ∫ x, q x ∂P = p)
    (j k : κ) :
    ∫ x,
        (q x * phi j x * phi k x - ∫ y, q y * phi j y * phi k y ∂P) ^ 2 ∂P
      ≤ B ^ 4 * p := by
  let coord : X → ℝ := fun x ↦ q x * phi j x * phi k x
  have hcoord_meas : Measurable coord :=
    (hqmeas.mul (hphimeas j)).mul (hphimeas k)
  have hcoord_bound : ∀ᵐ x ∂P, |coord x| ≤ B ^ 2 := by
    filter_upwards [hq, hphi j, hphi k] with x hx hphi_j hphi_k
    have hprod : |phi j x| * |phi k x| ≤ B * B :=
      mul_le_mul hphi_j hphi_k (abs_nonneg _) hB
    calc
      |coord x| = q x * (|phi j x| * |phi k x|) := by
        simp only [coord, abs_mul, abs_of_nonneg hx.1]
        ring
      _ ≤ 1 * (B * B) :=
        mul_le_mul hx.2 hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = B ^ 2 := by ring
  have hcoordLp : MemLp coord 2 P :=
    memLp_of_bounded (hcoord_bound.mono fun _ hx ↦ (abs_le.mp hx))
      hcoord_meas.aestronglyMeasurable 2
  have hqint : Integrable q P := localWeight_integrable P q hqmeas hq
  have hsquare_bound : ∀ᵐ x ∂P, coord x ^ 2 ≤ B ^ 4 * q x := by
    filter_upwards [hq, hphi j, hphi k] with x hx hphi_j hphi_k
    have hq_sq : q x ^ 2 ≤ q x := by
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have hj_sq : (phi j x) ^ 2 ≤ B ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hB] using hphi_j
    have hk_sq : (phi k x) ^ 2 ≤ B ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hB] using hphi_k
    have hprod_sq : (phi j x) ^ 2 * (phi k x) ^ 2 ≤ B ^ 2 * B ^ 2 :=
      mul_le_mul hj_sq hk_sq (sq_nonneg _) (sq_nonneg _)
    calc
      coord x ^ 2 = q x ^ 2 * ((phi j x) ^ 2 * (phi k x) ^ 2) := by
        simp only [coord]
        ring
      _ ≤ q x * (B ^ 2 * B ^ 2) :=
        mul_le_mul hq_sq hprod_sq
          (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx.1
      _ = B ^ 4 * q x := by ring
  have hmajorant_int : Integrable (fun x ↦ B ^ 4 * q x) P := by
    simpa only [smul_eq_mul] using hqint.const_mul (B ^ 4)
  change ∫ x, (coord x - ∫ y, coord y ∂P) ^ 2 ∂P ≤ B ^ 4 * p
  calc
    ∫ x, (coord x - ∫ y, coord y ∂P) ^ 2 ∂P = variance coord P :=
      (variance_eq_integral hcoord_meas.aemeasurable).symm
    _ = ∫ x, coord x ^ 2 ∂P - (∫ x, coord x ∂P) ^ 2 := by
      simpa only [Pi.pow_apply] using variance_eq_sub hcoordLp
    _ ≤ ∫ x, coord x ^ 2 ∂P := by
      nlinarith [sq_nonneg (∫ x, coord x ∂P)]
    _ ≤ ∫ x, B ^ 4 * q x ∂P :=
      integral_mono_ae hcoordLp.integrable_sq hmajorant_int hsquare_bound
    _ = B ^ 4 * ∫ x, q x ∂P := by rw [integral_const_mul]
    _ = B ^ 4 * p := by rw [hp]

/-- A localized Gram coordinate from [measurable functions](hyp:hqmeas,hphimeas), a
[unit-interval local weight](hyp:hq), and [bounded features](hyp:hB,hphi) is [integrable under
the population law](goal). -/
theorem localGram_integrable {X κ : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ) (phi : κ → X → ℝ)
    (hqmeas : Measurable q) (hphimeas : ∀ j, Measurable (phi j))
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hphi : ∀ j, ∀ᵐ x ∂P, |phi j x| ≤ B) (j k : κ) :
    Integrable (fun x ↦ q x * phi j x * phi k x) P := by
  refine (integrable_const (μ := P) (B ^ 2)).mono'
    ((hqmeas.mul (hphimeas j)).mul (hphimeas k)).aestronglyMeasurable ?_
  filter_upwards [hq, hphi j, hphi k] with x hx hphi_j hphi_k
  have hprod : |phi j x| * |phi k x| ≤ B * B :=
    mul_le_mul hphi_j hphi_k (abs_nonneg _) hB
  calc
    ‖q x * phi j x * phi k x‖ = q x * (|phi j x| * |phi k x|) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx.1]
      ring
    _ ≤ 1 * (B * B) :=
      mul_le_mul hx.2 hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
    _ = B ^ 2 := by ring

open scoped BigOperators

/-- For [a real-valued observation-weight function](hyp:q) and [a finite sample](hyp:omega), [the unnormalised local count](goal) is the sum of the weights assigned to all observations in the sample. -/
def localCount {N : ℕ} {X : Type*} (q : X → ℝ) (omega : Fin N → X) : ℝ :=
  ∑ i, q (omega i)

/-- For [a real-valued observation-weight function](hyp:q), [a finite indexed family of real-valued features](hyp:phi), [a finite sample](hyp:omega), and [two feature indices](hyp:j,k), [the corresponding entry of the unnormalised weighted empirical Gram matrix](goal) is the sum, over observations, of the weight times the two selected feature values. -/
def localGramEntry {N : ℕ} {κ X : Type*} [Fintype κ]
    (q : X → ℝ) (phi : κ → X → ℝ) (omega : Fin N → X) (j k : κ) : ℝ :=
  ∑ i, q (omega i) * phi j (omega i) * phi k (omega i)

/-- For [a real-valued observation-weight function](hyp:q), [a finite indexed family of real-valued features](hyp:phi), [a finite sample](hyp:omega), and [a real coefficient vector indexed by the features](hyp:v), [the quadratic form of the unnormalised weighted empirical Gram matrix](goal) is the double sum of the product of two coefficients and their weighted empirical Gram-matrix entry. -/
def localGramQuadratic {N : ℕ} {κ X : Type*} [Fintype κ]
    (q : X → ℝ) (phi : κ → X → ℝ) (omega : Fin N → X)
    (v : κ → ℝ) : ℝ :=
  ∑ j, ∑ k, v j * v k * localGramEntry q phi omega j k

/-- For [a real lower-eigenvalue threshold](hyp:lambda), [a real-valued observation-weight function](hyp:q), [a finite indexed family of real-valued features](hyp:phi), and [a finite sample](hyp:omega), [the localized empirical Gram matrix is good](goal) exactly when (1) [the local count is positive](step:1) and (2) [for every real coefficient vector indexed by the features, its quadratic form is at least one half of the threshold times the local count times the squared Euclidean norm of that vector](step:2). -/
def LocalizedGramGood {N : ℕ} {κ X : Type*} [Fintype κ]
    (lambda : ℝ) (q : X → ℝ) (phi : κ → X → ℝ) (omega : Fin N → X) : Prop :=
  0 < localCount q omega ∧
    ∀ v : κ → ℝ,
      (lambda / 2) * localCount q omega * (∑ j, (v j) ^ 2) ≤
        localGramQuadratic q phi omega v

/-- If [finite-matrix entries are bounded by a nonnegative tolerance](hyp:hepsilon,hE), [the
absolute quadratic-form error is at most dimension times tolerance times squared vector
norm](goal). -/
-- Proof route: triangle inequality, the entrywise bound, then
-- `(∑ |v j|)^2 ≤ card κ * ∑ (v j)^2` by finite Cauchy--Schwarz.
theorem entrywise_to_quadratic {κ : Type*} [Fintype κ]
    (E : κ → κ → ℝ) (v : κ → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hE : ∀ j k, |E j k| ≤ epsilon) :
    |∑ j, ∑ k, v j * v k * E j k| ≤
      (Fintype.card κ : ℝ) * epsilon * ∑ j, (v j) ^ 2 := by
  have hinner (j : κ) :
      (∑ k, |v j| * |v k| * epsilon) =
        |v j| * ((∑ k, |v k|) * epsilon) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    |∑ j, ∑ k, v j * v k * E j k|
        ≤ ∑ j, |∑ k, v j * v k * E j k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |v j * v k * E j k| := by
          gcongr with j
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |v j| * |v k| * epsilon := by
          gcongr with j k
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hE j k)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = epsilon * (∑ j, |v j|) ^ 2 := by
          simp_rw [hinner]
          rw [← Finset.sum_mul]
          ring
    _ ≤ epsilon * ((Fintype.card κ : ℝ) * ∑ j, |v j| ^ 2) := by
          gcongr
          simpa using
            (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : κ => |v j|))
    _ = (Fintype.card κ : ℝ) * epsilon * ∑ j, (v j) ^ 2 := by
          simp only [sq_abs]
          ring

/-- If [an empirical matrix is entrywise close to a scaled population matrix with nonnegative
tolerance](hyp:hepsilon,hentry), [each empirical quadratic form is bounded below by the
population form minus the dimension-scaled error](goal). -/
theorem entrywise_gram_lower_bound {κ : Type*} [Fintype κ]
    (G M : κ → κ → ℝ) (v : κ → ℝ) {scale epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hentry : ∀ j k, |G j k - scale * M j k| ≤ epsilon) :
    scale * (∑ j, ∑ k, v j * v k * M j k) -
        (Fintype.card κ : ℝ) * epsilon * ∑ j, (v j) ^ 2 ≤
      ∑ j, ∑ k, v j * v k * G j k := by
  let C : ℝ := (Fintype.card κ : ℝ) * epsilon * ∑ j, (v j) ^ 2
  have habs :
      |∑ j, ∑ k, v j * v k * (G j k - scale * M j k)| ≤ C := by
    exact entrywise_to_quadratic (fun j k => G j k - scale * M j k)
      v hepsilon hentry
  have hscale :
      (∑ j, ∑ k, v j * v k * (scale * M j k)) =
        scale * (∑ j, ∑ k, v j * v k * M j k) := by
    calc
      (∑ j, ∑ k, v j * v k * (scale * M j k)) =
          ∑ j, ∑ k, scale * (v j * v k * M j k) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = scale * (∑ j, ∑ k, v j * v k * M j k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
  have hdiff :
      (∑ j, ∑ k, v j * v k * (G j k - scale * M j k)) =
        (∑ j, ∑ k, v j * v k * G j k) -
          scale * (∑ j, ∑ k, v j * v k * M j k) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hscale]
  have hneg := neg_le_of_abs_le habs
  rw [hdiff] at hneg
  dsimp [C] at hneg ⊢
  linarith

/-- Given [positive sample size, mass, and coercivity](hyp:hN,hp,hlambda), [population
coercivity](hyp:hcoercive), a [small count error](hyp:hcount), and [small entrywise Gram
errors](hyp:hentry), [the realised local count is positive and the empirical Gram is coercive
relative to it](goal). -/
-- Proof route: the count window gives `0 < Q ≤ 3Np/2`; entrywise perturbation gives
-- `v'Gv ≥ λNp‖v‖² - λNp‖v‖²/4 = 3λNp‖v‖²/4`.
theorem localizedGram_good_of_entrywise
    {N : ℕ} {κ X : Type*} [Fintype κ] [Nonempty κ]
    (q : X → ℝ) (phi : κ → X → ℝ) (M : κ → κ → ℝ)
    {p lambda : ℝ} (hN : 0 < N) (hp : 0 < p) (hlambda : 0 < lambda)
    (hcoercive : ∀ v : κ → ℝ,
      lambda * p * (∑ j, (v j) ^ 2) ≤ ∑ j, ∑ k, v j * v k * M j k)
    (omega : Fin N → X)
    (hcount : |localCount q omega - (N : ℝ) * p| < (N : ℝ) * p / 2)
    (hentry : ∀ j k,
      |localGramEntry q phi omega j k - (N : ℝ) * M j k| <
        lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ))) :
    LocalizedGramGood lambda q phi omega := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) * p := mul_pos hNreal hp
  have hcount_bounds := (abs_lt.mp hcount)
  have hQpos : 0 < localCount q omega := by
    linarith [hcount_bounds.1]
  have hQupper : localCount q omega ≤ 3 * ((N : ℝ) * p) / 2 := by
    linarith [hcount_bounds.2]
  refine ⟨hQpos, ?_⟩
  intro v
  let S : ℝ := ∑ j, (v j) ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hcard : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  let epsilon : ℝ :=
    lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ))
  have hepsilon : 0 ≤ epsilon := by
    dsimp [epsilon]
    positivity
  have hentry_le : ∀ j k,
      |localGramEntry q phi omega j k - (N : ℝ) * M j k| ≤ epsilon := by
    intro j k
    exact le_of_lt (hentry j k)
  have hpert := entrywise_gram_lower_bound
    (fun j k => localGramEntry q phi omega j k) M v
    (scale := (N : ℝ)) (epsilon := epsilon) hepsilon hentry_le
  change
    (N : ℝ) * (∑ j, ∑ k, v j * v k * M j k) -
      (Fintype.card κ : ℝ) * epsilon * S ≤
        ∑ j, ∑ k, v j * v k * localGramEntry q phi omega j k at hpert
  have hpop := hcoercive v
  change lambda * p * S ≤ ∑ j, ∑ k, v j * v k * M j k at hpop
  have hscaled :
      (N : ℝ) * (lambda * p * S) ≤
        (N : ℝ) * (∑ j, ∑ k, v j * v k * M j k) :=
    mul_le_mul_of_nonneg_left hpop (le_of_lt hNreal)
  have herr :
      (Fintype.card κ : ℝ) * epsilon * S =
        (lambda * (N : ℝ) * p / 4) * S := by
    dsimp [epsilon]
    field_simp
  have hlower :
      (3 * (lambda * (N : ℝ) * p) / 4) * S ≤
        localGramQuadratic q phi omega v := by
    rw [localGramQuadratic]
    rw [herr] at hpert
    linarith
  have htarget :
      (lambda / 2) * localCount q omega * S ≤
        (3 * (lambda * (N : ℝ) * p) / 4) * S := by
    have hmul := mul_le_mul_of_nonneg_right hQupper
      (mul_nonneg (le_of_lt hlambda) hS)
    nlinarith
  dsimp [S] at htarget hlower ⊢
  exact htarget.trans hlower

/-- Under [positive sample size, mass, and coercivity](hyp:hN,hp,hlambda) and [population
coercivity](hyp:hcoercive), [failure of empirical local-Gram coercivity implies either a large
count error or a large entrywise Gram error](goal). -/
theorem localizedGram_failure_subset_deviations
    {N : ℕ} {κ X : Type*} [Fintype κ] [Nonempty κ]
    (q : X → ℝ) (phi : κ → X → ℝ) (M : κ → κ → ℝ)
    {p lambda : ℝ} (hN : 0 < N) (hp : 0 < p) (hlambda : 0 < lambda)
    (hcoercive : ∀ v : κ → ℝ,
      lambda * p * (∑ j, (v j) ^ 2) ≤ ∑ j, ∑ k, v j * v k * M j k) :
    {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega} ⊆
      {omega : Fin N → X |
        (N : ℝ) * p / 2 ≤ |localCount q omega - (N : ℝ) * p| ∨
        ∃ j k, lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ)) ≤
          |localGramEntry q phi omega j k - (N : ℝ) * M j k|} := by
  intro omega hfailure
  change ¬ LocalizedGramGood lambda q phi omega at hfailure
  change
    (N : ℝ) * p / 2 ≤ |localCount q omega - (N : ℝ) * p| ∨
      ∃ j k, lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ)) ≤
        |localGramEntry q phi omega j k - (N : ℝ) * M j k|
  by_contra hdeviations
  have hcount :
      |localCount q omega - (N : ℝ) * p| < (N : ℝ) * p / 2 := by
    exact lt_of_not_ge (fun hge => hdeviations (Or.inl hge))
  have hentry : ∀ j k,
      |localGramEntry q phi omega j k - (N : ℝ) * M j k| <
        lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ)) := by
    intro j k
    exact lt_of_not_ge (fun hge => hdeviations (Or.inr ⟨j, k, hge⟩))
  exact hfailure
    (localizedGram_good_of_entrywise q phi M hN hp hlambda hcoercive
      omega hcount hentry)

end Causalean.Stat.Concentration

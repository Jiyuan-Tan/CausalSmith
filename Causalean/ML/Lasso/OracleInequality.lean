/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core.Convex
public import Causalean.ML.Lasso.Finite
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Fixed-design Lasso oracle inequality

This module gives a fast-rate fixed-design Lasso bound under a full-vector
cone-curvature condition. The objective is normalized as
`(2n)⁻¹ ‖y - Xβ‖₂² + λ ‖β‖₁`; exact minimizers exist for positive `λ`.

For an `s`-sparse truth, score domination
`2 ‖Xᵀw/n‖∞ ≤ λ`, and restricted curvature
`‖XΔ‖₂²/n ≥ κ ‖Δ‖₂²` on a factor-three cone, the main theorem proves
the simultaneous ℓ², ℓ¹, and prediction bounds with constants `3`, `12`, and
`9`. This is a strengthened and reparameterized deterministic variant of the
oracle-inequality argument in Bickel, Ritov, and Tsybakov (2009), Theorem 7.2:
here curvature controls the full perturbation norm rather than its restriction to
the active support, and `kappa` corresponds to a squared restricted-eigenvalue
constant. The cited theorem also adds stochastic assumptions not used here.
-/

@[expose] public section

namespace Causalean.ML

open Filter Matrix BigOperators
open scoped NNReal

variable {n p : ℕ}

/-- [The Euclidean norm](goal) measures [a finite coefficient vector](hyp:β) in
[the stated dimension](hyp:p) by [the square root of summed squared coordinates](step:1). -/
noncomputable def finiteL2Norm (β : Fin p → ℝ) : ℝ :=
  Real.sqrt (∑ j, β j ^ 2)

/-- [The restricted one-norm](goal) measures [a coefficient vector](hyp:β) only on
[the selected coordinates](hyp:S), by [summing their absolute values](step:1) within
[the ambient dimension](hyp:p). -/
noncomputable def l1On (β : Fin p → ℝ) (S : Finset (Fin p)) : ℝ :=
  ∑ j ∈ S, |β j|

/-- [Normalized prediction error](goal) measures [a coefficient perturbation](hyp:Δ) by
[its mean squared fitted-value change](step:1). It uses
[sample and coefficient dimensions](hyp:n,p) and [the design matrix](hyp:X). -/
noncomputable def fixedDesignPredictionError
    (X : Matrix (Fin n) (Fin p) ℝ) (Δ : Fin p → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (X *ᵥ Δ) i ^ 2

/-- [Normalized least-squares loss](goal) is [half the mean squared residual](step:1). It
evaluates [a coefficient vector](hyp:β) against [the design and outcome vectors](hyp:X,y) at
[the sample and coefficient dimensions](hyp:n,p). -/
noncomputable def fixedDesignLoss
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (β : Fin p → ℝ) : ℝ :=
  (2 * (n : ℝ))⁻¹ * ∑ i, (y i - (X *ᵥ β) i) ^ 2

/-- [The normalized Lasso objective](goal) trades
[half mean squared residual against weighted L1 norm](step:1). It scores
[a coefficient vector](hyp:β) on [the fixed design and outcomes](hyp:X,y) at
[penalty level](hyp:lam), with [sample and coefficient dimensions](hyp:n,p). -/
noncomputable def normalizedLassoObjective
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  fixedDesignLoss X y β + lam * l1penalty β

/-- [A Lasso minimizer](goal) is [a coefficient no worse than every competitor](step:1). The
comparison uses [the candidate](hyp:βhat), [fixed design and outcomes](hyp:X,y), and
[penalty level](hyp:lam) at [the sample and coefficient dimensions](hyp:n,p). -/
def IsLassoMinimizer
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (βhat : Fin p → ℝ) : Prop :=
  ∀ β, normalizedLassoObjective X y lam βhat ≤ normalizedLassoObjective X y lam β

/-- [The normalized Lasso score](goal) at [a coefficient coordinate](hyp:j) is
[the mean design--noise product](step:1). It uses [a fixed design](hyp:X) and
[noise vector](hyp:w) at [the sample and coefficient dimensions](hyp:n,p). -/
noncomputable def lassoScore
    (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (j : Fin p) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, X i j * w i

/-- [The Lasso score infinity norm](goal) is [the largest absolute coordinate score](step:1),
with value zero in dimension zero. It uses [a fixed design](hyp:X) and
[noise vector](hyp:w) at [the sample and coefficient dimensions](hyp:n,p). -/
noncomputable def lassoScoreSupNorm
    (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) : ℝ :=
  ↑((Finset.univ : Finset (Fin p)).sup fun j => ‖lassoScore X w j‖₊)

/-- [The factor-three Lasso cone](goal) contains
[perturbations with off-support norm at most three times on-support norm](step:1). It uses
[the proposed support](hyp:S) in [the ambient coefficient dimension](hyp:p). -/
noncomputable def LassoCone (S : Finset (Fin p)) : Set (Fin p → ℝ) :=
  {Δ | l1On Δ ((Finset.univ : Finset (Fin p)) \ S) ≤ 3 * l1On Δ S}

/-- [The restricted-eigenvalue condition](goal) guarantees
[quadratic curvature on the factor-three cone](step:1). It uses
[the fixed design](hyp:X), [proposed support](hyp:S), and [curvature constant](hyp:kappa) at
[the sample and coefficient dimensions](hyp:n,p). -/
def RestrictedEigenvalue
    (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) (kappa : ℝ) : Prop :=
  ∀ Δ ∈ LassoCone S,
    kappa * finiteL2Norm Δ ^ 2 ≤ fixedDesignPredictionError X Δ

private lemma l1penalty_eq_on_add_off (β : Fin p → ℝ) (S : Finset (Fin p)) :
    l1penalty β = l1On β S + l1On β ((Finset.univ : Finset (Fin p)) \ S) := by
  unfold l1penalty l1On
  rw [← Finset.sum_sdiff (Finset.subset_univ S) (f := fun j => |β j|)]
  ring

private lemma l1On_nonneg (β : Fin p → ℝ) (S : Finset (Fin p)) :
    0 ≤ l1On β S := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma l1On_le_card_sqrt_mul_l2
    (β : Fin p → ℝ) (S : Finset (Fin p)) :
    l1On β S ≤ Real.sqrt S.card * finiteL2Norm β := by
  unfold l1On finiteL2Norm
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S (fun j => |β j|) (fun _ => (1 : ℝ))
  have hleft :
      (∑ j ∈ S, |β j|) ≤
        Real.sqrt (∑ j ∈ S, (β j) ^ 2) * Real.sqrt (S.card : ℝ) := by
    calc
      (∑ j ∈ S, |β j|) = ∑ j ∈ S, |β j| * (1 : ℝ) := by simp
      _ ≤ Real.sqrt (∑ j ∈ S, |β j| ^ 2) *
          Real.sqrt (∑ j ∈ S, (1 : ℝ) ^ 2) := hcs
      _ = Real.sqrt (∑ j ∈ S, (β j) ^ 2) * Real.sqrt (S.card : ℝ) := by
        simp [sq_abs]
  have hsum_le : (∑ j ∈ S, (β j) ^ 2) ≤ ∑ j, (β j) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun j _ _ => sq_nonneg (β j))
  calc
    (∑ j ∈ S, |β j|) ≤
        Real.sqrt (∑ j ∈ S, (β j) ^ 2) * Real.sqrt (S.card : ℝ) := hleft
    _ ≤ Real.sqrt (∑ j, (β j) ^ 2) * Real.sqrt (S.card : ℝ) := by
      gcongr
    _ = Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (β j) ^ 2) := by ring

private lemma lassoScore_abs_le_supNorm
    (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (j : Fin p) :
    |lassoScore X w j| ≤ lassoScoreSupNorm X w := by
  unfold lassoScoreSupNorm
  exact_mod_cast Finset.le_sup (s := Finset.univ)
    (f := fun k : Fin p => ‖lassoScore X w k‖₊) (Finset.mem_univ j)

private lemma lassoScore_holder
    (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (Δ : Fin p → ℝ) :
    |∑ j, lassoScore X w j * Δ j| ≤ lassoScoreSupNorm X w * l1penalty Δ := by
  calc
    |∑ j, lassoScore X w j * Δ j|
        ≤ ∑ j, |lassoScore X w j * Δ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |lassoScore X w j| * |Δ j| := by simp [abs_mul]
    _ ≤ ∑ j, lassoScoreSupNorm X w * |Δ j| := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (lassoScore_abs_le_supNorm X w j) (abs_nonneg _)
    _ = lassoScoreSupNorm X w * l1penalty Δ := by
      simp [l1penalty, Finset.mul_sum]

private lemma score_dot_eq_cross
    (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (Δ : Fin p → ℝ) :
    (∑ j, lassoScore X w j * Δ j) =
      (n : ℝ)⁻¹ * ∑ i, w i * (X *ᵥ Δ) i := by
  classical
  simp only [lassoScore, Matrix.mulVec, dotProduct]
  calc
    (∑ j, ((n : ℝ)⁻¹ * ∑ i, X i j * w i) * Δ j) =
        (n : ℝ)⁻¹ * ∑ j, ∑ i, (X i j * w i) * Δ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc]
      apply congrArg ((n : ℝ)⁻¹ * ·)
      rw [Finset.sum_mul]
    _ = (n : ℝ)⁻¹ * ∑ i, ∑ j, (X i j * w i) * Δ j := by
      rw [Finset.sum_comm]
    _ = (n : ℝ)⁻¹ * ∑ i, w i * ∑ j, X i j * Δ j := by
      apply congrArg ((n : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma support_penalty_difference_le
    (βstar βhat : Fin p → ℝ) (S : Finset (Fin p))
    (hsupp : ∀ j ∉ S, βstar j = 0) :
    l1penalty βstar - l1penalty βhat ≤
      l1On (βhat - βstar) S -
        l1On (βhat - βstar) ((Finset.univ : Finset (Fin p)) \ S) := by
  let Δ := βhat - βstar
  have hstar : l1penalty βstar = l1On βstar S := by
    rw [l1penalty_eq_on_add_off βstar S]
    have hoff : l1On βstar ((Finset.univ : Finset (Fin p)) \ S) = 0 := by
      unfold l1On
      exact Finset.sum_eq_zero fun j hj => by
        have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
        simp [hsupp j hjS]
    simp [hoff]
  have hhat_off :
      l1On βhat ((Finset.univ : Finset (Fin p)) \ S) =
        l1On Δ ((Finset.univ : Finset (Fin p)) \ S) := by
    unfold l1On
    apply Finset.sum_congr rfl
    intro j hj
    have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
    simp [Δ, hsupp j hjS]
  have hreverse : l1On βstar S - l1On Δ S ≤ l1On βhat S := by
    unfold l1On
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => by
      have htri := abs_sub_le (βstar j) (βhat j) 0
      have hdiff : |βstar j - βhat j| = |Δ j| := by
        have : βstar j - βhat j = -(Δ j) := by simp [Δ]
        rw [this, abs_neg]
      simpa [sub_zero, hdiff, add_comm] using htri
  rw [hstar, l1penalty_eq_on_add_off βhat S, hhat_off]
  linarith

private lemma lasso_basic_inequality
    (X : Matrix (Fin n) (Fin p) ℝ) (y w : Fin n → ℝ)
    (βstar βhat : Fin p → ℝ) (lam : ℝ)
    (hn : 0 < n) (hmodel : y = X *ᵥ βstar + w)
    (hmin : IsLassoMinimizer X y lam βhat) :
    fixedDesignPredictionError X (βhat - βstar) / 2 ≤
      (∑ j, lassoScore X w j * (βhat j - βstar j)) +
        lam * (l1penalty βstar - l1penalty βhat) := by
  classical
  let Δ : Fin p → ℝ := βhat - βstar
  let z : Fin n → ℝ := X *ᵥ Δ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hres_star : ∀ i, y i - (X *ᵥ βstar) i = w i := by
    intro i
    rw [hmodel]
    simp
  have hres_hat : ∀ i, y i - (X *ᵥ βhat) i = w i - z i := by
    intro i
    rw [hmodel]
    simp only [Pi.add_apply]
    have hmul : X *ᵥ βhat = X *ᵥ βstar + z := by
      have hβ : βhat = βstar + Δ := by
        ext j
        simp [Δ]
      rw [hβ, Matrix.mulVec_add]
    rw [hmul]
    simp
  have hopt := hmin βstar
  unfold normalizedLassoObjective fixedDesignLoss at hopt
  simp_rw [hres_star, hres_hat] at hopt
  have hcross :
      (∑ j, lassoScore X w j * Δ j) = (n : ℝ)⁻¹ * ∑ i, w i * z i := by
    simpa [z] using score_dot_eq_cross X w Δ
  have hquad :
      fixedDesignPredictionError X Δ / 2 =
        (2 * (n : ℝ))⁻¹ * ∑ i, z i ^ 2 := by
    unfold fixedDesignPredictionError
    simp only [z]
    field_simp
  change fixedDesignPredictionError X Δ / 2 ≤
    (∑ j, lassoScore X w j * Δ j) +
      lam * (l1penalty βstar - l1penalty βhat)
  rw [hcross, hquad]
  have hexpand :
      (∑ i, (w i - z i) ^ 2) =
        (∑ i, w i ^ 2) - 2 * (∑ i, w i * z i) + ∑ i, z i ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_assoc]
  rw [hexpand] at hopt
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp [hn0] at hopt ⊢
  nlinarith

/-- **Existence of a normalized Lasso solution.** For [a positive sample
size](hyp:hn), [a positive coefficient dimension](hyp:hp), [a fixed design
matrix](hyp:X), [an outcome vector](hyp:y), and [a positive penalty
level](hyp:hlam), [the normalized Lasso objective has a global minimizer](goal).

The positive penalty makes the objective coercive even when the design is rank
deficient. -/
theorem exists_lassoMinimizer
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (hn : 0 < n) (hp : 0 < p) (hlam : 0 < lam) :
    ∃ βhat, IsLassoMinimizer X y lam βhat := by
  classical
  let _ : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  have hl1_ge_norm : ∀ β : Fin p → ℝ, ‖β‖ ≤ l1penalty β := by
    intro β
    rw [Pi.norm_def]
    have hsum0 : 0 ≤ l1penalty β := l1penalty_nonneg β
    let L : ℝ≥0 := ⟨l1penalty β, hsum0⟩
    change (↑((Finset.univ : Finset (Fin p)).sup fun j => ‖β j‖₊) : ℝ) ≤ (L : ℝ)
    apply (NNReal.coe_le_coe).2
    apply Finset.sup_le
    intro j _
    apply (NNReal.coe_le_coe).1
    change |β j| ≤ l1penalty β
    unfold l1penalty
    exact Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin p => |β k|)
      (fun k _ => abs_nonneg (β k)) (Finset.mem_univ j)
  have hcont : Continuous (normalizedLassoObjective X y lam) := by
    unfold normalizedLassoObjective fixedDesignLoss l1penalty
    fun_prop
  have hl1_top : Tendsto (l1penalty : (Fin p → ℝ) → ℝ)
      (cocompact (Fin p → ℝ)) atTop :=
    tendsto_atTop_mono hl1_ge_norm tendsto_norm_cocompact_atTop
  have hlam_top : Tendsto (fun β : Fin p → ℝ => lam * l1penalty β)
      (cocompact (Fin p → ℝ)) atTop :=
    hl1_top.const_mul_atTop hlam
  have hobj_top : Tendsto (normalizedLassoObjective X y lam)
      (cocompact (Fin p → ℝ)) atTop := by
    refine tendsto_atTop_mono' _ ?_ hlam_top
    filter_upwards [] with β
    unfold normalizedLassoObjective fixedDesignLoss
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsquares : 0 ≤ ∑ i, (y i - (X *ᵥ β) i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hscale : 0 ≤ (2 * (n : ℝ))⁻¹ := by positivity
    nlinarith [mul_nonneg hscale hsquares]
  obtain ⟨βhat, hβhat⟩ := exists_isMinOn_univ_of_coercive hcont hobj_top
  exact ⟨βhat, fun β => hβhat (Set.mem_univ β)⟩

/-- **Fixed-design Lasso oracle inequality under restricted eigenvalues.** For
[a positive sample size](hyp:hn), let [the response obey
the fixed-design model `y = Xβ⋆ + w`](hyp:hmodel), let [the true coefficient be
supported on `S`](hyp:hsupp) with [support size `s`](hyp:hcard), and let [the
positive penalty level](hyp:hlam) satisfy [twice the score infinity norm is at
most the penalty](hyp:hscore).  If [the restricted-eigenvalue curvature `κ` is
positive](hyp:hkappa), [the design satisfies restricted eigenvalues on the
factor-three cone](hyp:hRE), and [the candidate is an exact normalized Lasso
minimizer](hyp:hmin), then [its error has Euclidean norm at most
`3√s λ/κ`, one-norm at most `12sλ/κ`, and normalized prediction error at most
`9sλ²/κ`](goal).

The constants follow the classical basic-inequality proof: optimality and score
domination put the error in the factor-three cone, after which restricted
curvature and Cauchy--Schwarz on the true support close all three bounds. -/
theorem lasso_oracle_inequality
    (X : Matrix (Fin n) (Fin p) ℝ) (y w : Fin n → ℝ)
    (βstar βhat : Fin p → ℝ) (S : Finset (Fin p)) (s : ℕ)
    (lam kappa : ℝ)
    (hn : 0 < n)
    (hmodel : y = X *ᵥ βstar + w)
    (hsupp : ∀ j ∉ S, βstar j = 0)
    (hcard : S.card = s)
    (hlam : 0 < lam)
    (hscore : 2 * lassoScoreSupNorm X w ≤ lam)
    (hkappa : 0 < kappa)
    (hRE : RestrictedEigenvalue X S kappa)
    (hmin : IsLassoMinimizer X y lam βhat) :
    finiteL2Norm (βhat - βstar) ≤ 3 * Real.sqrt s * lam / kappa ∧
      l1penalty (βhat - βstar) ≤ 12 * s * lam / kappa ∧
      fixedDesignPredictionError X (βhat - βstar) ≤ 9 * s * lam ^ 2 / kappa := by
  classical
  let Δ : Fin p → ℝ := βhat - βstar
  let A : ℝ := l1On Δ S
  let B : ℝ := l1On Δ ((Finset.univ : Finset (Fin p)) \ S)
  let L : ℝ := l1penalty Δ
  let Q : ℝ := fixedDesignPredictionError X Δ
  let G : ℝ := ∑ j, lassoScore X w j * Δ j
  have hA0 : 0 ≤ A := l1On_nonneg Δ S
  have hB0 : 0 ≤ B := l1On_nonneg Δ ((Finset.univ : Finset (Fin p)) \ S)
  have hL : L = A + B := by
    simpa [L, A, B] using l1penalty_eq_on_add_off Δ S
  have hQ0 : 0 ≤ Q := by
    unfold Q fixedDesignPredictionError
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hsup : lassoScoreSupNorm X w ≤ lam / 2 := by linarith
  have hGabs : |G| ≤ (lam / 2) * L := by
    have hhold := lassoScore_holder X w Δ
    exact hhold.trans (mul_le_mul_of_nonneg_right hsup (by
      simp [l1penalty, Finset.sum_nonneg]))
  have hD : l1penalty βstar - l1penalty βhat ≤ A - B := by
    simpa [A, B, Δ] using support_penalty_difference_le βstar βhat S hsupp
  have hbasic := lasso_basic_inequality X y w βstar βhat lam hn hmodel hmin
  have hmain : Q + lam * B ≤ 3 * lam * A := by
    have hG : G ≤ (lam / 2) * L := (le_abs_self G).trans hGabs
    have hbasic0 : Q / 2 ≤ G + lam * (l1penalty βstar - l1penalty βhat) := by
      simpa [Q, G, Δ] using hbasic
    have hbasic' : Q / 2 ≤ G + lam * (A - B) := by
      have hmul := mul_le_mul_of_nonneg_left hD hlam.le
      linarith
    rw [hL] at hG
    nlinarith
  have hcone : Δ ∈ LassoCone S := by
    unfold LassoCone
    change B ≤ 3 * A
    nlinarith
  have hREΔ : kappa * finiteL2Norm Δ ^ 2 ≤ Q := hRE Δ hcone
  have hA : A ≤ Real.sqrt s * finiteL2Norm Δ := by
    simpa [A, hcard] using l1On_le_card_sqrt_mul_l2 Δ S
  have hQ_le : Q ≤ 3 * lam * A := by nlinarith
  have hquad : kappa * finiteL2Norm Δ ^ 2 ≤
      3 * lam * (Real.sqrt s * finiteL2Norm Δ) := by
    exact hREΔ.trans (hQ_le.trans (mul_le_mul_of_nonneg_left hA (by positivity)))
  have hl2 : finiteL2Norm Δ ≤ 3 * Real.sqrt s * lam / kappa := by
    have hnorm0 : 0 ≤ finiteL2Norm Δ := Real.sqrt_nonneg _
    by_cases hzero : finiteL2Norm Δ = 0
    · rw [hzero]
      positivity
    · have hnormpos : 0 < finiteL2Norm Δ := lt_of_le_of_ne hnorm0 (Ne.symm hzero)
      rw [le_div_iff₀ hkappa]
      nlinarith
  have hl1 : L ≤ 12 * s * lam / kappa := by
    have hconeL : L ≤ 4 * A := by rw [hL]; nlinarith
    have hsqrt_sq : Real.sqrt s ^ 2 = (s : ℝ) := Real.sq_sqrt (Nat.cast_nonneg s)
    rw [le_div_iff₀ hkappa] at hl2 ⊢
    calc
      L * kappa ≤ (4 * A) * kappa := mul_le_mul_of_nonneg_right hconeL hkappa.le
      _ ≤ (4 * (Real.sqrt s * finiteL2Norm Δ)) * kappa := by
        gcongr
      _ ≤ 12 * (s : ℝ) * lam := by
        nlinarith [Real.sqrt_nonneg (s : ℝ)]
  have hpred : Q ≤ 9 * s * lam ^ 2 / kappa := by
    rw [le_div_iff₀ hkappa] at hl2 ⊢
    have hsqrt_sq : Real.sqrt s ^ 2 = (s : ℝ) := Real.sq_sqrt (Nat.cast_nonneg s)
    calc
      Q * kappa ≤ (3 * lam * A) * kappa :=
        mul_le_mul_of_nonneg_right hQ_le hkappa.le
      _ ≤ (3 * lam * (Real.sqrt s * finiteL2Norm Δ)) * kappa := by
        gcongr
      _ ≤ 9 * (s : ℝ) * lam ^ 2 := by
        nlinarith [Real.sqrt_nonneg (s : ℝ)]
  simpa [Δ, L, Q] using ⟨hl2, hl1, hpred⟩

end Causalean.ML

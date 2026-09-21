/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The van Trees inequality (Bayesian Cramer-Rao bound)

This file states and proves the classical single-parameter **van Trees
inequality** `van_trees_inequality`: a Bayesian analogue of the Cramer-Rao lower bound for the
mean-squared error of estimating a smooth functional of a random parameter.

Setup (an econometrician's reading). A scalar parameter `h` is drawn from a
prior with a continuously differentiable density `q` supported on `[a, b]` that
vanishes at both endpoints (`q a = q b = 0`); its prior Fisher information is
`I_q = ∫ q'(h)² / q(h) dh`. Given `h`, data `Z` are drawn from a law `P h` with
score function `S h` (mean zero under `P h`) and Fisher information
`I(h) = E_h[S h ²]`. For any estimator `δ(Z)` of a differentiable scalar target
`ψ(h)`, the average (Bayes) mean-squared error is bounded below by

  `(∫ ψ'(h) q(h) dh)² / (I_q + ∫ I(h) q(h) dh)`.

The denominator adds the *prior* information `I_q` to the *average experimental*
information `∫ I(h) q(h) dh`; the numerator is the squared average sensitivity of
the target. Because the prior information appears additively, the bound stays
finite even where the frequentist Cramer-Rao bound degenerates, which is why the
van Trees inequality is the standard device for proving minimax lower bounds.

The canonical theorem derives the estimator-specific differentiation identity
from model-level likelihood regularity through the observation-dependent van
Trees engine. The earlier formulation that assumed this identity for each
estimator remains only as a deprecated compatibility theorem.
-/

public section

namespace Causalean.Stat.Minimax

open MeasureTheory intervalIntegral Set

/-- **van Trees inequality (Bayesian Cramér–Rao bound), single parameter.**
Let a scalar parameter `h` range over [an interval `[a, b]`](hyp:hab), drawn from a prior
density `q` that is [continuously differentiable on `[a, b]`, nonnegative, positive on the
open interior, and vanishing at both endpoints](hyp:hq_deriv,hq_nonneg,hq_pos,hq_a,hq_b). Given
`h`, data are drawn from a law `P h` whose score function `S h` has
[conditional mean zero](hyp:hscore_mean) and [second moment equal to the Fisher information
`I h`](hyp:hfisher); let `δ` be an estimator of a target `ψ` that is
[differentiable with derivative `dψ`](hyp:hψ_deriv), whose posterior mean is
[differentiable with derivative equal to its covariance with the score](hyp:hDQM). Assume also
that `δ`, `S`, and their pointwise products are [integrable](hyp:hδ_int,hS_int,hδS_int,hSS_int),
that the three quadratic building blocks `(δ-ψ)²`, `(δ-ψ)(S+dq/q)`, `(S+dq/q)²` are
[integrable under `P h`](hyp:hEE_inner_int,hEPsi_inner_int,hPsiPsi_inner_int), that the
posterior-mean derivative, `dψ`, `dq`, and their combination are
[interval-integrable](hyp:hmprime_int,hdψ_int,hdq_int,hmprod_deriv_int), that `ψ·dq`, `dq²/q`,
and `I·q` are [interval-integrable](hyp:hψdq_int,hdq2q_int,hIq_int), and that the three
`h`-indexed second-moment integrands are
[interval-integrable](hyp:hEE_int,hEPsi_int,hPsiPsi_int) — the standard integrability side
conditions for the Bochner/interval-integral manipulations. Assume finally that [the total
information — prior information plus average experimental information — is
positive](hyp:hJ). Then [the Bayes mean-squared error
`∫ E_h[(δ − ψ h)²] q(h) dh` is at least `(∫ ψ'(h) q(h) dh)² / (I_q + ∫ I(h) q(h) dh)`, where
`I_q = ∫ q'(h)²/q(h) dh`](goal).

The hypotheses are the standard van Trees regularity conditions written in
"regularity (DQM) form": `hscore_mean` (score has conditional mean zero),
`hfisher` (`I h` is the conditional second moment of the score), and `hDQM`
(the posterior mean of `δ` is differentiable with derivative equal to its
covariance with the score). -/
@[deprecated (since := "2026-09-17")]
theorem van_trees_inequality_of_estimator_differentiation
    {Z : Type*} [MeasurableSpace Z]
    {a b : ℝ} (hab : a ≤ b)
    (P : ℝ → Measure Z) [∀ h, IsProbabilityMeasure (P h)]
    (δ : Z → ℝ) (ψ dψ q dq I : ℝ → ℝ) (S : ℝ → Z → ℝ)
    -- prior regularity: `q` is `C¹` on `[a,b]`, nonnegative, positive in the
    -- interior, vanishing at the endpoints
    (hq_deriv : ∀ h ∈ Icc a b, HasDerivAt q (dq h) h)
    (hq_nonneg : ∀ h ∈ Icc a b, 0 ≤ q h)
    (hq_pos : ∀ h ∈ Ioo a b, 0 < q h)
    (hq_a : q a = 0) (hq_b : q b = 0)
    -- target regularity: `ψ` differentiable with derivative `dψ`
    (hψ_deriv : ∀ h ∈ Icc a b, HasDerivAt ψ (dψ h) h)
    -- score / DQM regularity (the differentiation-in-quadratic-mean form)
    (hscore_mean : ∀ h ∈ Icc a b, ∫ z, S h z ∂(P h) = 0)
    (hfisher : ∀ h ∈ Icc a b, ∫ z, (S h z) ^ 2 ∂(P h) = I h)
    (hDQM : ∀ h ∈ Icc a b,
        HasDerivAt (fun h' => ∫ z, δ z ∂(P h')) (∫ z, δ z * S h z ∂(P h)) h)
    -- integrability side conditions for Bochner/interval integral linearity
    (hδ_int : ∀ h ∈ Icc a b, Integrable δ (P h))
    (hS_int : ∀ h ∈ Icc a b, Integrable (S h) (P h))
    (hδS_int : ∀ h ∈ Icc a b, Integrable (fun z => δ z * S h z) (P h))
    (hSS_int : ∀ h ∈ Icc a b, Integrable (fun z => S h z * S h z) (P h))
    (hEE_inner_int : ∀ h ∈ Icc a b,
        Integrable (fun z => (δ z - ψ h) * (δ z - ψ h)) (P h))
    (hEPsi_inner_int : ∀ h ∈ Icc a b,
        Integrable (fun z => (δ z - ψ h) * (S h z + dq h / q h)) (P h))
    (hPsiPsi_inner_int : ∀ h ∈ Icc a b,
        Integrable (fun z => (S h z + dq h / q h) * (S h z + dq h / q h)) (P h))
    (hmprime_int : IntervalIntegrable
        (fun h => ∫ z, δ z * S h z ∂(P h)) volume a b)
    (hdψ_int : IntervalIntegrable dψ volume a b)
    (hdq_int : IntervalIntegrable dq volume a b)
    (hmprod_deriv_int : IntervalIntegrable
        (fun h => (∫ z, δ z * S h z ∂(P h)) * q h
          + (∫ z, δ z ∂(P h)) * dq h) volume a b)
    (hψdq_int : IntervalIntegrable (fun h => ψ h * dq h) volume a b)
    (hdq2q_int : IntervalIntegrable (fun h => (dq h) ^ 2 / q h) volume a b)
    (hIq_int : IntervalIntegrable (fun h => I h * q h) volume a b)
    (hEE_int : IntervalIntegrable
        (fun h => (∫ z, (δ z - ψ h) * (δ z - ψ h) ∂(P h)) * q h) volume a b)
    (hEPsi_int : IntervalIntegrable
        (fun h => (∫ z, (δ z - ψ h) * (S h z + dq h / q h) ∂(P h)) * q h) volume a b)
    (hPsiPsi_int : IntervalIntegrable
        (fun h => (∫ z, (S h z + dq h / q h) * (S h z + dq h / q h) ∂(P h)) * q h)
        volume a b)
    -- positivity of the total information (prior + average experimental)
    (hJ : 0 < (∫ h in a..b, (dq h) ^ 2 / q h) + (∫ h in a..b, I h * q h)) :
    ((∫ h in a..b, dψ h * q h)) ^ 2
        / ((∫ h in a..b, (dq h) ^ 2 / q h) + (∫ h in a..b, I h * q h))
      ≤ ∫ h in a..b, (∫ z, (δ z - ψ h) ^ 2 ∂(P h)) * q h := by
  -- Abbreviations for the numerator (`A`), the total information (`J`) and the
  -- Bayes risk (`R`).
  set A : ℝ := ∫ h in a..b, dψ h * q h with hAdef
  set J : ℝ := (∫ h in a..b, (dq h) ^ 2 / q h) + (∫ h in a..b, I h * q h) with hJdef
  set R : ℝ := ∫ h in a..b, (∫ z, (δ z - ψ h) ^ 2 ∂(P h)) * q h with hRdef
  -- The weighted `L²(P h ⊗ q)` bilinear form, the error `e` and total score `Ψ`.
  set Bform : (ℝ → Z → ℝ) → (ℝ → Z → ℝ) → ℝ :=
    fun f g => ∫ h in a..b, (∫ z, f h z * g h z ∂(P h)) * q h with hBdef
  set e : ℝ → Z → ℝ := fun h z => δ z - ψ h with hedef
  set Ψ : ℝ → Z → ℝ := fun h z => S h z + dq h / q h with hΨdef
  -- === The five genuine analytic obligations (van Trees content) ===
  -- (0) The bilinear form on the error reproduces the Bayes risk.
  have hExx : Bform e e = R := by
    simp [hBdef, hRdef, hedef, pow_two]
  -- (1) NUMERATOR: integration by parts against the prior (`q a = q b = 0`),
  --     using `hDQM` (posterior-mean derivative = covariance with the score)
  --     and `hscore_mean` (mean-zero score).
  have hExPsi : Bform e Ψ = A := by
    let m : ℝ → ℝ := fun h => ∫ z, δ z ∂(P h)
    let mp : ℝ → ℝ := fun h => ∫ z, δ z * S h z ∂(P h)
    have hb_ae : ∀ᵐ h : ℝ ∂volume, h ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp
    have h_integrand :
        (∫ h in a..b, (∫ z, e h z * Ψ h z ∂(P h)) * q h)
          = ∫ h in a..b, (mp h * q h + m h * dq h) - ψ h * dq h := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hb_ae] with h hne_b
      intro hh
      have hhIoc : h ∈ Ioc a b := by
        simpa [uIoc, min_eq_left hab, max_eq_right hab] using hh
      have hhIoo : h ∈ Ioo a b :=
        ⟨hhIoc.1, lt_of_le_of_ne hhIoc.2 hne_b⟩
      have hhIcc : h ∈ Icc a b := ⟨le_of_lt hhIoc.1, hhIoc.2⟩
      let c : ℝ := dq h / q h
      have hq_ne : q h ≠ 0 := ne_of_gt (hq_pos h hhIoo)
      have hinner :
          (∫ z, e h z * Ψ h z ∂(P h))
            = mp h + c * m h - ψ h * c := by
        calc
          (∫ z, e h z * Ψ h z ∂(P h))
              = ∫ z, (δ z * S h z + c * δ z) - (ψ h * S h z + ψ h * c) ∂(P h) := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with z
                simp [hedef, hΨdef, c]
                ring
          _ = (∫ z, δ z * S h z + c * δ z ∂(P h))
                - ∫ z, ψ h * S h z + ψ h * c ∂(P h) := by
                have hsplit_sub := MeasureTheory.integral_sub
                  ((hδS_int h hhIcc).add ((hδ_int h hhIcc).const_mul c))
                  (((hS_int h hhIcc).const_mul (ψ h)).add (integrable_const (ψ h * c)))
                simpa [Pi.add_apply] using hsplit_sub
          _ = ((∫ z, δ z * S h z ∂(P h)) + ∫ z, c * δ z ∂(P h))
                - ((∫ z, ψ h * S h z ∂(P h)) + ∫ z, ψ h * c ∂(P h)) := by
                rw [MeasureTheory.integral_add
                  (hδS_int h hhIcc) ((hδ_int h hhIcc).const_mul c)]
                rw [MeasureTheory.integral_add
                  ((hS_int h hhIcc).const_mul (ψ h)) (integrable_const (ψ h * c))]
          _ = mp h + c * m h - ψ h * c := by
                rw [MeasureTheory.integral_const_mul]
                rw [MeasureTheory.integral_const_mul]
                rw [hscore_mean h hhIcc]
                simp [m, mp]
      calc
        (∫ z, e h z * Ψ h z ∂(P h)) * q h
            = (mp h + c * m h - ψ h * c) * q h := by
              rw [hinner]
        _ = (mp h * q h + m h * dq h) - ψ h * dq h := by
              rw [show c = dq h / q h by rfl]
              field_simp [hq_ne]
    have hm_ftc :
        (∫ h in a..b, mp h * q h + m h * dq h) = 0 := by
      have hderiv_mq :
          (∫ h in a..b, mp h * q h + m h * dq h)
            = m b * q b - m a * q a := by
        apply intervalIntegral.integral_deriv_mul_eq_sub
        · intro h hh
          have hhIcc : h ∈ Icc a b := by
            simpa [Set.uIcc_of_le hab] using hh
          exact hDQM h hhIcc
        · intro h hh
          have hhIcc : h ∈ Icc a b := by
            simpa [Set.uIcc_of_le hab] using hh
          exact hq_deriv h hhIcc
        · exact hmprime_int
        · exact hdq_int
      rw [hderiv_mq, hq_a, hq_b]
      ring
    have hψdq_eq :
        (∫ h in a..b, ψ h * dq h) = -A := by
      have hibp :
          (∫ h in a..b, ψ h * dq h)
            = ψ b * q b - ψ a * q a - ∫ h in a..b, dψ h * q h := by
        apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
        · intro h hh
          have hhIcc : h ∈ Icc a b := by
            simpa [Set.uIcc_of_le hab] using hh
          exact hψ_deriv h hhIcc
        · intro h hh
          have hhIcc : h ∈ Icc a b := by
            simpa [Set.uIcc_of_le hab] using hh
          exact hq_deriv h hhIcc
        · exact hdψ_int
        · exact hdq_int
      rw [hibp, hq_a, hq_b, hAdef]
      ring
    calc
      Bform e Ψ
          = ∫ h in a..b, (mp h * q h + m h * dq h) - ψ h * dq h := by
            simpa [hBdef] using h_integrand
      _ = (∫ h in a..b, mp h * q h + m h * dq h)
            - ∫ h in a..b, ψ h * dq h := by
            rw [intervalIntegral.integral_sub hmprod_deriv_int hψdq_int]
      _ = A := by
            rw [hm_ftc, hψdq_eq]
            ring
  -- (2) DENOMINATOR: variance decomposition of the total score, using
  --     `hfisher` (`E_h[S²] = I h`) and `hscore_mean`.
  have hPsiPsi : Bform Ψ Ψ = J := by
    have h_int :
        (∫ h in a..b, (∫ z, Ψ h z * Ψ h z ∂(P h)) * q h)
          = ∫ h in a..b, (I h * q h + (dq h) ^ 2 / q h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      have hhi : h ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using hh
      let c : ℝ := dq h / q h
      have hinner :
          (∫ z, Ψ h z * Ψ h z ∂(P h)) = I h + c ^ 2 := by
        calc
          (∫ z, Ψ h z * Ψ h z ∂(P h))
              = ∫ z, ((S h z * S h z) + (2 * c) * S h z + c * c) ∂(P h) := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with z
                simp [hΨdef, c]
                ring
          _ = (∫ z, S h z * S h z ∂(P h))
                + (∫ z, (2 * c) * S h z ∂(P h))
                + (∫ z, c * c ∂(P h)) := by
                have hsplit_outer := MeasureTheory.integral_add
                  ((hSS_int h hhi).add ((hS_int h hhi).const_mul (2 * c)))
                  (integrable_const (c * c))
                have hsplit_inner := MeasureTheory.integral_add
                  (hSS_int h hhi) ((hS_int h hhi).const_mul (2 * c))
                calc
                  (∫ z, S h z * S h z + (2 * c) * S h z + c * c ∂(P h))
                      = (∫ z, S h z * S h z + (2 * c) * S h z ∂(P h))
                          + ∫ z, c * c ∂(P h) := by
                        simpa [Pi.add_apply, add_assoc] using hsplit_outer
                  _ = (∫ z, S h z * S h z ∂(P h))
                          + (∫ z, (2 * c) * S h z ∂(P h))
                          + ∫ z, c * c ∂(P h) := by
                        rw [hsplit_inner]
          _ = I h + c ^ 2 := by
                have hSSval : (∫ z, S h z * S h z ∂(P h)) = I h := by
                  simpa [sq] using hfisher h hhi
                rw [MeasureTheory.integral_const_mul]
                rw [hscore_mean h hhi]
                rw [hSSval]
                simp [sq, c]
      calc
        (∫ z, Ψ h z * Ψ h z ∂(P h)) * q h
            = (I h + (dq h / q h) ^ 2) * q h := by
              simpa [c] using congrArg (fun x => x * q h) hinner
        _ = I h * q h + (dq h) ^ 2 / q h := by
              by_cases hq0 : q h = 0
              · simp [hq0]
              · field_simp [hq0]
    calc
      Bform Ψ Ψ = ∫ h in a..b, (I h * q h + (dq h) ^ 2 / q h) := by
        simpa [hBdef] using h_int
      _ = (∫ h in a..b, I h * q h)
            + (∫ h in a..b, (dq h) ^ 2 / q h) := by
        rw [intervalIntegral.integral_add hIq_int hdq2q_int]
      _ = J := by
        rw [hJdef]
        ring_nf
  -- (3) Bilinearity: expansion of the perturbed quadratic (needs integrability).
  have hexpand : ∀ t : ℝ,
      Bform (fun h z => e h z - t * Ψ h z) (fun h z => e h z - t * Ψ h z)
        = R - 2 * t * A + t ^ 2 * J := by
    intro t
    have h_expand_integral :
        Bform (fun h z => e h z - t * Ψ h z) (fun h z => e h z - t * Ψ h z)
          = Bform e e - (2 * t) * Bform e Ψ + t ^ 2 * Bform Ψ Ψ := by
      rw [hBdef]
      have hpoint :
          (∫ h in a..b,
              (∫ z, (e h z - t * Ψ h z) * (e h z - t * Ψ h z) ∂(P h)) * q h)
            = ∫ h in a..b,
                (∫ z, e h z * e h z ∂(P h)) * q h
                  - (2 * t) * ((∫ z, e h z * Ψ h z ∂(P h)) * q h)
                  + t ^ 2 * ((∫ z, Ψ h z * Ψ h z ∂(P h)) * q h) := by
        apply intervalIntegral.integral_congr
        intro h hh
        have hhIcc : h ∈ Icc a b := by
          simpa [Set.uIcc_of_le hab] using hh
        have hinner :
            (∫ z, (e h z - t * Ψ h z) * (e h z - t * Ψ h z) ∂(P h))
              = (∫ z, e h z * e h z ∂(P h))
                  - (2 * t) * (∫ z, e h z * Ψ h z ∂(P h))
                  + t ^ 2 * (∫ z, Ψ h z * Ψ h z ∂(P h)) := by
          calc
            (∫ z, (e h z - t * Ψ h z) * (e h z - t * Ψ h z) ∂(P h))
                = ∫ z, e h z * e h z - (2 * t) * (e h z * Ψ h z)
                    + t ^ 2 * (Ψ h z * Ψ h z) ∂(P h) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with z
                  ring
            _ = (∫ z, e h z * e h z ∂(P h))
                  - (2 * t) * (∫ z, e h z * Ψ h z ∂(P h))
                  + t ^ 2 * (∫ z, Ψ h z * Ψ h z ∂(P h)) := by
                  have hsub := MeasureTheory.integral_sub
                    (hEE_inner_int h hhIcc)
                    ((hEPsi_inner_int h hhIcc).const_mul (2 * t))
                  have hadd := MeasureTheory.integral_add
                    ((hEE_inner_int h hhIcc).sub
                      ((hEPsi_inner_int h hhIcc).const_mul (2 * t)))
                    ((hPsiPsi_inner_int h hhIcc).const_mul (t ^ 2))
                  have hsub' :
                      (∫ z, e h z * e h z - (2 * t) * (e h z * Ψ h z) ∂(P h))
                        = (∫ z, e h z * e h z ∂(P h))
                            - ∫ z, (2 * t) * (e h z * Ψ h z) ∂(P h) := by
                    simpa [hedef, hΨdef, Pi.sub_apply] using hsub
                  have hadd' :
                      (∫ z, e h z * e h z - (2 * t) * (e h z * Ψ h z)
                          + t ^ 2 * (Ψ h z * Ψ h z) ∂(P h))
                        = (∫ z, e h z * e h z - (2 * t) * (e h z * Ψ h z) ∂(P h))
                            + ∫ z, t ^ 2 * (Ψ h z * Ψ h z) ∂(P h) := by
                    simpa [hedef, hΨdef, Pi.add_apply, Pi.sub_apply, add_assoc] using hadd
                  rw [hadd', hsub']
                  rw [MeasureTheory.integral_const_mul]
                  rw [MeasureTheory.integral_const_mul]
        change
          (∫ z, (e h z - t * Ψ h z) * (e h z - t * Ψ h z) ∂(P h)) * q h
            = (∫ z, e h z * e h z ∂(P h)) * q h
                - (2 * t) * ((∫ z, e h z * Ψ h z ∂(P h)) * q h)
                + t ^ 2 * ((∫ z, Ψ h z * Ψ h z ∂(P h)) * q h)
        rw [hinner]
        ring
      calc
        (∫ h in a..b,
            (∫ z, (e h z - t * Ψ h z) * (e h z - t * Ψ h z) ∂(P h)) * q h)
            = ∫ h in a..b,
                (∫ z, e h z * e h z ∂(P h)) * q h
                  - (2 * t) * ((∫ z, e h z * Ψ h z ∂(P h)) * q h)
                  + t ^ 2 * ((∫ z, Ψ h z * Ψ h z ∂(P h)) * q h) := hpoint
        _ = (∫ h in a..b, (∫ z, e h z * e h z ∂(P h)) * q h)
              - (2 * t) * (∫ h in a..b, (∫ z, e h z * Ψ h z ∂(P h)) * q h)
              + t ^ 2 * (∫ h in a..b, (∫ z, Ψ h z * Ψ h z ∂(P h)) * q h) := by
              have hsub := intervalIntegral.integral_sub
                hEE_int (hEPsi_int.const_mul (2 * t))
              have hadd := intervalIntegral.integral_add
                (hEE_int.sub (hEPsi_int.const_mul (2 * t)))
                (hPsiPsi_int.const_mul (t ^ 2))
              rw [hadd]
              rw [hsub]
              rw [intervalIntegral.integral_const_mul]
              rw [intervalIntegral.integral_const_mul]
        _ = Bform e e - (2 * t) * Bform e Ψ + t ^ 2 * Bform Ψ Ψ := by
              simp [hBdef]
    rw [h_expand_integral, hExx, hExPsi, hPsiPsi]
  -- (4) Positive-semidefiniteness: the perturbed quadratic is a weighted integral
  --     of a square with nonnegative weight `q ≥ 0`, hence `≥ 0`.
  have hPSD : ∀ t : ℝ,
      0 ≤ Bform (fun h z => e h z - t * Ψ h z) (fun h z => e h z - t * Ψ h z) := by
    intro t
    rw [hBdef]
    apply intervalIntegral.integral_nonneg hab
    intro h hh
    exact mul_nonneg
      (MeasureTheory.integral_nonneg (fun z => by
        simpa [sq] using sq_nonneg (e h z - t * Ψ h z)))
      (hq_nonneg h hh)
  -- === Mechanical assembly: Cauchy–Schwarz via the discriminant ===
  have hquad : ∀ t : ℝ, 0 ≤ J * (t * t) + (-2 * A) * t + R := by
    intro t
    have hnn := hPSD t
    rw [hexpand t] at hnn
    nlinarith [hnn]
  have hdisc : discrim J (-2 * A) R ≤ 0 := by
    apply discrim_le_zero
    intro t
    have := hquad t
    nlinarith [this]
  have hmul : A ^ 2 ≤ R * J := by
    unfold discrim at hdisc
    nlinarith [hdisc]
  rw [div_le_iff₀ hJ]
  nlinarith [hmul]

/-- **Classical parameter-only van Trees inequality.** For [a dominating observation
measure](hyp:μ), [parameter endpoints](hyp:ell,u), [a prior and its derivative](hyp:w,dw),
[a likelihood and its derivative](hyp:p,dp), [a parameter-only target and its
derivative](hyp:ψ,dψ), and [an estimator](hyp:T), [a nondegenerate interval and the stated
prior, model, target, boundary, measurability, integrability, and positive-information
conditions](hyp:hellu,hwC1,hwsupport,hwderiv,hwnonneg,hwnorm,hpnonneg,hpnorm,hpint,hdpint,hdiffUnder,hpAC,hψAC,hdp,hψderiv,hboundary,hbalanceSm,hbalanceInt,herrorScoreSm,herrorScoreInt,hsensitivitySm,hsensitivityInt,herrorSqSm,herrorSqInt,hscoreSqSm,hscoreSqInt,hpriorSqSm,hpriorSqInt,hpriorJointSqSm,hpriorJointSqInt,hfisherSqSm,hfisherSqInt,hcrossSm,hcrossInt,hinfoPos),
[the squared prior-average derivative divided by prior plus average likelihood information is
at most the prior-average mean-squared error](goal).

This is a scalar, unweighted specialization of Gill--Levit (1995), Theorem 1, obtained by taking
one-dimensional parameters and targets with scalar unit weight. It specializes the
observation-dependent theorem with `g θ x = ψ θ`; the estimator-specific differentiation
identity is derived from model regularity. -/
theorem van_trees_inequality
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ell u : ℝ} (hellu : ell < u)
    (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ) (ψ dψ : ℝ → ℝ) (T : X → ℝ)
    (hwC1 : ContDiff ℝ 1 w)
    (hwsupport : Function.support w ⊆ Icc ell u)
    (hwderiv : ∀ θ, HasDerivAt w (dw θ) θ)
    (hwnonneg : ∀ θ, 0 ≤ w θ)
    (hwnorm : ∫ θ, w θ ∂ObservationDependentVanTrees.parameterMeasure ell u = 1)
    (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    (hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂μ = 1)
    (hpint : ∀ θ ∈ Icc ell u, Integrable (fun x => p θ x) μ)
    (hdpint : ∀ θ ∈ Icc ell u, Integrable (fun x => dp θ x) μ)
    (hdiffUnder : ∀ θ ∈ Ioo ell u,
      HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ)
    (hpAC : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u)
    (hψAC : AbsolutelyContinuousOnInterval ψ ell u)
    (hdp : ∀ᵐ z ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ),
      HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1)
    (hψderiv : ∀ θ, HasDerivAt ψ (dψ θ) θ)
    (hboundary : ∀ᵐ x ∂μ,
      w u * p u x * (T x - ψ u) = 0 ∧ w ell * p ell x * (T x - ψ ell) = 0)
    (hbalanceSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.derivativeBalanceField w dw p dp
        (fun θ _ => ψ θ) (fun θ _ => dψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hbalanceInt : Integrable
      (ObservationDependentVanTrees.derivativeBalanceField w dw p dp
        (fun θ _ => ψ θ) (fun θ _ => dψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorScoreSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.errorScoreField w dw p dp (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorScoreInt : Integrable
      (ObservationDependentVanTrees.errorScoreField w dw p dp (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hsensitivitySm : AEStronglyMeasurable
      (ObservationDependentVanTrees.sensitivityField w p (fun θ _ => dψ θ))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hsensitivityInt : Integrable
      (ObservationDependentVanTrees.sensitivityField w p (fun θ _ => dψ θ))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorSqSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.errorSqField w p (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (herrorSqInt : Integrable
      (ObservationDependentVanTrees.errorSqField w p (fun θ _ => ψ θ) T)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hscoreSqSm : AEStronglyMeasurable
      (ObservationDependentVanTrees.scoreSqField w dw p dp)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hscoreSqInt : Integrable (ObservationDependentVanTrees.scoreSqField w dw p dp)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hpriorSqSm : AEStronglyMeasurable
      (fun θ => w θ * (ObservationDependentVanTrees.priorScore w dw θ) ^ 2)
      (ObservationDependentVanTrees.parameterMeasure ell u))
    (hpriorSqInt : Integrable
      (fun θ => w θ * (ObservationDependentVanTrees.priorScore w dw θ) ^ 2)
      (ObservationDependentVanTrees.parameterMeasure ell u))
    (hpriorJointSqSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hpriorJointSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hfisherSqSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hfisherSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2) ^ 2)
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hcrossSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1 *
          ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hcrossInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 *
        (ObservationDependentVanTrees.priorScore w dw z.1 *
          ObservationDependentVanTrees.likelihoodScore p dp z.1 z.2))
      ((ObservationDependentVanTrees.parameterMeasure ell u).prod μ))
    (hinfoPos : 0 < ObservationDependentVanTrees.priorInformation ell u w dw +
      ∫ θ, w θ * ObservationDependentVanTrees.fisherInformation μ p dp θ
        ∂ObservationDependentVanTrees.parameterMeasure ell u) :
    (∫ θ, dψ θ * w θ ∂ObservationDependentVanTrees.parameterMeasure ell u) ^ 2 /
        (ObservationDependentVanTrees.priorInformation ell u w dw +
          ∫ θ, w θ * ObservationDependentVanTrees.fisherInformation μ p dp θ
            ∂ObservationDependentVanTrees.parameterMeasure ell u) ≤
      ∫ θ, (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
        ∂ObservationDependentVanTrees.parameterMeasure ell u := by
  letI : IsFiniteMeasure (ObservationDependentVanTrees.parameterMeasure ell u) := by
    unfold ObservationDependentVanTrees.parameterMeasure
    infer_instance
  let g : ℝ → X → ℝ := fun θ _ => ψ θ
  let dg : ℝ → X → ℝ := fun θ _ => dψ θ
  have hraw := ObservationDependentVanTrees.observation_dependent_van_trees μ hellu
    w dw p dp g dg T hwC1 hwsupport hwderiv hwnonneg hwnorm hpnonneg hpnorm hpint hdpint
    hdiffUnder hpAC (Filter.Eventually.of_forall fun _ => hψAC) hdp
    (Filter.Eventually.of_forall fun z => hψderiv z.1) hboundary hbalanceSm hbalanceInt
    herrorScoreSm herrorScoreInt hsensitivitySm hsensitivityInt herrorSqSm herrorSqInt
    hscoreSqSm hscoreSqInt hpriorSqSm hpriorSqInt hpriorJointSqSm hpriorJointSqInt
    hfisherSqSm hfisherSqInt hcrossSm hcrossInt hinfoPos
  have hsensitivity :
      ∫ z, ObservationDependentVanTrees.sensitivityField w p dg z
          ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ) =
        ∫ θ, dψ θ * w θ ∂ObservationDependentVanTrees.parameterMeasure ell u := by
    rw [integral_prod _ hsensitivityInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    change (∫ x, dψ θ * (w θ * p θ x) ∂μ) = dψ θ * w θ
    rw [show (fun x => dψ θ * (w θ * p θ x)) =
        fun x => (dψ θ * w θ) * p θ x by funext x; ring,
      MeasureTheory.integral_const_mul, hpnorm θ hθ, mul_one]
  have hrisk :
      ∫ z, ObservationDependentVanTrees.errorSqField w p g T z
          ∂((ObservationDependentVanTrees.parameterMeasure ell u).prod μ) =
        ∫ θ, (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
          ∂ObservationDependentVanTrees.parameterMeasure ell u := by
    rw [integral_prod _ herrorSqInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    change (∫ x, (T x - ψ θ) ^ 2 * (w θ * p θ x) ∂μ) =
      (∫ x, (T x - ψ θ) ^ 2 * p θ x ∂μ) * w θ
    rw [show (fun x => (T x - ψ θ) ^ 2 * (w θ * p θ x)) =
        fun x => ((T x - ψ θ) ^ 2 * p θ x) * w θ by funext x; ring,
      MeasureTheory.integral_mul_const]
  simpa [g, dg, hsensitivity, hrisk] using hraw

end Causalean.Stat.Minimax

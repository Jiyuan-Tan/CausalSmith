/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.SeriesSieve.LeastSquares
public import Causalean.Stat.Nonparametric.SeriesSieve.Prediction

/-!
# Conditional series least-squares prediction bound under an assumed Jackson objective bound

The Causalean file `Causalean.Stat.Nonparametric.SeriesSieve.Prediction` proves a *conditional*
oracle inequality `seriesLS_expected_prediction_le`:

    𝔼[‖f − Φ·ĉ‖²_w] ≤ A + σ² · V,

where `A` is any bound on the noise-free least-squares objective (bias side) and `V` is any bound
on the effective-degrees-of-freedom sum `∑ᵢ wᵢ ∑ₖ aᵢₖ²` (variance side). This module rewrites an
explicitly assumed Jackson-shaped objective bound and derives the finite-dimensional hat-matrix
term. It does not prove that the piecewise-Taylor approximant belongs to a chosen series span.

## Main results

* `seriesBiasRate_of_jackson_bound` — rewrites the assumed Jackson objective bound
  `A ≤ (∑ᵢ wᵢ)·(C_J·J^{−s/d})²` into the explicit bias rate `A ≤ ((∑ᵢ wᵢ)·C_J²)·J^{−2s/d}`.
  The Jackson approximation power of the sieve is taken as an explicit hypothesis (no attempt to
  prove Jackson's theorem for a concrete basis).
* `seriesEffectiveDoF_le` — converts a Frobenius bound into the normalized `J/N` scale.
* `seriesLS_prediction_rate_of_jackson_bound` — constructs the least-squares coefficients and hat
  matrix from `Φ`, conditional on the Jackson objective bound. Gram invertibility supplies the
  normal equations, fitted-value linearity, and the exact identity `∑ᵢₖ Hᵢₖ² = J`, so neither
  linearity nor a trace bound is assumed.

Here `J^{−s/d}` is the real power `(J : ℝ) ^ (-(s/d))` (`Real.rpow`), keeping `s, d, J, N, σ` as
free parameters. A caller must separately justify the assumed objective bound for its basis and
dimension; the classical series-estimator and Jackson literature is motivation, not a result
formalized by this module.
-/

public section

open Causalean.Mathlib.LinearAlgebra.NormalEquations

namespace Causalean.Stat.Nonparametric.SeriesSieve

open Causalean.Stat.Nonparametric
open scoped BigOperators

/-- **Bias-rate rewrite from an assumed Jackson objective bound.** If [the noise-free
least-squares objective `A := lstsqObjective Φ w f c0` obeys the squared Jackson
best-approximation bound `A ≤ (∑ᵢ wᵢ)·(C_J·J^{−s/d})²`](hyp:hJack) — the shape produced by
`seriesApprox_le_of_sup` with sup-error `δ = C_J·J^{−s/d}` — then [the same objective satisfies
the explicit doubled-exponent bias rate `A ≤ ((∑ᵢ wᵢ)·C_J²) · J^{−2s/d}`](goal):

    A ≤ ((∑ᵢ wᵢ)·C_J²) · J^{−2s/d}.

The power `J^{−s/d}` is the real power `(J : ℝ) ^ (-(s/d))`; squaring it doubles the exponent to
`−2s/d`. The Jackson approximation power is an assumed hypothesis (no concrete basis). -/
theorem seriesBiasRate_of_jackson_bound {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c0 : ι → ℝ}
    {s d C_J : ℝ} {J : ℕ}
    (hJack : lstsqObjective Φ w f c0
      ≤ (∑ i, w i) * (C_J * (J : ℝ) ^ (-(s / d))) ^ 2) :
    lstsqObjective Φ w f c0 ≤ ((∑ i, w i) * C_J ^ 2) * (J : ℝ) ^ (-(2 * s / d)) := by
  -- Rewrite the squared Jackson bound into the doubled-exponent rate, then transfer `hJack`.
  have hpow : ((J : ℝ) ^ (-(s / d))) ^ 2 = (J : ℝ) ^ (-(2 * s / d)) := by
    rw [← Real.rpow_natCast ((J : ℝ) ^ (-(s / d))) 2,
        ← Real.rpow_mul (Nat.cast_nonneg J)]
    congr 1
    push_cast
    ring
  have hrw : (∑ i, w i) * (C_J * (J : ℝ) ^ (-(s / d))) ^ 2
      = ((∑ i, w i) * C_J ^ 2) * (J : ℝ) ^ (-(2 * s / d)) := by
    rw [mul_pow, hpow]; ring
  exact hJack.trans_eq hrw

/-- **Effective degrees of freedom is controlled by `J/N`.** If [the sample size `N` is
positive](hyp:hN), [the least-squares weights are normalized as `wᵢ = 1/N`](hyp:hw), and [the hat
map `a` obeys the Frobenius/trace bound `∑ᵢ ∑ₖ aᵢₖ² ≤ Cvar·J`](hyp:htr), then [the weighted
coefficient sum — the effective degrees of freedom `V` of the oracle inequality — obeys the bound
`Cvar · J / N`](goal):

    ∑ᵢ wᵢ ∑ₖ aᵢₖ² ≤ Cvar · J / N.

For a rank-`J` projection hat matrix the Frobenius sum equals the trace `= J`, so this expresses the
standard "effective DoF ≈ J" fact after normalization by `N`; the trace bound is taken as an
explicit hypothesis rather than derived from an explicit Gram matrix. -/
theorem seriesEffectiveDoF_le {N : ℕ} {a : Fin N → Fin N → ℝ} {w : Fin N → ℝ}
    {Cvar : ℝ} {J : ℕ} (hN : 0 < N)
    (hw : ∀ i, w i = (1 : ℝ) / N)
    (htr : (∑ i, ∑ k, a i k ^ 2) ≤ Cvar * J) :
    (∑ i, w i * ∑ k, a i k ^ 2) ≤ Cvar * (J : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (∑ i, w i * ∑ k, a i k ^ 2)
        = (1 / (N : ℝ)) * ∑ i, ∑ k, a i k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [hw i])
    _ ≤ (1 / (N : ℝ)) * (Cvar * J) := by
          exact mul_le_mul_of_nonneg_left htr (by positivity)
    _ = Cvar * (J : ℝ) / N := by ring

/-- **Series least-squares prediction bound under an assumed Jackson objective bound.** Assume [a
positive sample size](hyp:hN), [an invertible series Gram matrix](hyp:hGram), and [an error
family that is square-integrable](hyp:hε), [mean zero](hyp:hmean), and [uncorrelated with
coordinate variances
bounded by `σbar²`](hyp:hnoise). If [the noise-free closed-form least-squares fit obeys the squared
Jackson approximation bound](hyp:hJack), then [the expected normalized prediction error of the
closed-form fit to `f+ε` is at most the doubled-exponent Jackson term plus
`σbar² · card(ι)/N`](goal).  The normal equations, least-squares linearity, and exact hat-matrix
Frobenius identity are conclusions of Gram invertibility, not assumptions. -/
theorem seriesLS_prediction_rate_of_jackson_bound {Ω : Type*} {N : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Φ : Matrix (Fin N) ι ℝ} {f : Fin N → ℝ} {ε : Fin N → Ω → ℝ}
    {s d C_J σbar : ℝ}
    (hN : 0 < N)
    (hGram : IsUnit (seriesGram Φ).det)
    (hε : ∀ k, MeasureTheory.MemLp (ε k) 2 μ)
    (hmean : ∀ k, ∫ ω, ε k ω ∂μ = 0)
    (hnoise : UncorrelatedVarianceFamily ε μ σbar)
    (hJack : lstsqObjective Φ (fun _ => (1 : ℝ) / N) f (seriesLSCoeff Φ f)
      ≤ (∑ _i : Fin N, (1 : ℝ) / N) *
        (C_J * (Fintype.card ι : ℝ) ^ (-(s / d))) ^ 2) :
    ∫ ω, lstsqObjective Φ (fun _ => (1 : ℝ) / N) f
        (seriesLSCoeff Φ (f + fun i => ε i ω)) ∂μ
      ≤ ((∑ _i : Fin N, (1 : ℝ) / N) * C_J ^ 2) *
          (Fintype.card ι : ℝ) ^ (-(2 * s / d)) +
        σbar ^ 2 * ((Fintype.card ι : ℝ) / N) := by
  let w : Fin N → ℝ := fun _ => (1 : ℝ) / N
  let c0 : ι → ℝ := seriesLSCoeff Φ f
  let chat : Ω → ι → ℝ := fun ω => seriesLSCoeff Φ (f + fun i => ε i ω)
  let H : Matrix (Fin N) (Fin N) ℝ := seriesHatMatrix Φ
  let a : Fin N → Fin N → ℝ := fun i k => -H i k
  have hw : ∀ i, w i = (1 : ℝ) / N := fun _ => rfl
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    simp [w]
  have hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ f c0 i * Φ i k = 0 := by
    intro k
    have hnormal := seriesLSCoeff_normal_equations Φ f hGram k
    calc
      ∑ i, w i * lstsqResidual Φ f c0 i * Φ i k
          = (1 / (N : ℝ)) * ∑ i, lstsqResidual Φ f c0 i * Φ i k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp [w]
              ring
      _ = 0 := by simp [c0, hnormal]
  have hlin : ∀ ω, ∀ i,
      (∑ j, (c0 j - chat ω j) * Φ i j) = ∑ k, a i k * ε k ω := by
    intro ω i
    have hv := congrFun
      (seriesLS_fitted_sub_eq_neg_hat Φ f (fun k => ε k ω)) i
    simpa [Matrix.mulVec, dotProduct, c0, chat, a, H, mul_comm] using hv
  have htr : (∑ i, ∑ k, a i k ^ 2) ≤ (1 : ℝ) * Fintype.card ι := by
    have hF := seriesHatMatrix_frobenius_sq Φ hGram
    simpa [a, H] using hF.le
  have hA := seriesBiasRate_of_jackson_bound (Φ := Φ) (w := w) (f := f) (c0 := c0)
    (s := s) (d := d) (C_J := C_J) (J := Fintype.card ι) (by simpa [w, c0] using hJack)
  have hV := seriesEffectiveDoF_le (a := a) (w := w) (Cvar := (1 : ℝ))
    (J := Fintype.card ι) hN hw htr
  simpa [w, c0, chat] using
    (seriesLS_expected_prediction_le hortho hA hlin hw_nonneg hε hmean hnoise hV)

end Causalean.Stat.Nonparametric.SeriesSieve

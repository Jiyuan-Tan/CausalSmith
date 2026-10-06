/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.PerSample

/-! # Primal NPIV rate with a regularization sequence

This module gives the fixed-sample, fixed-confidence rate for a TRAE estimator
using `lambda n`.  Its constants come from a uniform Tikhonov certificate and
therefore do not depend on the selected regularization level.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open Filter MeasureTheory Causalean.Stat

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

private lemma strong_rate_at_of_combined
    {S : OperatorSystem Omega mu} {beta lambda delta K : ℝ}
    (sc : SourceCondition S beta)
    (tb : TikhonovBiasBoundAt S beta lambda sc)
    (hhat : S.PrimalL2)
    (hlambda_lt : lambda < 2)
    (hK : 0 ≤ K)
    (hcombined :
      lambda * (S.strongNorm (hhat - S.hL2 tb.h_lambda_star_mem)) ^ 2
          + (S.weakNorm (hhat - S.hL2 tb.h_lambda_star_mem)) ^ 2
        ≤ K *
            ((S.weakNorm
                (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
              + delta ^ 2)) :
    (S.strongNorm (hhat - S.hL2 S.h₀_mem)) ^ 2
      ≤ (2 * K + 2 * K * tb.C + 4 * tb.C) *
          (delta ^ 2 / lambda
            + S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min beta 1)) := by
  let hstar := S.hL2 tb.h_lambda_star_mem
  let hzero := S.hL2 S.h₀_mem
  let x := S.strongNorm (hhat - hstar)
  let b := S.strongNorm (hstar - hzero)
  let r := S.weakNorm (hstar - hzero)
  let W := S.strongNorm (S.hL2 sc.w₀_mem)
  let X := delta ^ 2 / lambda
  let Y := W * lambda ^ (min beta 1)
  let u := S.strongNorm (hhat - hzero)
  have hlambda : 0 < lambda := tb.lambda_pos
  have hlambda_nonneg : 0 ≤ lambda := hlambda.le
  have hx : 0 ≤ x := by simp [x, OperatorSystem.strongNorm]
  have hb : 0 ≤ b := by simp [b, OperatorSystem.strongNorm]
  have hu : 0 ≤ u := by simp [u, OperatorSystem.strongNorm]
  have hW : 0 ≤ W := by simp [W, OperatorSystem.strongNorm]
  have hX : 0 ≤ X := div_nonneg (sq_nonneg delta) hlambda_nonneg
  have hY : 0 ≤ Y :=
    mul_nonneg hW (Real.rpow_nonneg hlambda_nonneg _)
  have hexp : min (beta + 1) 2 - 1 = min beta 1 := by
    by_cases hbeta : beta ≤ 1
    · rw [min_eq_left hbeta, min_eq_left (by linarith : beta + 1 ≤ 2)]
      ring
    · have hbeta' : 1 ≤ beta := le_of_not_ge hbeta
      rw [min_eq_right hbeta', min_eq_right (by linarith : 2 ≤ beta + 1)]
      ring
  have hpow_div :
      lambda ^ (min (beta + 1) 2) / lambda = lambda ^ (min beta 1) := by
    rw [← Real.rpow_sub_one hlambda.ne', hexp]
  have hstrong_pow :
      lambda ^ (min beta 2) ≤ 2 * lambda ^ (min beta 1) := by
    by_cases hbeta : beta ≤ 1
    · rw [min_eq_left (hbeta.trans (by norm_num)), min_eq_left hbeta]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hlambda_nonneg _)
        (by norm_num)
    · have hbeta' : 1 ≤ beta := le_of_not_ge hbeta
      rw [min_eq_right hbeta']
      by_cases hle : lambda ≤ 1
      · have hp := Real.rpow_le_rpow_of_exponent_ge hlambda hle
          (le_min hbeta' (by norm_num : (1 : ℝ) ≤ 2))
        have hp2 : lambda ^ (1 : ℝ) ≤ 2 * lambda ^ (1 : ℝ) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hlambda_nonneg _) (by norm_num)
        simpa [Real.rpow_one] using hp.trans hp2
      · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hle)
          (min_le_right beta 2)
        have hp2 : lambda ^ (2 : ℝ) ≤ 2 * lambda := by
          rw [Real.rpow_two]
          nlinarith
        simpa [Real.rpow_one] using hp.trans hp2
  have htri : u ≤ x + b := by
    simp only [u, x, b, OperatorSystem.strongNorm]
    have hdecomp : hhat - hzero = (hhat - hstar) + (hstar - hzero) := by abel
    rw [hdecomp]
    exact norm_add_le _ _
  have hu_sq : u ^ 2 ≤ 2 * (x ^ 2 + b ^ 2) := by
    have hsq : u ^ 2 ≤ (x + b) ^ 2 := by
      nlinarith [htri, hu, hx, hb, sq_nonneg (x + b - u)]
    exact hsq.trans add_sq_le
  have hdrop : lambda * x ^ 2 ≤ K * (r ^ 2 + delta ^ 2) := by
    have hw : 0 ≤ (S.weakNorm (hhat - hstar)) ^ 2 := sq_nonneg _
    dsimp [x, r, hstar, hzero] at hcombined ⊢
    nlinarith
  have hx_sq : x ^ 2 ≤ K * (r ^ 2 / lambda + delta ^ 2 / lambda) := by
    have hd := div_le_div_of_nonneg_right hdrop hlambda_nonneg
    calc
      x ^ 2 = lambda * x ^ 2 / lambda := by field_simp [hlambda.ne']
      _ ≤ K * (r ^ 2 + delta ^ 2) / lambda := hd
      _ = K * (r ^ 2 / lambda + delta ^ 2 / lambda) := by
        field_simp [hlambda.ne']
  have hr_div : r ^ 2 / lambda ≤ tb.C * Y := by
    have hbias :
        r ^ 2 ≤ tb.C * W * lambda ^ (min (beta + 1) 2) := by
      simpa [r, W, hstar, hzero] using tb.weak_bias
    have hd := div_le_div_of_nonneg_right hbias hlambda_nonneg
    calc
      r ^ 2 / lambda
          ≤ (tb.C * W * lambda ^ (min (beta + 1) 2)) / lambda := hd
      _ = tb.C * Y := by simp only [Y]; rw [mul_div_assoc, hpow_div]; ring
  have hx_bound : x ^ 2 ≤ K * X + K * tb.C * Y := by
    calc
      x ^ 2 ≤ K * (r ^ 2 / lambda + delta ^ 2 / lambda) := hx_sq
      _ ≤ K * (tb.C * Y + X) := by gcongr
      _ = K * X + K * tb.C * Y := by ring
  have hb_bound : b ^ 2 ≤ 2 * tb.C * Y := by
    have hbias : b ^ 2 ≤ tb.C * W * lambda ^ (min beta 2) := by
      simpa [b, W, hstar, hzero] using tb.strong_bias
    have hCW : 0 ≤ tb.C * W := mul_nonneg tb.C_nonneg hW
    calc
      b ^ 2 ≤ tb.C * W * lambda ^ (min beta 2) := hbias
      _ ≤ tb.C * W * (2 * lambda ^ (min beta 1)) := by gcongr
      _ = 2 * tb.C * Y := by simp only [Y]; ring
  calc
    (S.strongNorm (hhat - S.hL2 S.h₀_mem)) ^ 2 = u ^ 2 := by rfl
    _ ≤ 2 * (x ^ 2 + b ^ 2) := hu_sq
    _ ≤ 2 * K * X + (2 * K * tb.C + 4 * tb.C) * Y := by
      nlinarith [hx_bound, hb_bound]
    _ ≤ (2 * K + 2 * K * tb.C + 4 * tb.C) * (X + Y) := by
      have hC := tb.C_nonneg
      nlinarith [mul_nonneg hK hX, mul_nonneg hK hY,
        mul_nonneg hC hX, mul_nonneg hC hY]
    _ = (2 * K + 2 * K * tb.C + 4 * tb.C) *
          (delta ^ 2 / lambda
            + S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min beta 1)) := by
      rfl

/-- Given [a source condition](hyp:sc), [a uniform source-condition bias
certificate](hyp:bias), [a
sample-size-dependent TRAE estimator](hyp:is_estimator), [a positive
regularization sequence bounded above by two](hyp:hlambda_pos,hlambda_lt),
[the localized regime at index `n`](hyp:regime), [a positive fold size](hyp:hn),
[a fixed confidence level
	between zero and one](hyp:hzeta_pos,hzeta_lt), and [the fixed-confidence
	critical-radius floor](hyp:floor), [the corresponding fixed-level peeling
floor](hyp:peeling), and [the sample-size index](hyp:n),
[there is an event of probability at least `1 - zeta` on which the squared
strong error is bounded by the displayed level-independent constant times
`delta n ^ 2 / lambda_n n + norm(w0) * (lambda_n n) ^ min beta 1`](goal).

This is the fixed-`n` NPIV Tikhonov rate.  In contrast to a simultaneous
countable-intersection statement, its confidence term is `log (4 / zeta)`;
choosing `lambda_n` to vanish is therefore compatible with a vanishing rate. -/
theorem trae_primal_rate
    {S : OperatorSystem Omega mu} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Omega S.𝒲 mu P_W}
    {split : OneShotSplit sample}
    {lambda_n : ℕ → ℝ} {beta : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Omega → S.𝒳 → ℝ}
    {n : ℕ}
    (is_estimator :
      IsTRAEPrimalEstimatorSequence S TC sample split lambda_n h_hat)
    (sc : SourceCondition S beta)
    (bias : TikhonovBiasBound S beta sc)
    [IsProbabilityMeasure mu]
    (hlambda_pos : ∀ j, 0 < lambda_n j)
    (hlambda_lt : ∀ j, lambda_n j < 2)
    (regime : LocalizedRegimes S TC sample sc
      { uniform := bias, lambda_pos := hlambda_pos n }
      (split.n₁ n) (delta n))
    (hn : 1 ≤ split.n₁ n)
    {zeta : ℝ}
    (hzeta_pos : 0 < zeta) (hzeta_lt : zeta < 1)
    (floor : PerSampleConfidenceFloor regime zeta)
    (peeling : PeelingFloor regime (zeta / 4)) :
    ∃ A : Set Omega,
      MeasurableSet A ∧ mu A ≥ 1 - ENNReal.ofReal zeta ∧
      ∀ omega ∈ A,
        (S.strongNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
              - S.hL2 S.h₀_mem)) ^ 2
          ≤ (2 * 320 + 2 * 320 * bias.C + 4 * bias.C) *
              ((delta n) ^ 2 / lambda_n n
                + S.strongNorm (S.hL2 sc.w₀_mem) *
                    (lambda_n n) ^ (min beta 1)) := by
  let tb : TikhonovBiasBoundAt S beta (lambda_n n) sc :=
    { uniform := bias, lambda_pos := hlambda_pos n }
  obtain ⟨A, hAmeas, hAmass, hA⟩ :=
    per_sample_empirical_process_event is_estimator sc tb regime hn
      hzeta_pos hzeta_lt (hlambda_pos n).le floor peeling
  let Cstrong := 2 * 320 + 2 * 320 * bias.C + 4 * bias.C
  refine ⟨A, hAmeas, hAmass, ?_⟩
  · intro omega homega
    let hh := TC.H_subset (is_estimator.mem_H n omega)
    have hsc := tb.strong_convexity (h_hat n omega) hh
    have hep := hA omega homega
    have hcombined :
        lambda_n n *
            (S.strongNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)) ^ 2
          + (S.weakNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)) ^ 2
          ≤ 320 *
              ((S.weakNorm
                  (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
                + (delta n) ^ 2) := by
      let x := S.strongNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)
      let y := S.weakNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)
      let d := delta n
      have hpre :
          lambda_n n * x ^ 2 + y ^ 2
            ≤ 50 * d ^ 2 + lambda_n n * (10 * d * x + 5 * d ^ 2) := by
        simpa [x, y, d, hh] using hsc.trans hep
      have hyoung : 10 * d * x ≤ (1 / 2 : ℝ) * x ^ 2 + 50 * d ^ 2 := by
        nlinarith [sq_nonneg (x - 10 * d)]
      have hyoung_lambda :=
        mul_le_mul_of_nonneg_left hyoung (hlambda_pos n).le
      have hlambda_d : lambda_n n * d ^ 2 ≤ 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_right (hlambda_lt n).le (sq_nonneg d)
      have hdelta :
          lambda_n n * x ^ 2 + y ^ 2 ≤ 320 * d ^ 2 := by
        nlinarith [hpre, hyoung_lambda, hlambda_d, sq_nonneg y]
      calc
        _ ≤ 320 * d ^ 2 := hdelta
        _ ≤ 320 *
            ((S.weakNorm
                (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
              + d ^ 2) := by
            nlinarith [sq_nonneg
              (S.weakNorm
                (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem))]
    have hrate := strong_rate_at_of_combined sc tb (S.hL2 hh)
      (hlambda_lt n) (by norm_num : (0 : ℝ) ≤ 320) hcombined
    simpa [Cstrong, hh, tb] using hrate

/-- For [a primal TRAE estimator sequence](hyp:is_estimator), [a positive
source exponent](hyp:hbeta) with [source condition and uniform bias
certificate](hyp:sc,bias), [positive regularization levels below
two](hyp:hlambda_pos,hlambda_lt), [localized regimes](hyp:regimes),
[fixed-confidence critical-radius
floors](hyp:floors), and [fixed-level peeling floors](hyp:peeling), suppose
the [failure probabilities vanish](hyp:hzeta_zero) while remaining [strictly
between zero and one](hyp:hzeta_pos,hzeta_lt), the [localization radii
vanish](hyp:hdelta_zero), the [regularization levels
vanish](hyp:hlambda_zero), and the [variance term `delta n² / lambda_n n`
vanishes](hyp:hdelta_sq_div_lambda_zero).  Then [the primal strong-norm error
converges to zero in probability](goal).

The nuisance-fold size is eventually positive because every `OneShotSplit`
requires it to tend to infinity; no impossible positivity condition at sample
size zero is imposed. The compatibility condition is stated explicitly:
localization must shrink faster than the square root of the regularization
level. The source exponent and `lambda_n → 0` discharge the remaining
Tikhonov bias term. -/
theorem primal_strongNorm_tendstoInProb_of_rates
    {S : OperatorSystem Omega mu} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Omega S.𝒲 mu P_W}
    {split : OneShotSplit sample}
    {lambda_n : ℕ → ℝ} {beta : ℝ} {delta zeta : ℕ → ℝ}
    {h_hat : ℕ → Omega → S.𝒳 → ℝ}
    (is_estimator :
      IsTRAEPrimalEstimatorSequence S TC sample split lambda_n h_hat)
    (sc : SourceCondition S beta)
    (bias : TikhonovBiasBound S beta sc)
    [IsProbabilityMeasure mu]
    (hbeta : 0 < beta)
    (hlambda_pos : ∀ n, 0 < lambda_n n)
    (hlambda_lt : ∀ n, lambda_n n < 2)
    (regimes : ∀ n, LocalizedRegimes S TC sample sc
      { uniform := bias, lambda_pos := hlambda_pos n }
      (split.n₁ n) (delta n))
    (hzeta_pos : ∀ n, 0 < zeta n)
    (hzeta_lt : ∀ n, zeta n < 1)
    (floors : ∀ n, PerSampleConfidenceFloor (regimes n) (zeta n))
    (peeling : ∀ n, PeelingFloor (regimes n) (zeta n / 4))
    (hzeta_zero : Tendsto zeta atTop (nhds 0))
    (hdelta_zero : Tendsto delta atTop (nhds 0))
    (hlambda_zero : Tendsto lambda_n atTop (nhds 0))
    (hdelta_sq_div_lambda_zero :
      Tendsto (fun n => (delta n) ^ 2 / lambda_n n) atTop (nhds 0)) :
    Tendsto_inProb
      (fun n omega =>
        S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
            - S.hL2 S.h₀_mem))
      (fun _ => 0) mu := by
  have _hdelta_sq_zero :
      Tendsto (fun n => (delta n) ^ 2) atTop (nhds 0) := by
    simpa [pow_two] using hdelta_zero.mul hdelta_zero
  let p : ℝ := min beta 1
  have hp : 0 < p := lt_min hbeta (by norm_num)
  have hlambda_pow :
      Tendsto (fun n => (lambda_n n) ^ p) atTop (nhds 0) := by
    have h := hlambda_zero.rpow_const (Or.inr hp.le)
    simpa [Real.zero_rpow hp.ne'] using h
  have hbias_rate :
      Tendsto
        (fun n => S.strongNorm (S.hL2 sc.w₀_mem) * (lambda_n n) ^ p)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlambda_pow
  have htotal_rate :
      Tendsto
        (fun n => (delta n) ^ 2 / lambda_n n
          + S.strongNorm (S.hL2 sc.w₀_mem) * (lambda_n n) ^ p)
        atTop (nhds 0) := by
    simpa using hdelta_sq_div_lambda_zero.add hbias_rate
  let C : ℝ := 2 * 320 + 2 * 320 * bias.C + 4 * bias.C
  have hC_rate :
      Tendsto
        (fun n => C * ((delta n) ^ 2 / lambda_n n
          + S.strongNorm (S.hL2 sc.w₀_mem) * (lambda_n n) ^ p))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul htotal_rate
  rw [Tendsto_inProb_iff]
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n in atTop,
      C * ((delta n) ^ 2 / lambda_n n
        + S.strongNorm (S.hL2 sc.w₀_mem) * (lambda_n n) ^ p)
        < epsilon ^ 2 :=
    (tendsto_order.1 hC_rate).2 (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  have hzeta_enn :
      Tendsto (fun n => ENNReal.ofReal (zeta n)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hzeta_zero
  have hn : ∀ᶠ n in atTop, 1 ≤ split.n₁ n :=
    (Filter.tendsto_atTop.1 split.grow) 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hzeta_enn
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hsmall, hn] with n hnsmall hn_pos
  obtain ⟨A, hAmeas, hAmass, hAbound⟩ :=
    trae_primal_rate is_estimator sc bias hlambda_pos hlambda_lt
      (regimes n) hn_pos (hzeta_pos n) (hzeta_lt n) (floors n) (peeling n)
  have hbad_subset :
      {omega | epsilon ≤
          ‖S.strongNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
                - S.hL2 S.h₀_mem) - 0‖} ⊆ Aᶜ := by
    intro omega homega
    by_contra homega_compl
    have homega_A : omega ∈ A := by simpa using homega_compl
    have hnorm_nonneg :
        0 ≤ S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
            - S.hL2 S.h₀_mem) := norm_nonneg _
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg hnorm_nonneg] at homega
    have hsq := hAbound omega homega_A
    change _ ≤ C * _ at hsq
    change _ < epsilon ^ 2 at hnsmall
    simp only [p] at hsq hnsmall
    have : epsilon ^ 2 ≤
        (S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
            - S.hL2 S.h₀_mem)) ^ 2 := by nlinarith
    nlinarith
  calc
    mu {omega | epsilon ≤
        ‖S.strongNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
              - S.hL2 S.h₀_mem) - 0‖}
        ≤ mu Aᶜ := measure_mono hbad_subset
    _ ≤ ENNReal.ofReal (zeta n) := by
      rw [measure_compl hAmeas (measure_ne_top _ _), measure_univ]
      exact tsub_le_iff_right.mpr <|
        by simpa [add_comm] using tsub_le_iff_left.mp hAmass

/-- For [a positive smoothness exponent](hyp:hbeta), [a positive critical
radius](hyp:hdelta), and [the power-balancing regularization
level](hyp:hlambda), [the sum of `delta^2/lambda` and
`lambda^(min beta 1)` equals twice their common power of `delta`](goal).

This is an order-balancing identity, not a claim that this level is the exact
minimizer of a rate bound with arbitrary coefficients. -/
theorem lambda_balance_identity
    {beta delta lambda : ℝ}
    (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hlambda : lambda = delta ^ (2 / (min beta 1 + 1))) :
    delta ^ 2 / lambda + lambda ^ (min beta 1)
      = 2 * delta ^ (2 * min beta 1 / (min beta 1 + 1)) := by
  subst lambda
  let a := min beta 1
  have ha : 0 < a := lt_min hbeta (by norm_num)
  have hden : a + 1 ≠ 0 := by linarith
  have hdelta_nonneg : 0 ≤ delta := hdelta.le
  have hfirst :
      delta ^ 2 / delta ^ (2 / (a + 1))
        = delta ^ (2 * a / (a + 1)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_sub hdelta]
    congr 1
    field_simp [hden]
    ring
  have hsecond :
      (delta ^ (2 / (a + 1))) ^ a
        = delta ^ (2 * a / (a + 1)) := by
    rw [← Real.rpow_mul hdelta_nonneg]
    congr 1
    ring
  rw [show min beta 1 = a by rfl, hfirst, hsecond]
  ring

end Primal
end NPIV
end Estimation
end Causalean

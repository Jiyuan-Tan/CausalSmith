/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.DR.AsymptoticLinear
public import Causalean.Estimation.NPIV.Primal.RateSequence

/-! # Passing the primal NPIV rate to the doubly robust layer

The primal theorem is stated in the `L²(sigma(X))` strong norm. This module
proves its equivalence to an explicit `eLpNorm` convergence statement and
derives that convergence from the primal rate theorem. The current doubly
robust remainder bundle has no nuisance-consistency field.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open Filter MeasureTheory Causalean.Stat Primal

/-- Given [an NPIV operator system](hyp:S), [a sequence of primal nuisance
estimators](hyp:h_hat), and [membership of every fitted nuisance in the primal
candidate space](hyp:hmem), [strong-norm convergence in probability is
equivalent to convergence in the corresponding explicit ambient `L²` metric](goal). -/
theorem primal_l2_consistency_iff_strongNorm
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (S : OperatorSystem Omega mu)
    (h_hat : ℕ → Omega → S.𝒳 → ℝ)
    (hmem : ∀ n omega, h_hat n omega ∈ S.Hbar) :
    Tendsto_inProb
        (fun n omega =>
          S.strongNorm (S.hL2 (hmem n omega) - S.hL2 S.h₀_mem))
        (fun _ => 0) mu
      ↔
    Tendsto_inProb
        (fun n omega =>
          (eLpNorm
            (fun omega' =>
              h_hat n omega (S.xOf (S.W omega'))
                - S.h₀ (S.xOf (S.W omega'))) 2 mu).toReal)
      (fun _ => 0) mu := by
  have hfun :
      (fun n omega =>
        S.strongNorm (S.hL2 (hmem n omega) - S.hL2 S.h₀_mem))
        = fun n omega =>
          (eLpNorm
            (fun omega' =>
              h_hat n omega (S.xOf (S.W omega'))
                - S.h₀ (S.xOf (S.W omega'))) 2 mu).toReal := by
    funext n omega
    exact S.strongNorm_hL2_sub_eq_eLpNorm_toReal
      (hmem n omega) S.h₀_mem
  rw [hfun]

/-- [The fitted primal nuisance converges to the truth in the ambient `L²` metric in
probability](goal) when [an NPIV operator system and its primal TRAE estimator
sequence](hyp:S,is_estimator) satisfy [source smoothness and bias
conditions](hyp:sc,bias,hbeta), [admissible regularization and localized
regimes](hyp:hlambda_pos,hlambda_lt,regimes), [valid confidence levels with critical-radius and
peeling floors](hyp:hzeta_pos,hzeta_lt,floors,peeling), [vanishing confidence and localization
sequences](hyp:hzeta_zero,hdelta_zero), and [vanishing regularization and scaled
variance](hyp:hlambda_zero,hdelta_sq_div_lambda_zero).

This applies `primal_strongNorm_tendstoInProb_of_rates` and then translates
the operator strong norm to the corresponding explicit `L²` norm. -/
theorem primal_l2_consistency_of_rate
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (S : OperatorSystem Omega mu) {TC : TRAEClasses S}
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
        (eLpNorm
          (fun omega' =>
            h_hat n omega (S.xOf (S.W omega'))
              - S.h₀ (S.xOf (S.W omega'))) 2 mu).toReal)
      (fun _ => 0) mu := by
  let hmem : ∀ n omega, h_hat n omega ∈ S.Hbar :=
    fun n omega => TC.H_subset (is_estimator.mem_H n omega)
  have hrate := Primal.primal_strongNorm_tendstoInProb_of_rates
    is_estimator sc bias hbeta hlambda_pos hlambda_lt regimes
    hzeta_pos hzeta_lt floors peeling hzeta_zero hdelta_zero hlambda_zero
    hdelta_sq_div_lambda_zero
  exact (primal_l2_consistency_iff_strongNorm S h_hat hmem).mp <| by
    simpa [hmem] using hrate

end DR
end NPIV
end Estimation
end Causalean

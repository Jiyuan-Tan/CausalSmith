/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPInequality
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Regulariser

/-!
Assembles the localized empirical-process and centered-regularizer events for
the earlier simultaneous-in-sample-size NPIV route.  The current fixed-sample
rate uses `per_sample_empirical_process_event` instead.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Empirical-process event assembly

This file combines the localized empirical-process inequality and the centred
regulariser bound, then exposes the final empirical-process event in the shape
used by the primal NPIV rate theorem. The declarations below are the concrete
event-assembly theorem from the earlier all-`n` construction.  Its right-hand
side retains the critical radii and geometric-union-bound logarithms rather
than absorbing them into the paper's fixed-sample rate. -/

/-- **Discharge of `empirical_process_event` from `localized_uniform_deviation` —
explicit-rate form.** Given [a localized-regime bundle for the weak-norm, regularizer, and
cross function classes at each fold-A sample size](hyp:regimes) and [a nonnegative Tikhonov
regularization weight `lambda`](hyp:lambda_nonneg), [for every confidence level `ζ` strictly
between `0` and `1` there is an event of probability at least `1 − ζ` on which, simultaneously
for every `n` with `1 ≤ split.n₁ n`, the weak-norm estimation excess plus `lambda` times the
strong-norm estimation excess is bounded by the sum of the explicit per-`n` empirical-process
rate and the explicit per-`n` centred-regularizer rate — each an additive combination of
critical radii and a `√(log/n)` deviation term](goal).

Combines the EP inequality and the centred-regulariser bound on a
common high-probability event.  The RHS is the explicit per-`n` sum of
critical-radius and `√(log/n_A)` terms; see
`per_sample_empirical_process_event` supersedes this result for the current
paper-faithful route by assembling the same ingredients directly at one
sample size and one confidence level. -/
theorem empirical_process_event_from_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBoundAt S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    (lambda_nonneg : 0 ≤ lambda) :
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ Aζ : Set Ω,
        MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧
        ∀ ω ∈ Aζ, ∀ n : ℕ, 1 ≤ split.n₁ n →
          (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm
                (S.hL2 tb.h_lambda_star_mem
                  - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                ((S.strongNorm
                      (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                  - (S.strongNorm
                      (S.hL2 tb.h_lambda_star_mem)) ^ 2)
            ≤
              -- D-side raw explicit rate (EP step, before absorption).
              (16 * delta n *
                    criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
                  + 16 * delta n *
                    criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
                  + 8 * delta n *
                    criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
                  + 4 * npivBousquetSlack (regimes n).bundle_HF.regime.b (delta n)
                      (criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n)))
                      (Real.log (8 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n)
                  + 4 * npivBousquetSlack (regimes n).bundle_mF.regime.b (delta n)
                      (criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n)))
                      (Real.log (8 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n)
                  + 2 * npivBousquetSlack (regimes n).bundle_F.regime.b (delta n)
                      (criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n)))
                      (Real.log (8 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n))
            -- C-side rate (centred regulariser).
            + lambda *
                (4 * ((regimes n).H_diameter + delta n) *
                    criticalRadius ((regimes n).bundle_H.regime.ψ (split.n₁ n))
                  + npivBousquetSlack (regimes n).bundle_H.regime.b
                      ((regimes n).H_diameter + delta n)
                      (criticalRadius ((regimes n).bundle_H.regime.ψ (split.n₁ n)))
                      (Real.log ((2 : ℝ) ^ (n + 2) / ζ)) (split.n₁ n)) := by
  -- Proof: combine `ep_inequality_from_localized` (D) and
  -- `centred_regulariser_bound_from_localized` (C) at confidence `ζ/2`
  -- each.  Splitting `ζ → ζ/2` per side doubles the inner argument of
  -- the log: D-side `log(4·2^(n+1)/(ζ/2)) = log(8·2^(n+1)/ζ)`, C-side
  -- `log(2^(n+1)/(ζ/2)) = log(2^(n+2)/ζ)`.  Intersection of the two
  -- events has mass `≥ 1 - ζ/2 - ζ/2 = 1 - ζ`.
  intro ζ hζ_pos hζ_lt
  have hζ_half_pos : 0 < ζ / 2 := by linarith
  have hζ_half_lt : ζ / 2 < 1 := by linarith
  obtain ⟨Aζ_ep, hAζ_ep_meas, hAζ_ep_mass, hAζ_ep_bound⟩ :=
    ep_inequality_from_localized (h_hat := h_hat) (is_estimator := is_estimator)
      sc tb regimes hζ_half_pos hζ_half_lt
  obtain ⟨Aζ_reg, hAζ_reg_meas, hAζ_reg_mass, hAζ_reg_bound⟩ :=
    centred_regulariser_bound_from_localized (h_hat := h_hat)
      (is_estimator := is_estimator) sc tb regimes lambda_nonneg hζ_half_pos
      hζ_half_lt
  refine ⟨Aζ_ep ∩ Aζ_reg, hAζ_ep_meas.inter hAζ_reg_meas, ?_, ?_⟩
  · have hhalf_nonneg : 0 ≤ ζ / 2 := by linarith
    have hmass :=
      measure_inter_ge_one_sub_add_of_ge hAζ_ep_meas hAζ_reg_meas
        hAζ_ep_mass hAζ_reg_mass
    simpa [← ENNReal.ofReal_add hhalf_nonneg hhalf_nonneg, add_halves] using hmass
  · intro ω hω n hn
    rcases hω with ⟨hω_ep, hω_reg⟩
    have hlog_ep : 4 * (2 : ℝ) ^ (n + 1) / (ζ / 2) =
        8 * (2 : ℝ) ^ (n + 1) / ζ := by
      field_simp [ne_of_gt hζ_pos]
      ring
    have hlog_reg : (2 : ℝ) ^ (n + 1) / (ζ / 2) =
        (2 : ℝ) ^ (n + 2) / ζ := by
      field_simp [ne_of_gt hζ_pos]
      rw [pow_succ]
      ring
    have hD := hAζ_ep_bound ω hω_ep n hn
    rw [hlog_ep] at hD
    have hC_abs := hAζ_reg_bound ω hω_reg n hn
    rw [hlog_reg] at hC_abs
    have hC_upper := (le_abs_self _).trans hC_abs
    simp only [npivBousquetSlack] at hD ⊢
    nlinarith [hD, hC_upper]

end Primal
end NPIV
end Estimation
end Causalean

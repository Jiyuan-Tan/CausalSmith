/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EventAssembly

/-! # Fixed-sample NPIV empirical-process event

This module combines the four localized deviation events at one sample-size
index and one confidence level.  It intentionally has no countable
intersection over sample sizes, so its deviation term is
`sqrt (log (4 / zeta) / n)` rather than `sqrt (log (2^n / zeta) / n)`.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A [localized regime](hyp:regime) satisfies the [fixed-confidence critical-radius
floor at level `zeta`](hyp:zeta) when each of the three objective-process envelope terms is
at most the squared localization radius.

This is the standard finite-sample enlargement of a population critical
radius by the bounded-deviation term `b * sqrt(log(4/zeta)/n)`. -/
structure PerSampleConfidenceFloor
    {S : OperatorSystem Omega mu} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲} {sample : IIDSample Omega S.𝒲 mu P_W}
    {beta lambda delta_n : ℝ} {n : ℕ}
    {sc : SourceCondition S beta}
    {tb : TikhonovBiasBoundAt S beta lambda sc}
    (regime : LocalizedRegimes S TC sample sc tb n delta_n)
    (zeta : ℝ) : Prop where
  /-- Confidence floor for the product process. -/
  HF : 2 * Real.sqrt
        ((delta_n ^ 2 + 8 * regime.bundle_HF.regime.b * delta_n *
            criticalRadius (regime.bundle_HF.regime.ψ n)) *
          Real.log (4 / zeta) / n)
      + 8 * regime.bundle_HF.regime.b * Real.log (4 / zeta) / n ≤ delta_n ^ 2
  /-- Confidence floor for the moment process. -/
  mF : 2 * Real.sqrt
        ((delta_n ^ 2 + 8 * regime.bundle_mF.regime.b * delta_n *
            criticalRadius (regime.bundle_mF.regime.ψ n)) *
          Real.log (4 / zeta) / n)
      + 8 * regime.bundle_mF.regime.b * Real.log (4 / zeta) / n ≤ delta_n ^ 2
  /-- Confidence floor for the squared-critic process. -/
  F : 2 * Real.sqrt
        ((delta_n ^ 2 + 8 * regime.bundle_F.regime.b * delta_n *
            criticalRadius (regime.bundle_F.regime.ψ n)) *
          Real.log (4 / zeta) / n)
      + 8 * regime.bundle_F.regime.b * Real.log (4 / zeta) / n ≤ delta_n ^ 2

set_option maxHeartbeats 800000 in
-- The final algebra combines four event bounds with large empirical sums.
/-- Given [a source condition](hyp:sc), [its fixed-level bias certificate](hyp:tb),
[a positive fold size](hyp:hn), [a confidence level strictly between
zero and one](hyp:hzeta_pos,hzeta_lt), [a nonnegative regularization
level](hyp:hlambda), [the localized regime at that one fold size](hyp:regime),
the [fixed-confidence critical-radius floor](hyp:floor), [the peeling floor
at one quarter of that confidence](hyp:peeling), [a sample-size
index](hyp:n), and [a sample-size-dependent TRAE estimator](hyp:is_estimator), [there is an
event of probability at least `1 - zeta` on which the population
strong-convexity right-hand side at index `n` is bounded by `50 * delta n²`
plus the peeled centered-regularizer envelope](goal).

This is the fixed-confidence counterpart of the former simultaneous-in-`n`
construction.  The same event is uniform over candidates and critics, but no
confidence budget is split across sample sizes. -/
theorem per_sample_empirical_process_event
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
    (tb : TikhonovBiasBoundAt S beta (lambda_n n) sc)
    [IsProbabilityMeasure mu]
    (regime :
      LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    (hn : 1 ≤ split.n₁ n)
    {zeta : ℝ} (hzeta_pos : 0 < zeta) (hzeta_lt : zeta < 1)
    (hlambda : 0 ≤ lambda_n n)
    (floor : PerSampleConfidenceFloor regime zeta)
    (peeling : PeelingFloor regime (zeta / 4)) :
    ∃ A : Set Omega,
      MeasurableSet A ∧ mu A ≥ 1 - ENNReal.ofReal zeta ∧
      ∀ omega ∈ A,
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
              - S.hL2 S.h₀_mem)) ^ 2
          - (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
          + lambda_n n *
              ((S.strongNorm
                  (S.hL2 (TC.H_subset (is_estimator.mem_H n omega)))) ^ 2
                - (S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2)
          ≤ 50 * (delta n) ^ 2
              + lambda_n n *
                  (10 * delta n *
                      S.strongNorm
                        (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
                          - S.hL2 tb.h_lambda_star_mem)
                    + 5 * (delta n) ^ 2) := by
  classical
  let eta : ℝ := zeta / 4
  have heta_pos : 0 < eta := by dsimp [eta]; linarith
  have heta_le : eta ≤ 1 := by dsimp [eta]; linarith
  have hn_pos : 0 < split.n₁ n := lt_of_lt_of_le zero_lt_one hn
  obtain ⟨EHF, hEHF_meas, hEHF_mass, hEHF⟩ :=
    localized_omega_event_for_HF regime hn_pos heta_pos heta_le
  obtain ⟨EmF, hEmF_meas, hEmF_mass, hEmF⟩ :=
    localized_omega_event_for_mF regime hn_pos heta_pos heta_le
  obtain ⟨EF, hEF_meas, hEF_mass, hEF⟩ :=
    localized_omega_event_for_F regime hn_pos heta_pos heta_le
  obtain ⟨EH, hEH_meas, hEH_mass, hEH⟩ :=
    localized_omega_event_for_H_pair_peeled
      (regime := regime) hn_pos heta_pos heta_le (by simpa [eta] using peeling)
  let A : Set Omega := ((EHF ∩ EmF) ∩ EF) ∩ EH
  refine ⟨A, ((hEHF_meas.inter hEmF_meas).inter hEF_meas).inter hEH_meas,
    ?_, ?_⟩
  · have h12 := measure_inter_ge_one_sub_add_of_ge hEHF_meas hEmF_meas
      hEHF_mass hEmF_mass
    have h123 := measure_inter_ge_one_sub_add_of_ge
      (hEHF_meas.inter hEmF_meas) hEF_meas h12 hEF_mass
    have h1234 := measure_inter_ge_one_sub_add_of_ge
      ((hEHF_meas.inter hEmF_meas).inter hEF_meas) hEH_meas h123 hEH_mass
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hsum :
        ((ENNReal.ofReal eta + ENNReal.ofReal eta) + ENNReal.ofReal eta)
            + ENNReal.ofReal eta = ENNReal.ofReal zeta := by
      rw [← ENNReal.ofReal_add heta_nonneg heta_nonneg]
      rw [← ENNReal.ofReal_add (add_nonneg heta_nonneg heta_nonneg) heta_nonneg]
      rw [← ENNReal.ofReal_add
        (add_nonneg (add_nonneg heta_nonneg heta_nonneg) heta_nonneg) heta_nonneg]
      congr 1
      dsimp [eta]
      ring
    simpa [A, hsum] using h1234
  · intro omega homega
    rcases homega with ⟨⟨⟨homegaHF, homegamF⟩, homegaF⟩, homegaH⟩
    obtain ⟨f_h, hf_h, hcl_h⟩ :=
      regime.closedness (h_hat n omega) (is_estimator.mem_H n omega)
    obtain ⟨f_star, hf_star, hstar_sup_le_inner⟩ :=
      regime.supObjective_attained split n omega
        tb.h_lambda_star_fun regime.realizability
    have hinner_le_sup :
        innerObjective S sample split (lambda_n n) (h_hat n omega) f_h n omega
          ≤ supObjective S TC sample split (lambda_n n) (h_hat n omega) n omega :=
      regime.inner_le_supObjective split n omega
        (h_hat n omega) (is_estimator.mem_H n omega) f_h hf_h
    have hlog : 1 / eta = 4 / zeta := by
      dsimp [eta]
      field_simp [ne_of_gt hzeta_pos]
    have hHF_h := hEHF omega homegaHF (h_hat n omega)
      (is_estimator.mem_H n omega) f_h hf_h
    have hmF_h := hEmF omega homegamF f_h hf_h
    have hF_h := hEF omega homegaF f_h hf_h
    have hHF_star := hEHF omega homegaHF tb.h_lambda_star_fun
      regime.realizability f_star hf_star
    have hmF_star := hEmF omega homegamF f_star hf_star
    have hF_star := hEF omega homegaF f_star hf_star
    rw [hlog] at hHF_h hmF_h hF_h hHF_star hmF_star hF_star
    let rHF : ℝ :=
      4 * delta n * criticalRadius (regime.bundle_HF.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * regime.bundle_HF.regime.b * delta n *
                criticalRadius (regime.bundle_HF.regime.ψ (split.n₁ n))) *
              Real.log (4 / zeta) / split.n₁ n)
        + 8 * regime.bundle_HF.regime.b * Real.log (4 / zeta) / split.n₁ n
    let rmF : ℝ :=
      4 * delta n * criticalRadius (regime.bundle_mF.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * regime.bundle_mF.regime.b * delta n *
                criticalRadius (regime.bundle_mF.regime.ψ (split.n₁ n))) *
              Real.log (4 / zeta) / split.n₁ n)
        + 8 * regime.bundle_mF.regime.b * Real.log (4 / zeta) / split.n₁ n
    let rF : ℝ :=
      4 * delta n * criticalRadius (regime.bundle_F.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * regime.bundle_F.regime.b * delta n *
                criticalRadius (regime.bundle_F.regime.ψ (split.n₁ n))) *
              Real.log (4 / zeta) / split.n₁ n)
        + 8 * regime.bundle_F.regime.b * Real.log (4 / zeta) / split.n₁ n
    have hupper_h :
        2 * (∫ omega', S.m (S.W omega') f_h ∂mu)
            - 2 * (∫ omega',
                h_hat n omega (S.xOf (S.W omega')) *
                  f_h (S.zOf (S.W omega')) ∂mu)
            - ∫ omega', (f_h (S.zOf (S.W omega'))) ^ 2 ∂mu
            + lambda_n n *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (h_hat n omega (S.xOf (sample.Z (k : ℕ) omega))) ^ 2)
          ≤ innerObjective S sample split (lambda_n n)
              (h_hat n omega) f_h n omega + (2 * rmF + 2 * rHF + rF) := by
      exact population_regularized_le_innerObjective_add_deviation
        split (lambda_n n) (h_hat n omega) f_h n omega hmF_h hHF_h hF_h
    have hupper_star :
        innerObjective S sample split (lambda_n n)
            tb.h_lambda_star_fun f_star n omega
          ≤ 2 * (∫ omega', S.m (S.W omega') f_star ∂mu)
            - 2 * (∫ omega',
                tb.h_lambda_star_fun (S.xOf (S.W omega')) *
                  f_star (S.zOf (S.W omega')) ∂mu)
            - ∫ omega', (f_star (S.zOf (S.W omega'))) ^ 2 ∂mu
            + lambda_n n *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun
                    (S.xOf (sample.Z (k : ℕ) omega))) ^ 2)
            + (2 * rmF + 2 * rHF + rF) := by
      exact innerObjective_le_population_regularized_add_deviation
        split (lambda_n n) tb.h_lambda_star_fun f_star n omega
          hmF_star hHF_star hF_star
    have hpop_h_eq :
        2 * (∫ omega', S.m (S.W omega') f_h ∂mu)
            - 2 * (∫ omega', h_hat n omega (S.xOf (S.W omega')) *
                f_h (S.zOf (S.W omega')) ∂mu)
            - ∫ omega', (f_h (S.zOf (S.W omega'))) ^ 2 ∂mu
          = (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
                - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_eq_closedness_witness
        (hh := is_estimator.mem_H n omega) (hf := hf_h) hcl_h
    have hpop_star_le :
        2 * (∫ omega', S.m (S.W omega') f_star ∂mu)
            - 2 * (∫ omega', tb.h_lambda_star_fun (S.xOf (S.W omega')) *
                f_star (S.zOf (S.W omega')) ∂mu)
            - ∫ omega', (f_star (S.zOf (S.W omega'))) ^ 2 ∂mu
          ≤ (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_le_weak (hh := regime.realizability) (hf := hf_star)
    have hopt := is_estimator.opt n omega tb.h_lambda_star_fun regime.realizability
    have hEP :
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
              - S.hL2 S.h₀_mem)) ^ 2
          - (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
          ≤ lambda_n n *
              ((((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun
                    (S.xOf (sample.Z (k : ℕ) omega))) ^ 2)
                - (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                    ∑ k : Fin (split.n₁ n),
                      (h_hat n omega
                        (S.xOf (sample.Z (k : ℕ) omega))) ^ 2))
            + (4 * rmF + 4 * rHF + 2 * rF) := by
      linarith [hupper_h, hupper_star, hpop_h_eq, hpop_star_le,
        hinner_le_sup, hstar_sup_le_inner, hopt]
    have hHdev := hEH omega homegaH tb.h_lambda_star_fun
      regime.realizability (h_hat n omega) (is_estimator.mem_H n omega)
    have hstar_sq :
        (S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2 =
          ∫ omega', (tb.h_lambda_star_fun (S.xOf (S.W omega'))) ^ 2 ∂mu :=
      S.strongNorm_sq_hL2_eq_integral tb.h_lambda_star_mem
    have hhat_sq :
        (S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n omega)))) ^ 2 =
          ∫ omega', (h_hat n omega (S.xOf (S.W omega'))) ^ 2 ∂mu :=
      S.strongNorm_sq_hL2_eq_integral
        (TC.H_subset (is_estimator.mem_H n omega))
    have hHmul := mul_le_mul_of_nonneg_left hHdev hlambda
    have hnorm_sub :
        S.strongNorm
            (S.hL2 tb.h_lambda_star_mem
              - S.hL2 (TC.H_subset (is_estimator.mem_H n omega)))
          = S.strongNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
                - S.hL2 tb.h_lambda_star_mem) := by
      simp [OperatorSystem.strongNorm, norm_sub_rev]
    rw [hnorm_sub] at hHmul
    have hHabs :
        |lambda_n n *
          (((((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (tb.h_lambda_star_fun
                (S.xOf (sample.Z (k : ℕ) omega))) ^ 2)
            - (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h_hat n omega
                  (S.xOf (sample.Z (k : ℕ) omega))) ^ 2))
            - ((S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2
              - (S.strongNorm
                  (S.hL2 (TC.H_subset
                    (is_estimator.mem_H n omega)))) ^ 2))|
          ≤ lambda_n n *
            (10 * delta n *
                S.strongNorm
                  (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
                    - S.hL2 tb.h_lambda_star_mem)
              + 5 * (delta n) ^ 2) := by
      simpa [abs_mul, abs_of_nonneg hlambda, hstar_sq, hhat_sq, mul_assoc]
        using hHmul
    have hHupper := (le_abs_self _).trans hHabs
    have hdelta_pos : 0 < delta n :=
      lt_of_lt_of_le regime.bundle_HF.crit_pos regime.bundle_HF.crit_le
    have hdelta_nonneg : 0 ≤ delta n := hdelta_pos.le
    have hcrit_HF :
        delta n * criticalRadius (regime.bundle_HF.regime.ψ (split.n₁ n))
          ≤ (delta n) ^ 2 := by
      calc
        _ ≤ delta n * delta n :=
          mul_le_mul_of_nonneg_left regime.bundle_HF.crit_le hdelta_nonneg
        _ = (delta n) ^ 2 := by ring
    have hcrit_mF :
        delta n * criticalRadius (regime.bundle_mF.regime.ψ (split.n₁ n))
          ≤ (delta n) ^ 2 := by
      calc
        _ ≤ delta n * delta n :=
          mul_le_mul_of_nonneg_left regime.bundle_mF.crit_le hdelta_nonneg
        _ = (delta n) ^ 2 := by ring
    have hcrit_F :
        delta n * criticalRadius (regime.bundle_F.regime.ψ (split.n₁ n))
          ≤ (delta n) ^ 2 := by
      calc
        _ ≤ delta n * delta n :=
          mul_le_mul_of_nonneg_left regime.bundle_F.crit_le hdelta_nonneg
        _ = (delta n) ^ 2 := by ring
    have hrHF_le : rHF ≤ 5 * (delta n) ^ 2 := by
      dsimp [rHF]
      linarith [hcrit_HF, floor.HF]
    have hrmF_le : rmF ≤ 5 * (delta n) ^ 2 := by
      dsimp [rmF]
      linarith [hcrit_mF, floor.mF]
    have hrF_le : rF ≤ 5 * (delta n) ^ 2 := by
      dsimp [rF]
      linarith [hcrit_F, floor.F]
    have hEP' :
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n omega))
              - S.hL2 S.h₀_mem)) ^ 2
          - (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
          ≤ lambda_n n *
              ((((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun
                    (S.xOf (sample.Z (k : ℕ) omega))) ^ 2)
                - (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                    ∑ k : Fin (split.n₁ n),
                      (h_hat n omega
                        (S.xOf (sample.Z (k : ℕ) omega))) ^ 2))
            + 50 * (delta n) ^ 2 := by
      linarith [hEP]
    linarith

end Primal
end NPIV
end Estimation
end Causalean

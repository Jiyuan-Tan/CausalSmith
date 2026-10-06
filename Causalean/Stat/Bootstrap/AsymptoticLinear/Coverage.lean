module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Main

/-!
# Asymptotic coverage of the percentile and basic bootstrap intervals

This module proves that, for a bootstrap-asymptotically-linear estimator, the percentile and the
basic bootstrap confidence intervals both cover the target with probability tending to the nominal
level.  Both proofs combine the random-endpoint coverage lemma with conditional quantile
convergence.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}
  {S : IIDSample Omega X mu P}
  {est : (n : ℕ) -> (Fin n -> X) -> ℝ} {theta0 : ℝ} {psi : X -> ℝ}

namespace BootstrapAsymLinear

/-- For [a bootstrap-asymptotically-linear estimator](hyp:h) and [an interior nominal error
level](hyp:halpha0,halpha1), [the percentile bootstrap confidence interval covers the target with
probability tending to one minus that level](goal). -/
theorem percentileCI_coverage (h : BootstrapAsymLinear S est theta0 psi)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n => mu.real {omega |
        theta0 ∈ percentileCI est n alpha (S.sampleVector n omega)})
      atTop (nhds (1 - alpha)) := by
  -- Rewrite target membership as the rescaled sampling statistic lying between the negatives of
  -- the upper/lower bootstrap quantiles.  The random endpoints converge by `quantile_tendsto`;
  -- apply random-endpoint portmanteau and the reflected Gaussian equal-tail mass lemma.
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hvReal : 0 < h.asymptoticVariance := h.var_pos_finite.1
  have hv : 0 < h.asymptoticVariance.toNNReal := by
    rwa [Real.toNNReal_pos]
  let G : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 h.asymptoticVariance.toNNReal, inferInstance⟩
  have hG : h.asymptoticGaussian = G := by
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  let T : ℕ → Omega → ℝ := fun n omega =>
    Real.sqrt (n : ℝ) * (est n (S.sampleVector n omega) - theta0)
  have hx (n : ℕ) : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have hTMeas (n : ℕ) : AEMeasurable (T n) mu := by
    exact (measurable_const.mul
      (((h.meas.1 n).comp (hx n)).sub measurable_const)).aemeasurable
  have hT : Tendsto_dist T (G : Measure ℝ) mu hTMeas := by
    apply (Tendsto_dist_iff _ _ _ hTMeas).2
    have hlaw : (fun n => (⟨mu.map (T n),
        Measure.isProbabilityMeasure_map (hTMeas n)⟩ : ProbabilityMeasure ℝ)) =
        samplingEstimatorLaw S est theta0 h.meas.1 := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      rfl
    rw [hlaw, ← hG]
    exact sampling_tendsto_gaussian h
  have ha2_pos : 0 < alpha / 2 := by linarith
  have ha2_lt_one : alpha / 2 < 1 := by linarith
  have h1a2_pos : 0 < 1 - alpha / 2 := by linarith
  have h1a2_lt_one : 1 - alpha / 2 < 1 := by linarith
  let qlo : ℕ → Omega → ℝ := fun n omega =>
    bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega)
  let qhi : ℕ → Omega → ℝ := fun n omega =>
    bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega)
  let alo := Real.sqrt h.asymptoticVariance * Causalean.Mathlib.probit (alpha / 2)
  let ahi := Real.sqrt h.asymptoticVariance *
    Causalean.Mathlib.probit (1 - alpha / 2)
  have hqloMeas (n : ℕ) : Measurable (qlo n) :=
    (measurable_bootstrapQuantile est h.meas.1 n ha2_pos ha2_lt_one).comp (hx n)
  have hqhiMeas (n : ℕ) : Measurable (qhi n) :=
    (measurable_bootstrapQuantile est h.meas.1 n h1a2_pos h1a2_lt_one).comp (hx n)
  have hqlo : Tendsto_inProb qlo (fun _ => alo) mu :=
    quantile_tendsto h ha2_pos ha2_lt_one
  have hqhi : Tendsto_inProb qhi (fun _ => ahi) mu :=
    quantile_tendsto h h1a2_pos h1a2_lt_one
  have hnegqhi : Tendsto_inProb (fun n omega => -qhi n omega) (fun _ => -ahi) mu := by
    simpa only [neg_zero] using Tendsto_inProb.comp_continuousAt
      (g := fun x : ℝ => -x) continuousAt_neg hqhi
  have hnegqlo : Tendsto_inProb (fun n omega => -qlo n omega) (fun _ => -alo) mu := by
    simpa only [neg_zero] using Tendsto_inProb.comp_continuousAt
      (g := fun x : ℝ => -x) continuousAt_neg hqlo
  have hprobit : Causalean.Mathlib.probit (alpha / 2) ≤
      Causalean.Mathlib.probit (1 - alpha / 2) := by
    apply Causalean.Mathlib.stdNormalCDF_strictMono.le_iff_le.mp
    rw [Causalean.Mathlib.stdNormalCDF_probit ha2_pos ha2_lt_one,
      Causalean.Mathlib.stdNormalCDF_probit h1a2_pos h1a2_lt_one]
    linarith
  have halohi : alo ≤ ahi := by
    dsimp [alo, ahi]
    exact mul_le_mul_of_nonneg_left hprobit (Real.sqrt_nonneg _)
  have hboundary : (G : Measure ℝ) (frontier (Icc (-ahi) (-alo))) = 0 := by
    haveI : NullSingletonClass (G : Measure ℝ) := by
      dsimp [G]
      exact nullSingletonClass_gaussianReal hv.ne'
    rw [frontier_Icc (neg_le_neg halohi)]
    apply le_antisymm
    · calc
        (G : Measure ℝ) ({-ahi, -alo} : Set ℝ) ≤
            (G : Measure ℝ) ({-ahi} : Set ℝ) +
              (G : Measure ℝ) ({-alo} : Set ℝ) := by
              rw [show ({-ahi, -alo} : Set ℝ) = {-ahi} ∪ {-alo} by ext x; simp [or_comm]]
              exact measure_union_le ({-ahi} : Set ℝ) ({-alo} : Set ℝ)
        _ = 0 := by simp only [NullSingletonClass.measure_singleton, add_zero]
    · exact zero_le
  have hcoverage := tendsto_dist_random_Icc_coverage hTMeas hT
    (fun n omega => -qhi n omega) (fun n omega => -qlo n omega)
    (-ahi) (-alo)
    (fun n => (hqhiMeas n).neg) (fun n => (hqloMeas n).neg)
    hnegqhi hnegqlo (neg_le_neg halohi) hboundary
  have hmass : (G : Measure ℝ).real (Icc (-ahi) (-alo)) = 1 - alpha := by
    dsimp [G, alo, ahi]
    simpa only [Real.coe_toNNReal _ hvReal.le] using
      gaussianReal_reflectedQuantile_Icc_toReal hv halpha0 halpha1
  rw [hmass] at hcoverage
  apply hcoverage.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  congr 1
  ext omega
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
  change
    (-qhi n omega ≤ T n omega ∧ T n omega ≤ -qlo n omega) ↔
    (est n (S.sampleVector n omega) + qlo n omega / Real.sqrt (n : ℝ) ≤ theta0 ∧
      theta0 ≤ est n (S.sampleVector n omega) + qhi n omega / Real.sqrt (n : ℝ))
  rw [iff_comm]
  dsimp [T]
  constructor
  · rintro ⟨hlow, hhigh⟩
    constructor
    · have hz : (theta0 - est n (S.sampleVector n omega)) * Real.sqrt (n : ℝ) ≤
          qhi n omega := (le_div_iff₀ hsqrt).mp (by linarith)
      nlinarith
    · have hz : qlo n omega ≤
          (theta0 - est n (S.sampleVector n omega)) * Real.sqrt (n : ℝ) :=
        (div_le_iff₀ hsqrt).mp (by linarith)
      nlinarith
  · rintro ⟨hlow, hhigh⟩
    constructor
    · have hz : qlo n omega / Real.sqrt (n : ℝ) ≤
          theta0 - est n (S.sampleVector n omega) :=
        (div_le_iff₀ hsqrt).mpr (by nlinarith)
      linarith
    · have hz : theta0 - est n (S.sampleVector n omega) ≤
          qhi n omega / Real.sqrt (n : ℝ) :=
        (le_div_iff₀ hsqrt).mpr (by nlinarith)
      linarith

/-- For [a bootstrap-asymptotically-linear estimator](hyp:h) and [an interior nominal error
level](hyp:halpha0,halpha1), [the basic bootstrap confidence interval covers the target with
probability tending to one minus that level](goal). -/
theorem basicCI_coverage (h : BootstrapAsymLinear S est theta0 psi)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n => mu.real {omega |
        theta0 ∈ basicCI est n alpha (S.sampleVector n omega)})
      atTop (nhds (1 - alpha)) := by
  -- Rewrite target membership as the rescaled sampling statistic lying between the lower and
  -- upper bootstrap quantiles.  Apply random-endpoint portmanteau, the sampling CLT, quantile
  -- convergence, and `gaussianReal_quantile_Icc_toReal`.
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hvReal : 0 < h.asymptoticVariance := h.var_pos_finite.1
  have hv : 0 < h.asymptoticVariance.toNNReal := by
    rwa [Real.toNNReal_pos]
  let G : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 h.asymptoticVariance.toNNReal, inferInstance⟩
  have hG : h.asymptoticGaussian = G := by
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  let T : ℕ → Omega → ℝ := fun n omega =>
    Real.sqrt (n : ℝ) * (est n (S.sampleVector n omega) - theta0)
  have hx (n : ℕ) : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have hTMeas (n : ℕ) : AEMeasurable (T n) mu := by
    exact (measurable_const.mul
      (((h.meas.1 n).comp (hx n)).sub measurable_const)).aemeasurable
  have hT : Tendsto_dist T (G : Measure ℝ) mu hTMeas := by
    apply (Tendsto_dist_iff _ _ _ hTMeas).2
    have hlaw : (fun n => (⟨mu.map (T n),
        Measure.isProbabilityMeasure_map (hTMeas n)⟩ : ProbabilityMeasure ℝ)) =
        samplingEstimatorLaw S est theta0 h.meas.1 := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      rfl
    rw [hlaw, ← hG]
    exact sampling_tendsto_gaussian h
  have ha2_pos : 0 < alpha / 2 := by linarith
  have ha2_lt_one : alpha / 2 < 1 := by linarith
  have h1a2_pos : 0 < 1 - alpha / 2 := by linarith
  have h1a2_lt_one : 1 - alpha / 2 < 1 := by linarith
  let qlo : ℕ → Omega → ℝ := fun n omega =>
    bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega)
  let qhi : ℕ → Omega → ℝ := fun n omega =>
    bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega)
  let alo := Real.sqrt h.asymptoticVariance * Causalean.Mathlib.probit (alpha / 2)
  let ahi := Real.sqrt h.asymptoticVariance *
    Causalean.Mathlib.probit (1 - alpha / 2)
  have hqloMeas (n : ℕ) : Measurable (qlo n) :=
    (measurable_bootstrapQuantile est h.meas.1 n ha2_pos ha2_lt_one).comp (hx n)
  have hqhiMeas (n : ℕ) : Measurable (qhi n) :=
    (measurable_bootstrapQuantile est h.meas.1 n h1a2_pos h1a2_lt_one).comp (hx n)
  have hqlo : Tendsto_inProb qlo (fun _ => alo) mu :=
    quantile_tendsto h ha2_pos ha2_lt_one
  have hqhi : Tendsto_inProb qhi (fun _ => ahi) mu :=
    quantile_tendsto h h1a2_pos h1a2_lt_one
  have hprobit : Causalean.Mathlib.probit (alpha / 2) ≤
      Causalean.Mathlib.probit (1 - alpha / 2) := by
    apply Causalean.Mathlib.stdNormalCDF_strictMono.le_iff_le.mp
    rw [Causalean.Mathlib.stdNormalCDF_probit ha2_pos ha2_lt_one,
      Causalean.Mathlib.stdNormalCDF_probit h1a2_pos h1a2_lt_one]
    linarith
  have halohi : alo ≤ ahi := by
    dsimp [alo, ahi]
    exact mul_le_mul_of_nonneg_left hprobit (Real.sqrt_nonneg _)
  have hboundary : (G : Measure ℝ) (frontier (Icc alo ahi)) = 0 := by
    haveI : NullSingletonClass (G : Measure ℝ) := by
      dsimp [G]
      exact nullSingletonClass_gaussianReal hv.ne'
    rw [frontier_Icc halohi]
    apply le_antisymm
    · calc
        (G : Measure ℝ) ({alo, ahi} : Set ℝ) ≤
            (G : Measure ℝ) ({alo} : Set ℝ) +
              (G : Measure ℝ) ({ahi} : Set ℝ) := by
              rw [show ({alo, ahi} : Set ℝ) = {alo} ∪ {ahi} by ext x; simp [or_comm]]
              exact measure_union_le ({alo} : Set ℝ) ({ahi} : Set ℝ)
        _ = 0 := by simp only [NullSingletonClass.measure_singleton, add_zero]
    · exact zero_le
  have hcoverage := tendsto_dist_random_Icc_coverage hTMeas hT qlo qhi alo ahi
    hqloMeas hqhiMeas hqlo hqhi halohi hboundary
  have hmass : (G : Measure ℝ).real (Icc alo ahi) = 1 - alpha := by
    dsimp [G, alo, ahi]
    simpa only [Real.coe_toNNReal _ hvReal.le] using
      gaussianReal_quantile_Icc_toReal hv halpha0 halpha1
  rw [hmass] at hcoverage
  apply hcoverage.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  congr 1
  ext omega
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
  change
    (qlo n omega ≤ T n omega ∧ T n omega ≤ qhi n omega) ↔
    (est n (S.sampleVector n omega) - qhi n omega / Real.sqrt (n : ℝ) ≤ theta0 ∧
      theta0 ≤ est n (S.sampleVector n omega) - qlo n omega / Real.sqrt (n : ℝ))
  rw [iff_comm]
  dsimp [T]
  constructor
  · rintro ⟨hlow, hhigh⟩
    constructor
    · have hz : qlo n omega ≤
          (est n (S.sampleVector n omega) - theta0) * Real.sqrt (n : ℝ) :=
        (div_le_iff₀ hsqrt).mp (by linarith)
      nlinarith
    · have hz : (est n (S.sampleVector n omega) - theta0) * Real.sqrt (n : ℝ) ≤
          qhi n omega := (le_div_iff₀ hsqrt).mp (by linarith)
      nlinarith
  · rintro ⟨hlow, hhigh⟩
    constructor
    · have hz : est n (S.sampleVector n omega) - theta0 ≤
          qhi n omega / Real.sqrt (n : ℝ) :=
        (le_div_iff₀ hsqrt).mpr (by nlinarith)
      linarith
    · have hz : qlo n omega / Real.sqrt (n : ℝ) ≤
          est n (S.sampleVector n omega) - theta0 :=
        (div_le_iff₀ hsqrt).mpr (by nlinarith)
      linarith

end BootstrapAsymLinear

end

end Causalean.Stat

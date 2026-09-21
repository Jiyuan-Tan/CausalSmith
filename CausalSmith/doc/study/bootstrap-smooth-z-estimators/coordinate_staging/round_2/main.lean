module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.BootstrapLinearization

/-!
# Bootstrap validity for smooth finite-dimensional Z-estimators

This module constructs `BootstrapAsymLinear` for every nondegenerate continuous linear contrast
of a smooth finite-dimensional Z-estimator.  It then exposes percentile and basic bootstrap
confidence-interval coverage as direct corollaries of the existing interval API.
-/

public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {mu : Measure Omega} {P : Measure X}

namespace BootstrapAsymLinear

/-- For [an estimating function](hyp:psi), [a target parameter](hyp:theta0), [a population
law](hyp:P), [a smooth Z-estimator regularity package](hyp:reg), [an iid sample](hyp:S), [a
sample-function estimator](hyp:est), [measurability at every sample size](hyp:hEstMeas), [a
continuous linear contrast](hyp:c), [data consistency](hyp:hConsistent), [data
estimating-equation validity](hyp:hSolve), [bootstrap consistency](hyp:hBootConsistent),
[bootstrap estimating-equation validity](hyp:hBootSolve), and [positive contrast influence
variance](hyp:hVar), [the scalar contrast estimator is bootstrap asymptotically linear](goal). -/
theorem zEstimator
    [IsProbabilityMeasure mu]
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hEstMeas : ∀ n, Measurable (est n))
    (c : E →L[ℝ] ℝ)
    (hConsistent : ∀ epsilon > 0,
      Tendsto
        (fun n ↦ mu {omega |
          epsilon < ‖est n (S.sampleVector n omega) - theta0‖})
        atTop (nhds 0))
    (hSolve : SolvesEstimatingEquationInProbability S psi est)
    (hBootConsistent : BootstrapEstimatorConsistent S est theta0)
    (hBootSolve : BootstrapSolvesEstimatingEquationInProbability S psi est)
    (hVar : 0 < ∫ z, (c (reg.jacobianInv (psi theta0 z))) ^ 2 ∂P) :
    Causalean.Stat.BootstrapAsymLinear S
      (fun n x ↦ c (est n x)) (c theta0)
      (fun z ↦ -c (reg.jacobianInv (psi theta0 z))) := by
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let influence : X → ℝ := fun z ↦ -c (reg.jacobianInv (psi theta0 z))
  have hinfluence : influence = fun z ↦ c (reg.influence z) := by
    funext z
    simp [influence, SmoothZEstimatorRegularity.influence]
  have hinfluence_meas : Measurable influence := by
    rw [hinfluence]
    exact c.continuous.measurable.comp reg.influence_measurable
  have hreg_mem : MemLp reg.influence 2 P :=
    (memLp_two_iff_integrable_sq_norm reg.influence_measurable.aestronglyMeasurable).2
      reg.influence_integrable_sq
  have hinfluence_mem : MemLp influence 2 P := by
    rw [hinfluence]
    exact hreg_mem.continuousLinearMap_comp c
  have hreg_int : Integrable reg.influence P := hreg_mem.integrable (by norm_num)
  have hinfluence_mean : ∫ z, influence z ∂P = 0 := by
    rw [hinfluence, c.integral_comp_comm hreg_int]
    unfold SmoothZEstimatorRegularity.influence
    rw [integral_neg, reg.jacobianInv.integral_comp_comm
      ((memLp_two_iff_integrable_sq_norm reg.score_meas.aestronglyMeasurable).2
        reg.score_finite_var |>.integrable (by norm_num)), reg.identification]
    simp
  have hsample_eq : ∀ (n : ℕ) omega,
      Real.sqrt (n : ℝ) *
          (c (est n (S.sampleVector n omega)) - c theta0) -
          IsAsymLinear.normalizedSum S influence (fun m ↦ Finset.range m) n omega =
        c (zEstimatorSamplingRemainder S est theta0 reg.influence n omega) := by
    intro n omega
    simp [zEstimatorSamplingRemainder, IsAsymLinear.normalizedSum,
      IsAsymLinearVec.normalizedSum, hinfluence, map_sub, map_smul, map_sum]
  have hlinear : Tendsto_inProb
      (fun n omega ↦
        Real.sqrt (n : ℝ) *
            (c (est n (S.sampleVector n omega)) - c theta0) -
          IsAsymLinear.normalizedSum S influence (fun m ↦ Finset.range m) n omega)
      (fun _ ↦ 0) mu := by
    have hvec := zEstimator_samplingLinearization
      psi theta0 P reg S est hConsistent hSolve
    unfold Tendsto_inProb at hvec ⊢
    rw [tendstoInMeasure_iff_norm] at hvec ⊢
    intro epsilon hepsilon
    have hscale : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
    have hvec' := hvec (epsilon / (‖c‖ + 1)) (div_pos hepsilon hscale)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvec'
      (fun _ ↦ zero_le) (fun n ↦ measure_mono fun omega homega ↦ ?_)
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at homega ⊢
    rw [hsample_eq] at homega
    have hop : |c (zEstimatorSamplingRemainder S est theta0 reg.influence n omega)| ≤
        ‖c‖ * ‖zEstimatorSamplingRemainder S est theta0 reg.influence n omega‖ := by
      simpa [Real.norm_eq_abs] using
        c.le_opNorm (zEstimatorSamplingRemainder S est theta0 reg.influence n omega)
    have hcnonneg : 0 ≤ ‖c‖ := norm_nonneg c
    have hrnonneg : 0 ≤
        ‖zEstimatorSamplingRemainder S est theta0 reg.influence n omega‖ := norm_nonneg _
    apply (div_le_iff₀ hscale).2
    rw [abs_of_nonneg hrnonneg]
    nlinarith
  have hboot_eq : ∀ n (x xstar : Fin n → X),
      centeredEstimatorBootstrapStatistic (fun m y ↦ c (est m y)) n x xstar -
          centeredBootstrapSum influence x xstar =
        c (zEstimatorBootstrapRemainder est reg.influence n x xstar) := by
    intro n x xstar
    by_cases hn : n = 0
    · subst n
      simp [centeredEstimatorBootstrapStatistic, centeredBootstrapSum,
        zEstimatorBootstrapRemainder, scaledBootstrapMeanDifference]
    · rw [centeredBootstrapSum_eq_sqrt_mul_finAverage_sub hn]
      simp [centeredEstimatorBootstrapStatistic, zEstimatorBootstrapRemainder,
        scaledBootstrapMeanDifference, Causalean.Stat.finMean,
        Causalean.Stat.finAverage, hinfluence, map_sub, map_smul, map_sum]
  have hboot : ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ mu.real {omega |
          epsilon < (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon < abs
              (centeredEstimatorBootstrapStatistic (fun m y ↦ c (est m y)) n
                  (S.sampleVector n omega) xstar -
                centeredBootstrapSum influence
                  (S.sampleVector n omega) xstar)}})
        atTop (nhds 0) := by
    intro epsilon hepsilon
    have hscale : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
    have hvec := zEstimator_bootstrapLinearization
      psi theta0 P reg S est hConsistent hSolve hBootConsistent hBootSolve
      (epsilon / (‖c‖ + 1)) (div_pos hepsilon hscale) epsilon hepsilon
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvec
      (fun _ ↦ by rw [Measure.real_def]; exact ENNReal.toReal_nonneg) (fun n ↦ ?_)
    apply measureReal_mono _ (measure_ne_top _ _)
    intro omega homega
    simp only [Set.mem_setOf_eq] at homega ⊢
    by_cases hn : n = 0
    · subst n
      simp [centeredEstimatorBootstrapStatistic, centeredBootstrapSum,
        not_lt_of_ge hepsilon.le] at homega
    let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
      bootstrapResample_isProbabilityMeasure _ hn
    have hmono :
        (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon <
              |centeredEstimatorBootstrapStatistic (fun m y ↦ c (est m y)) n
                  (S.sampleVector n omega) xstar -
                centeredBootstrapSum influence (S.sampleVector n omega) xstar|} ≤
          (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon / (‖c‖ + 1) <
              ‖zEstimatorBootstrapRemainder est reg.influence n
                  (S.sampleVector n omega) xstar - 0‖} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro xstar hxstar
      simp only [Set.mem_setOf_eq] at hxstar ⊢
      rw [hboot_eq] at hxstar
      have hop : |c (zEstimatorBootstrapRemainder est reg.influence n
          (S.sampleVector n omega) xstar)| ≤
          ‖c‖ * ‖zEstimatorBootstrapRemainder est reg.influence n
            (S.sampleVector n omega) xstar‖ := by
        simpa [Real.norm_eq_abs] using c.le_opNorm
          (zEstimatorBootstrapRemainder est reg.influence n
            (S.sampleVector n omega) xstar)
      have hcnonneg : 0 ≤ ‖c‖ := norm_nonneg c
      have hrnonneg : 0 ≤ ‖zEstimatorBootstrapRemainder est reg.influence n
          (S.sampleVector n omega) xstar‖ := norm_nonneg _
      simp only [sub_zero]
      apply (div_lt_iff₀ hscale).2
      nlinarith
    exact homega.trans_le hmono
  refine ⟨⟨fun n ↦ c.continuous.measurable.comp (hEstMeas n), hinfluence_meas⟩,
    hinfluence_mean, ⟨?_, ?_⟩, hlinear, hboot⟩
  · simpa [influence] using hVar
  · exact (memLp_two_iff_integrable_sq hinfluence_meas.aestronglyMeasurable).1
      hinfluence_mem

/-- For [an estimating function](hyp:psi), [a target parameter](hyp:theta0), [a population
law](hyp:P), [a smooth Z-estimator regularity package](hyp:reg), [an iid sample](hyp:S), [a
measurable sample-function estimator](hyp:est,hEstMeas), [a continuous linear contrast](hyp:c),
[data consistency and estimating-equation validity](hyp:hConsistent,hSolve), [bootstrap
consistency and estimating-equation validity](hyp:hBootConsistent,hBootSolve), [positive contrast
influence variance](hyp:hVar), [a nominal error level](hyp:alpha), and [an interior confidence
level](hyp:halpha0,halpha1), [the percentile interval covers the true contrast with its nominal
asymptotic probability](goal). -/
theorem zEstimator_percentileCI_coverage
    [IsProbabilityMeasure mu]
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hEstMeas : ∀ n, Measurable (est n))
    (c : E →L[ℝ] ℝ)
    (hConsistent : ∀ epsilon > 0,
      Tendsto (fun n ↦ mu {omega |
        epsilon < ‖est n (S.sampleVector n omega) - theta0‖}) atTop (nhds 0))
    (hSolve : SolvesEstimatingEquationInProbability S psi est)
    (hBootConsistent : BootstrapEstimatorConsistent S est theta0)
    (hBootSolve : BootstrapSolvesEstimatingEquationInProbability S psi est)
    (hVar : 0 < ∫ z, (c (reg.jacobianInv (psi theta0 z))) ^ 2 ∂P)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n ↦ mu.real {omega |
        c theta0 ∈ percentileCI (fun m x ↦ c (est m x)) n alpha
          (S.sampleVector n omega)})
      atTop (nhds (1 - alpha)) := by
  -- Proof plan: apply `BootstrapAsymLinear.percentileCI_coverage` to `zEstimator`.
  exact (zEstimator psi theta0 P reg S est hEstMeas c hConsistent hSolve
    hBootConsistent hBootSolve hVar).percentileCI_coverage halpha0 halpha1

/-- For [an estimating function](hyp:psi), [a target parameter](hyp:theta0), [a population
law](hyp:P), [a smooth Z-estimator regularity package](hyp:reg), [an iid sample](hyp:S), [a
measurable sample-function estimator](hyp:est,hEstMeas), [a continuous linear contrast](hyp:c),
[data consistency and estimating-equation validity](hyp:hConsistent,hSolve), [bootstrap
consistency and estimating-equation validity](hyp:hBootConsistent,hBootSolve), [positive contrast
influence variance](hyp:hVar), [a nominal error level](hyp:alpha), and [an interior confidence
level](hyp:halpha0,halpha1), [the basic interval covers the true contrast with its nominal
asymptotic probability](goal). -/
theorem zEstimator_basicCI_coverage
    [IsProbabilityMeasure mu]
    (psi : E → X → E) (theta0 : E) (P : Measure X)
    (reg : SmoothZEstimatorRegularity psi theta0 P)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hEstMeas : ∀ n, Measurable (est n))
    (c : E →L[ℝ] ℝ)
    (hConsistent : ∀ epsilon > 0,
      Tendsto (fun n ↦ mu {omega |
        epsilon < ‖est n (S.sampleVector n omega) - theta0‖}) atTop (nhds 0))
    (hSolve : SolvesEstimatingEquationInProbability S psi est)
    (hBootConsistent : BootstrapEstimatorConsistent S est theta0)
    (hBootSolve : BootstrapSolvesEstimatingEquationInProbability S psi est)
    (hVar : 0 < ∫ z, (c (reg.jacobianInv (psi theta0 z))) ^ 2 ∂P)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n ↦ mu.real {omega |
        c theta0 ∈ basicCI (fun m x ↦ c (est m x)) n alpha
          (S.sampleVector n omega)})
      atTop (nhds (1 - alpha)) := by
  -- Proof plan: apply `BootstrapAsymLinear.basicCI_coverage` to `zEstimator`.
  exact (zEstimator psi theta0 P reg S est hEstMeas c hConsistent hSolve
    hBootConsistent hBootSolve hVar).basicCI_coverage halpha0 halpha1

end BootstrapAsymLinear

end

end Causalean.Stat

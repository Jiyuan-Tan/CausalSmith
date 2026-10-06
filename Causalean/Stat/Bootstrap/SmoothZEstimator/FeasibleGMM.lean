module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Basic
public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMMLinearization

/-!
# Feasible GMM: the bootstrap-asymptotic-linearity constructor

This module turns the feasible-GMM sampling and bootstrap linearizations into the
`BootstrapAsymLinear` bundle for a contrast of the coefficient vector, so the percentile and basic
bootstrap intervals apply to feasible GMM with a general weight matrix.
-/

public section

namespace Causalean.Stat

open ContinuousLinearMap Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators RealInnerProductSpace Topology

noncomputable section

variable {Omega X E F : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
  {mu : Measure Omega} {P : Measure X}

namespace BootstrapAsymLinear

/-- Under [a smooth feasible-GMM problem](hyp:prob,reg), [an iid sample, measurable estimator,
weight estimator, and contrast](hyp:S,est,hEstMeas,weightEst,c), [data and bootstrap consistency
of the parameter and weight](hyp:hConsistent,hWeight,hBootConsistent,hBootWeight), [negligible
data and bootstrap first-order-condition residuals](hyp:hApproxFOC,hBootFOC), and [positive
contrast influence variance](hyp:hVar), [the feasible-GMM contrast is bootstrap asymptotically
linear](goal).  The sampling linearization is supplied by
`feasibleGMM_asymLinear_of_smoothMoment_of_sampleFn`. -/
theorem feasibleGMM
    [IsProbabilityMeasure mu]
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob)
    (S : IIDSample Omega X mu P)
    (est : (n : ℕ) → (Fin n → X) → E)
    (hEstMeas : ∀ n, Measurable (est n))
    (weightEst : (n : ℕ) → (Fin n → X) → (F →L[ℝ] F))
    (c : E →L[ℝ] ℝ)
    (hConsistent : ∀ epsilon > 0,
      Tendsto (fun n ↦ mu {omega |
        epsilon < ‖est n (S.sampleVector n omega) - prob.θ₀‖}) atTop (nhds 0))
    (hWeight : Tendsto_inProb
      (fun n omega ↦ ‖weightEst n (S.sampleVector n omega) - prob.W‖)
      (fun _ ↦ 0) mu)
    (hApproxFOC : IsLittleOp
      (fun n omega ↦ ‖feasibleGMMFOCResidualFn prob reg
        (est n (S.sampleVector n omega))
        (weightEst n (S.sampleVector n omega)) (S.sampleVector n omega)‖)
      (fun _ ↦ (1 : ℝ)) mu)
    (hBootConsistent : BootstrapEstimatorConsistent S est prob.θ₀)
    (hBootWeight : BootstrapTendstoInProbability S
      (fun n _ xstar ↦ weightEst n xstar) (fun _ _ ↦ prob.W))
    (hBootFOC : BootstrapTendstoInProbability S
      (fun n _ xstar ↦ feasibleGMMFOCResidualFn prob reg
        (est n xstar) (weightEst n xstar) xstar)
      (fun _ _ ↦ 0))
    (hVar : 0 < ∫ z, (c (prob.influence z)) ^ 2 ∂P) :
    BootstrapAsymLinear S
      (fun n data ↦ c (est n data)) (c prob.θ₀)
      (fun z ↦ c (prob.influence z)) := by
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let influence : X → ℝ := fun z ↦ c (prob.influence z)
  have hinfluence_meas : Measurable influence :=
    c.continuous.measurable.comp prob.influence_measurable
  have hprob_mem : MemLp prob.influence 2 P :=
    (memLp_two_iff_integrable_sq_norm prob.influence_measurable.aestronglyMeasurable).2
      prob.influence_integrable_sq
  have hinfluence_mem : MemLp influence 2 P :=
    hprob_mem.continuousLinearMap_comp c
  have hprob_int : Integrable prob.influence P := hprob_mem.integrable (by norm_num)
  have hinfluence_mean : ∫ z, influence z ∂P = 0 := by
    rw [c.integral_comp_comm hprob_int]
    unfold GMMProblem.influence gmmIF
    rw [integral_neg, prob.breadInv.integral_comp_comm
      ((adjoint prob.G).integrable_comp
        (prob.W.integrable_comp
          ((memLp_two_iff_integrable_sq_norm prob.g_meas.aestronglyMeasurable).2
            prob.finite_var |>.integrable (by norm_num)))),
      (adjoint prob.G).integral_comp_comm
        (prob.W.integrable_comp
          ((memLp_two_iff_integrable_sq_norm prob.g_meas.aestronglyMeasurable).2
            prob.finite_var |>.integrable (by norm_num))),
      prob.W.integral_comp_comm
        ((memLp_two_iff_integrable_sq_norm prob.g_meas.aestronglyMeasurable).2
          prob.finite_var |>.integrable (by norm_num)), prob.identification]
    simp
  have hsample_eq : ∀ (n : ℕ) omega,
      Real.sqrt (n : ℝ) *
          (c (est n (S.sampleVector n omega)) - c prob.θ₀) -
          IsAsymLinear.normalizedSum S influence (fun m ↦ Finset.range m) n omega =
        c (zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega) := by
    intro n omega
    simp [zEstimatorSamplingRemainder, IsAsymLinear.normalizedSum,
      IsAsymLinearVec.normalizedSum, influence, map_sub, map_smul, map_sum]
  have hlinear : Tendsto_inProb
      (fun n omega ↦
        Real.sqrt (n : ℝ) *
            (c (est n (S.sampleVector n omega)) - c prob.θ₀) -
          IsAsymLinear.normalizedSum S influence (fun m ↦ Finset.range m) n omega)
      (fun _ ↦ 0) mu := by
    have hjac (n : ℕ) (omega : Omega) :
        gmmSampleJacobianFn reg (est n (S.sampleVector n omega))
            (S.sampleVector n omega) =
          gmmSampleJacobian reg S (est n (S.sampleVector n omega)) n omega := by
      unfold gmmSampleJacobianFn gmmSampleJacobian finMean
        IIDSample.sampleVector
      rw [Fin.sum_univ_eq_sum_range
        (fun i ↦ reg.deriv (est n (fun i ↦ S.Z i omega)) (S.Z i omega)) n]
    have hmom (n : ℕ) (omega : Omega) :
        gmmNormalizedMomentFn prob (est n (S.sampleVector n omega))
            (S.sampleVector n omega) =
          gmmNormalizedMoment S prob.g (est n (S.sampleVector n omega)) n omega := by
      unfold gmmNormalizedMomentFn gmmNormalizedMoment IIDSample.sampleVector
      rw [Fin.sum_univ_eq_sum_range
        (fun i ↦ prob.g (est n (fun i ↦ S.Z i omega)) (S.Z i omega)) n]
    have hAL := feasibleGMM_asymLinear_of_smoothMoment_of_sampleFn
      prob reg S est (fun n omega ↦ weightEst n (S.sampleVector n omega))
      hConsistent hWeight (by
        simpa only [feasibleGMMFOCResidualFn, hjac, hmom] using hApproxFOC)
    have hvec : Tendsto_inProb
        (fun n omega ↦
          ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖)
        (fun _ ↦ 0) mu := by
      rw [Tendsto_inProb_iff_hub,
        Modes.tendstoInProbability_zero_iff_isLittleOpF_one]
      simpa [IsLittleOp, zEstimatorSamplingRemainder,
        IsAsymLinearVec.normalizedSum] using hAL.remainder
    rw [Tendsto_inProb_iff] at hvec ⊢
    rw [tendstoInMeasure_iff_norm] at hvec ⊢
    intro epsilon hepsilon
    have hscale : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
    have hvec' := hvec (epsilon / (‖c‖ + 1)) (div_pos hepsilon hscale)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvec'
      (fun _ ↦ zero_le) (fun n ↦ measure_mono fun omega homega ↦ ?_)
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at homega ⊢
    rw [hsample_eq] at homega
    have hop : |c (zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega)| ≤
        ‖c‖ * ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖ := by
      simpa [Real.norm_eq_abs] using
        c.le_opNorm (zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega)
    have hcnonneg : 0 ≤ ‖c‖ := norm_nonneg c
    have hrnonneg : 0 ≤
        ‖zEstimatorSamplingRemainder S est prob.θ₀ prob.influence n omega‖ := norm_nonneg _
    apply (div_le_iff₀ hscale).2
    rw [abs_of_nonneg hrnonneg]
    nlinarith
  have hboot_eq : ∀ n (x xstar : Fin n → X),
      centeredEstimatorBootstrapStatistic (fun m y ↦ c (est m y)) n x xstar -
          centeredBootstrapSum influence x xstar =
        c (zEstimatorBootstrapRemainder est prob.influence n x xstar) := by
    intro n x xstar
    by_cases hn : n = 0
    · subst n
      simp [centeredEstimatorBootstrapStatistic, centeredBootstrapSum,
        zEstimatorBootstrapRemainder, scaledBootstrapMeanDifference]
    · rw [centeredBootstrapSum_eq_sqrt_mul_finAverage_sub hn]
      simp [centeredEstimatorBootstrapStatistic, zEstimatorBootstrapRemainder,
        scaledBootstrapMeanDifference, finMean,
        finMean, influence, map_sub, map_smul, map_sum]
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
    have hvec := feasibleGMM_bootstrapLinearization_of_smoothMoment
      prob reg S est weightEst hConsistent hWeight hApproxFOC hBootConsistent
      hBootWeight hBootFOC (epsilon / (‖c‖ + 1)) (div_pos hepsilon hscale)
      epsilon hepsilon
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
              ‖zEstimatorBootstrapRemainder est prob.influence n
                  (S.sampleVector n omega) xstar - 0‖} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro xstar hxstar
      simp only [Set.mem_setOf_eq] at hxstar ⊢
      rw [hboot_eq] at hxstar
      have hop : |c (zEstimatorBootstrapRemainder est prob.influence n
          (S.sampleVector n omega) xstar)| ≤
          ‖c‖ * ‖zEstimatorBootstrapRemainder est prob.influence n
            (S.sampleVector n omega) xstar‖ := by
        simpa [Real.norm_eq_abs] using c.le_opNorm
          (zEstimatorBootstrapRemainder est prob.influence n
            (S.sampleVector n omega) xstar)
      have hcnonneg : 0 ≤ ‖c‖ := norm_nonneg c
      have hrnonneg : 0 ≤ ‖zEstimatorBootstrapRemainder est prob.influence n
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

end BootstrapAsymLinear

end

end Causalean.Stat

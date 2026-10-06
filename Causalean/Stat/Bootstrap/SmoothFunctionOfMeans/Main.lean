module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Coverage
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Linearization
public import Causalean.Stat.Inference.RatioDeltaMethod

/-!
# Bootstrap validity for smooth functions of sample means

This module packages the sampling and conditional bootstrap delta expansions into the
`BootstrapAsymLinear` interface.  It supplies the user-facing percentile-interval corollary and
the ratio of two sample moments as a worked specialization.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}

namespace BootstrapAsymLinear

/-- **Smooth-function-of-means constructor.** For [an iid sample](hyp:S), a [measurable
finite-dimensional moment function with integrable squared norm](hyp:g,hg,hg2), a [measurable
scalar transform differentiable at the population moment](hyp:h,hh,Dh,hderiv), and a [strictly
positive influence-function second moment](hyp:hvar), [the transformed sample mean is bootstrap
asymptotically linear with derivative-applied centered moment as influence function](goal). -/
theorem smoothFunctionOfMeans
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h)
    (Dh : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hderiv : HasFDerivAt h Dh (∫ x, g x ∂P))
    (hvar : 0 < ∫ x, (Dh (g x - ∫ y, g y ∂P)) ^ 2 ∂P) :
    BootstrapAsymLinear S (smoothMeanEstimator g h) (h (∫ x, g x ∂P))
      (fun x ↦ Dh (g x - ∫ y, g y ∂P)) := by
  let _ : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hg_mem : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2
  have hg_int : Integrable g P := hg_mem.integrable (by norm_num)
  have hcentered_mem : MemLp (fun x ↦ g x - ∫ y, g y ∂P) 2 P :=
    hg_mem.sub (memLp_const _)
  have hcentered_int : Integrable (fun x ↦ g x - ∫ y, g y ∂P) P :=
    hcentered_mem.integrable (by norm_num)
  have hpsi_mem : MemLp (fun x ↦ Dh (g x - ∫ y, g y ∂P)) 2 P :=
    hcentered_mem.continuousLinearMap_comp Dh
  have hpsi_meas : Measurable (fun x ↦ Dh (g x - ∫ y, g y ∂P)) :=
    Dh.continuous.measurable.comp (hg.sub measurable_const)
  refine ⟨⟨fun n ↦ measurable_smoothMeanEstimator hg hh n, hpsi_meas⟩, ?_,
    ⟨hvar, (memLp_two_iff_integrable_sq hpsi_meas.aestronglyMeasurable).1 hpsi_mem⟩,
    samplingLinearization_smoothFunctionOfMeans S g hg hg2 h Dh hderiv,
    bootstrapLinearization_smoothFunctionOfMeans S g hg hg2 h Dh hderiv⟩
  rw [Dh.integral_comp_comm hcentered_int]
  rw [integral_sub hg_int (integrable_const _)]
  simp

/-- Under [the smooth-function-of-means assumptions](hyp:S,g,hg,hg2,h,hh,Dh,hderiv,hvar) and
an [interior nominal error level](hyp:halpha0,halpha1), [the percentile bootstrap interval has
asymptotic coverage one minus that level](goal). -/
theorem percentileCI_coverage_smoothFunctionOfMeans
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h)
    (Dh : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hderiv : HasFDerivAt h Dh (∫ x, g x ∂P))
    (hvar : 0 < ∫ x, (Dh (g x - ∫ y, g y ∂P)) ^ 2 ∂P)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n ↦ mu.real {omega |
        h (∫ x, g x ∂P) ∈
          percentileCI (smoothMeanEstimator g h) n alpha (S.sampleVector n omega)})
      atTop (𝓝 (1 - alpha)) := by
  exact (smoothFunctionOfMeans S g hg hg2 h hh Dh hderiv hvar).percentileCI_coverage
    halpha0 halpha1

/-- At [a bivariate population moment with nonzero denominator](hyp:m,hm), [the coordinate-ratio
map is Fréchet differentiable](goal). -/
theorem coordinateRatio_hasFDerivAt
    (m : EuclideanSpace ℝ (Fin 2)) (hm : m 1 ≠ 0) :
    HasFDerivAt coordinateRatio (fderiv ℝ coordinateRatio m) m := by
  unfold coordinateRatio
  have hratio := hasFDerivAt_ratio hm
  rw [hratio.fderiv]
  exact hratio

/-- At [a bivariate population moment with nonzero denominator](hyp:m,hm), [the derivative of the
coordinate ratio applied to a displacement](hyp:v) [is the usual quotient-rule expression](goal). -/
theorem fderiv_coordinateRatio_apply
    (m v : EuclideanSpace ℝ (Fin 2)) (hm : m 1 ≠ 0) :
    fderiv ℝ coordinateRatio m v =
      v 0 / m 1 - m 0 * v 1 / (m 1) ^ 2 := by
  have hratio := hasFDerivAt_ratio hm
  change fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0 / z 1) m v = _
  rw [hratio.fderiv]
  simp only [ratioDeriv, sub_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj, smul_eq_mul]
  ring_nf

/-- **Ratio-of-means instance.** For [an iid sample](hyp:S), a [measurable square-integrable
bivariate moment](hyp:g,hg,hg2), a [nonzero population denominator](hyp:hden), and a [strictly
positive ratio-influence second moment](hyp:hvar), [the ratio of the two sample moments is
bootstrap asymptotically linear with the quotient-rule influence function](goal). -/
theorem ratioOfMeans
    (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin 2)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (hden : (∫ x, g x ∂P) 1 ≠ 0)
    (hvar : 0 < ∫ x, (ratioInfluence g (∫ y, g y ∂P) x) ^ 2 ∂P) :
    BootstrapAsymLinear S (ratioOfMeansEstimator g)
      ((∫ x, g x ∂P) 0 / (∫ x, g x ∂P) 1)
      (ratioInfluence g (∫ y, g y ∂P)) := by
  have hratio_meas : Measurable coordinateRatio := by
    unfold coordinateRatio
    exact Measurable.fun_div
      (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable
      (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.measurable
  have hpsi_eq :
      (fun x ↦ fderiv ℝ coordinateRatio (∫ y, g y ∂P)
        (g x - ∫ y, g y ∂P)) =
        ratioInfluence g (∫ y, g y ∂P) := by
    funext x
    rw [fderiv_coordinateRatio_apply (∫ y, g y ∂P) _ hden]
    simp [ratioInfluence]
  have hvar' : 0 < ∫ x, (fderiv ℝ coordinateRatio (∫ y, g y ∂P)
      (g x - ∫ y, g y ∂P)) ^ 2 ∂P := by
    have hpsi_eq_apply (x : X) :
        fderiv ℝ coordinateRatio (∫ y, g y ∂P) (g x - ∫ y, g y ∂P) =
          ratioInfluence g (∫ y, g y ∂P) x := congrFun hpsi_eq x
    simpa only [hpsi_eq_apply] using hvar
  have hsmooth := smoothFunctionOfMeans S g hg hg2 coordinateRatio hratio_meas
    (fderiv ℝ coordinateRatio (∫ x, g x ∂P))
    (coordinateRatio_hasFDerivAt (∫ x, g x ∂P) hden) hvar'
  have hest_eq : ratioOfMeansEstimator g = smoothMeanEstimator g coordinateRatio := by
    funext n x
    exact ratioOfMeansEstimator_eq_smoothMeanEstimator g n x
  rw [hest_eq]
  simpa only [coordinateRatio, hpsi_eq] using hsmooth

end BootstrapAsymLinear

end

end Causalean.Stat

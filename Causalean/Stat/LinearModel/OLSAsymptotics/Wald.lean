/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Inference.Studentize
public import Causalean.Stat.LinearModel.OLSAsymptotics.AsymptoticNormality

/-! # Heteroskedasticity-robust OLS contrasts and Wald inference

This module projects the vector OLS central limit theorem onto a fixed linear
contrast, combines it with HC0 consistency, and proves the standard robust
t-statistic limit and two-sided Wald-interval coverage.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section

variable {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population Gram
matrix](hyp:hQ), for [a contrast vector](hyp:c), [the projected OLS Gaussian
limit is the centered scalar Gaussian with variance `c′Vc`](goal). -/
theorem olsGaussianLimit_contrast_map [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K) :
    let reg := olsSmoothZRegularity hx hy hraw hQ
    (gaussianLimit reg.influence_measurable reg.influence_integrable_sq).map
      (innerSL ℝ c) =
      gaussianMeasure 0 (olsContrastVariance (olsAsymptoticCovariance P x y) c) := by
  dsimp only
  letI : IsGaussian
      (gaussianMeasure 0 (olsContrastVariance (olsAsymptoticCovariance P x y) c)) := by
    unfold gaussianMeasure
    infer_instance
  have hvar_nonneg :
      0 ≤ olsContrastVariance (olsAsymptoticCovariance P x y) c := by
    rw [← olsGaussianLimit_contrastVariance hx hy hraw hQ]
    exact covarianceBilin_self_nonneg c
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    calc
      ∫ z, (innerSL ℝ c) z ∂gaussianLimit
          (olsSmoothZRegularity hx hy hraw hQ).influence_measurable
          (olsSmoothZRegularity hx hy hraw hQ).influence_integrable_sq =
          (innerSL ℝ c) (∫ z, z ∂gaussianLimit
            (olsSmoothZRegularity hx hy hraw hQ).influence_measurable
            (olsSmoothZRegularity hx hy hraw hQ).influence_integrable_sq) :=
        ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_id
      _ = 0 := by rw [gaussianLimit_mean]; simp
      _ = ∫ z, z ∂gaussianMeasure 0
          (olsContrastVariance (olsAsymptoticCovariance P x y) c) := by
        simp [gaussianMeasure]
  · ext
    rw [covarianceBilin_map IsGaussian.memLp_two_id]
    rw [covarianceBilin_real]
    simp only [gaussianMeasure, variance_id_gaussianReal,
      Real.coe_toNNReal', hvar_nonneg, max_eq_left]
    rw [olsGaussianLimit_contrastVariance hx hy hraw hQ]
    simp [ContinuousLinearMap.adjoint_innerSL_apply,
      ContinuousLinearMap.toSpanSingleton_apply]

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
the [root-sample-size rescaled contrast error](goal) is
`√n (c′β̂ₙ-c′β)`. -/
def olsContrastRescaled
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (n : ℝ) *
    (inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
the [HC0 standard error for the rescaled contrast](goal) is `√(c′V̂c)`. -/
def olsHC0ContrastSE
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (olsContrastVariance (olsHC0 S x y n ω) c)

private def olsHC0Studentized
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  olsContrastRescaled S x y c n ω / olsHC0ContrastSE S x y c n ω

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
the [heteroskedasticity-robust t-statistic](goal) is
`(c′β̂ₙ-c′β)/√(c′V̂c/n)`. -/
def olsHC0TStatistic
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  (inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y)) /
    Real.sqrt (olsContrastVariance (olsHC0 S x y n ω) c / (n : ℝ))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), [a sample size](hyp:n), and
[a sample outcome](hyp:ω), the [HC0 Wald half-width](goal) is
`z√(c′V̂c/n)`. -/
def olsHC0WaldRadius
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  z * Real.sqrt (olsContrastVariance (olsHC0 S x y n ω) c / (n : ℝ))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), [a sample size](hyp:n), and
[a sample outcome](hyp:ω), the [two-sided HC0 Wald interval covers the
population contrast](goal) exactly when `c′β` lies between
`c′β̂ₙ ± z√(c′V̂c/n)`. -/
def olsHC0WaldCovers
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  inner ℝ c (olsBeta P x y) ∈ Set.Icc
    (inner ℝ c (olsBetaHat S x y n ω) - olsHC0WaldRadius S x y c z n ω)
    (inner ℝ c (olsBetaHat S x y n ω) + olsHC0WaldRadius S x y c z n ω)

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), and [a sample size](hyp:n),
the [true coverage probability of the two-sided HC0 Wald interval](goal) is
the sampling probability that `c′β` lies between its two endpoints. -/
def olsHC0WaldCoverageProbability
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) : ℝ :=
  μ.real {ω | olsHC0WaldCovers S x y c z n ω}

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), and [a sample
size](hyp:n), the [rescaled contrast error is almost-everywhere
measurable](goal). -/
theorem aemeasurable_olsContrastRescaled
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    AEMeasurable (olsContrastRescaled S x y c n) μ := by
  change AEMeasurable (fun ω => Real.sqrt (n : ℝ) *
    (inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y))) μ
  exact ((((innerSL ℝ c).measurable.comp
      (measurable_olsBetaHat S hx hy n)).sub
        (measurable_const : Measurable (fun _ : Ω => inner ℝ c (olsBeta P x y)))).const_mul
          (Real.sqrt (n : ℝ))).aemeasurable

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), and [a sample
size](hyp:n), [the HC0 contrast-variance estimate is measurable](goal). -/
@[fun_prop]
theorem measurable_olsHC0Contrast
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    Measurable (fun ω => olsContrastVariance (olsHC0 S x y n ω) c) := by
  letI : MeasurableSpace (Matrix K K ℝ) := MeasurableSpace.pi
  letI : BorelSpace (Matrix K K ℝ) := ⟨by
    change MeasurableSpace.pi = borel (K → K → ℝ)
    exact BorelSpace.measurable_eq⟩
  have hM := S.measurable_sampleMeanVec (measurable_olsRawMoment hx hy) n
  have hQ : Measurable (fun ω => olsQHat S x y n ω) := by
    unfold olsQHat olsQFromMoments olsEmpiricalMoments
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply _).comp hM
  have hInv : Measurable (fun ω => (olsQHat S x y n ω)⁻¹) := by
    rw [show (fun ω => (olsQHat S x y n ω)⁻¹) =
      (fun ω => Ring.inverse (Matrix.det (olsQHat S x y n ω)) •
        Matrix.adjugate (olsQHat S x y n ω)) by
          funext ω
          exact Matrix.inv_def _]
    change Measurable
      ((fun ω => Ring.inverse (Matrix.det (olsQHat S x y n ω))) •
        (fun ω => Matrix.adjugate (olsQHat S x y n ω)))
    simpa [Function.comp_def] using
      (measurable_inv.comp (continuous_id.matrix_det.measurable.comp hQ)).smul
        (continuous_id.matrix_adjugate.measurable.comp hQ)
  have hBeta := measurable_olsBetaHat S hx hy n
  have hMeat : Measurable (fun ω => olsHC0Meat S x y n ω) := by
    unfold olsHC0Meat olsMeatFromMoments olsEmpiricalMoments
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => by
      fun_prop
  have hHC0 : Measurable (olsHC0 S x y n) := by
    change Measurable (fun ω i j => ∑ k,
      (∑ l, (olsQHat S x y n ω)⁻¹ i l * olsHC0Meat S x y n ω l k) *
        (olsQHat S x y n ω)⁻¹ k j)
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      Finset.measurable_sum _ fun k _ =>
        (Finset.measurable_sum _ fun l _ =>
          ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hInv)).mul
            ((measurable_pi_apply k).comp ((measurable_pi_apply l).comp hMeat))).mul
          ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hInv))
  change Measurable (fun ω => ∑ i, ∑ j,
    c i * olsHC0 S x y n ω i j * c j)
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (measurable_const.mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hHC0))).mul
        measurable_const

private theorem aemeasurable_olsHC0Studentized
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    AEMeasurable (olsHC0Studentized S x y c n) μ := by
  apply AEMeasurable.div
  · exact aemeasurable_olsContrastRescaled S hx hy c n
  · exact (Real.continuous_sqrt.measurable.comp
      (measurable_olsHC0Contrast S hx hy c n)).aemeasurable

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), and [a sample
size](hyp:n), the [HC0 t-statistic is measurable](goal). -/
theorem measurable_olsHC0TStatistic
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    Measurable (olsHC0TStatistic S x y c n) := by
  apply Measurable.div
  · exact ((innerSL ℝ c).measurable.comp
      (measurable_olsBetaHat S hx hy n)).sub
        (measurable_const : Measurable (fun _ : Ω => inner ℝ c (olsBeta P x y)))
  · exact (Real.continuous_sqrt.measurable.comp
      ((measurable_olsHC0Contrast S hx hy c n).div_const (n : ℝ)))

private theorem measurableSet_olsHC0WaldCovers
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K)
    (z : ℝ) (n : ℕ) :
    MeasurableSet {ω | olsHC0WaldCovers S x y c z n ω} := by
  have hest : Measurable (fun ω => inner ℝ c (olsBetaHat S x y n ω)) :=
    (innerSL ℝ c).measurable.comp (measurable_olsBetaHat S hx hy n)
  have hrad : Measurable (olsHC0WaldRadius S x y c z n) := by
    exact (Real.continuous_sqrt.measurable.comp
      ((measurable_olsHC0Contrast S hx hy c n).div_const (n : ℝ))).const_mul z
  exact (measurableSet_le (hest.sub hrad) measurable_const).inter
    (measurableSet_le measurable_const (hest.add hrad))

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), and [a positive-definite population Gram
matrix](hyp:hQ), for [a contrast vector](hyp:c), [the root-sample-size error
converges in distribution to `N(0,c′Vc)`](goal). -/
theorem olsContrast_tendsto_normal [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K) :
    Tendsto_dist (olsContrastRescaled S x y c)
      (gaussianMeasure 0 (olsContrastVariance (olsAsymptoticCovariance P x y) c)) μ
      (aemeasurable_olsContrastRescaled S hx hy c) := by
  let reg := olsSmoothZRegularity hx hy hraw hQ
  have hvec := olsBetaHat_tendsto_normal S hx hy hraw hQ
  have hvec' := (Tendsto_dist_vec_iff _ _ _
    (aemeasurable_ols_rescaled S hx hy)).2 hvec
  have hmap := Tendsto_dist_vec.map_continuous (innerSL ℝ c).continuous
    (aemeasurable_ols_rescaled S hx hy) hvec'
  have hmap_eq :
      (gaussianLimit reg.influence_measurable reg.influence_integrable_sq).map
        (innerSL ℝ c) =
        gaussianMeasure 0
          (olsContrastVariance (olsAsymptoticCovariance P x y) c) := by
    simpa [reg] using olsGaussianLimit_contrast_map hx hy hraw hQ c
  have hpm_eq :
      (⟨(gaussianLimit reg.influence_measurable reg.influence_integrable_sq).map
          (innerSL ℝ c),
        Measure.isProbabilityMeasure_map
          (innerSL ℝ c).continuous.measurable.aemeasurable⟩ : ProbabilityMeasure ℝ) =
      ⟨gaussianMeasure 0
          (olsContrastVariance (olsAsymptoticCovariance P x y) c), inferInstance⟩ := by
    apply Subtype.ext
    exact hmap_eq
  rw [hpm_eq] at hmap
  apply (Tendsto_dist_iff _ _ _ _).2
  refine hmap.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  apply Measure.map_congr
  filter_upwards with ω
  simp [olsContrastRescaled, IsAsymLinearVec.rescaledEstimator,
    innerSL_apply_apply, inner_sub_right, smul_eq_mul]

private theorem olsHC0Studentized_tendsto [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c) :
    Tendsto_dist (olsHC0Studentized S x y c) (gaussianMeasure 0 1) μ
      (aemeasurable_olsHC0Studentized S hx hy c) := by
  let v := olsContrastVariance (olsAsymptoticCovariance P x y) c
  let σ := Real.sqrt v
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hpos
  have hσsq : σ ^ 2 = v := Real.sq_sqrt hpos.le
  have hnum : Tendsto_dist (olsContrastRescaled S x y c)
      (gaussianMeasure 0 (σ ^ 2)) μ
      (aemeasurable_olsContrastRescaled S hx hy c) := by
    rw [hσsq]
    exact olsContrast_tendsto_normal S hx hy hraw hQ c
  have hse : Tendsto_inProb (olsHC0ContrastSE S x y c) (fun _ => σ) μ := by
    exact tendstoInMeasure_comp_continuousAt_const Real.continuous_sqrt.continuousAt
      (olsHC0_contrast_tendsto_inProb S hx hy hraw hQ c)
  exact Tendsto_dist.div_tendsto_inProb_gaussian hσpos
    (aemeasurable_olsContrastRescaled S hx hy c) hnum hse
    (aemeasurable_olsHC0Studentized S hx hy c)

private theorem olsHC0TStatistic_eq_studentized
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    olsHC0TStatistic S x y c n ω = olsHC0Studentized S x y c n ω := by
  let v := olsContrastVariance (olsHC0 S x y n ω) c
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases hv : 0 ≤ v
  · rw [olsHC0TStatistic, olsHC0Studentized, olsContrastRescaled,
      olsHC0ContrastSE]
    rw [Real.sqrt_div hv]
    have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
    field_simp
    ring
  · have hv' : v ≤ 0 := le_of_not_ge hv
    simp [olsHC0TStatistic, olsHC0Studentized, olsContrastRescaled,
      olsHC0ContrastSE, v, Real.sqrt_eq_zero_of_nonpos hv',
      Real.sqrt_eq_zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg hv' hnR.le)]

private theorem olsHC0WaldCovers_iff_statistic
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hv : 0 < olsContrastVariance (olsHC0 S x y n ω) c) :
    olsHC0WaldCovers S x y c z n ω ↔
      olsHC0TStatistic S x y c n ω ∈ Set.Icc (-z) z := by
  let d := inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y)
  let s := Real.sqrt (olsContrastVariance (olsHC0 S x y n ω) c / (n : ℝ))
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hv hnR)
  change (inner ℝ c (olsBetaHat S x y n ω) - z * s ≤ inner ℝ c (olsBeta P x y) ∧
      inner ℝ c (olsBeta P x y) ≤ inner ℝ c (olsBetaHat S x y n ω) + z * s) ↔
    -z ≤ d / s ∧ d / s ≤ z
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · rw [le_div_iff₀ hs]
      dsimp [d]
      linarith
    · rw [div_le_iff₀ hs]
      dsimp [d]
      linarith
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hs] at hl
    rw [div_le_iff₀ hs] at hu
    dsimp [d] at hl hu
    constructor <;> linarith

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram
matrix](hyp:hQ), [a contrast vector](hyp:c), and [a nondegenerate contrast
variance](hyp:hpos), [the HC0 t-statistic converges in distribution to the
standard normal law](goal). -/
theorem olsHC0TStatistic_tendsto_normal [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c) :
    Tendsto_dist (olsHC0TStatistic S x y c) (gaussianMeasure 0 1) μ
      (fun n => (measurable_olsHC0TStatistic S hx hy c n).aemeasurable) := by
  have hstud : Tendsto_dist (olsHC0Studentized S x y c) (gaussianMeasure 0 1) μ
      (aemeasurable_olsHC0Studentized S hx hy c) :=
    olsHC0Studentized_tendsto S hx hy hraw hQ c hpos
  apply Tendsto_dist.congr_ae
    (aemeasurable_olsHC0Studentized S hx hy c)
    (fun n => (measurable_olsHC0TStatistic S hx hy c n).aemeasurable) hstud
  filter_upwards [eventually_gt_atTop 0] with n hn
  filter_upwards with ω
  exact (olsHC0TStatistic_eq_studentized S x y c hn ω).symm

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram
matrix](hyp:hQ), [a contrast](hyp:c) with [positive asymptotic
variance](hyp:hpos), and [a positive critical value](hyp:hz), the [coverage
probability of the HC0 interval `c′β̂ₙ ± z√(c′V̂c/n)`](goal) converges to
the standard-normal probability of `[-z,z]`. -/
theorem olsHC0_wald_coverage [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c)
    {z : ℝ} (hz : 0 < z) :
    Tendsto (olsHC0WaldCoverageProbability S x y c z) atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  let f : ℕ → Ω → ℝ := fun n ω => olsContrastVariance (olsHC0 S x y n ω) c
  let v : ℝ := olsContrastVariance (olsAsymptoticCovariance P x y) c
  let A : ℕ → Set Ω := fun n => {ω | olsHC0WaldCovers S x y c z n ω}
  let B : ℕ → Set Ω := fun n => {ω | olsHC0TStatistic S x y c n ω ∈ Set.Icc (-z) z}
  let D : ℕ → Set Ω := fun n => {ω | f n ω ≤ 0}
  have hf : TendstoInMeasure μ f atTop (fun _ => v) :=
    olsHC0_contrast_tendsto_inProb S hx hy hraw hQ c
  have herr : Tendsto (fun n => μ.real {ω | v ≤ ‖f n ω - v‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_norm.mp hf) v hpos
  have hD_le : ∀ n, μ.real (D n) ≤ μ.real {ω | v ≤ ‖f n ω - v‖} := by
    intro n
    apply measureReal_mono
    · intro ω hω
      change v ≤ ‖f n ω - v‖
      rw [Real.norm_eq_abs, abs_of_nonpos]
      · change f n ω ≤ 0 at hω
        change 0 < v at hpos
        linarith
      · exact sub_nonpos.mpr (hω.trans hpos.le)
    · exact measure_ne_top _ _
  have hD : Tendsto (fun n => μ.real (D n)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun n => measureReal_nonneg)
      (Eventually.of_forall hD_le)
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_olsHC0WaldCovers S hx hy c z n
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_Icc.preimage
      (measurable_olsHC0TStatistic S hx hy c n)
  have hsymm : ∀ᶠ n in atTop, symmDiff (A n) (B n) ⊆ D n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro ω hω
    rw [Set.mem_symmDiff] at hω
    by_contra hnot
    have hvhat : 0 < f n ω := lt_of_not_ge hnot
    have heq := olsHC0WaldCovers_iff_statistic S x y c z hn ω hvhat
    rcases hω with ⟨ha, hnb⟩ | ⟨hb, hna⟩
    · exact hnb (heq.mp ha)
    · exact hna (heq.mpr hb)
  have hgap_abs : Tendsto
      (fun n => |olsHC0WaldCoverageProbability S x y c z n - μ.real (B n)|)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD
    · exact Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [hsymm] with n hn
      calc
        |olsHC0WaldCoverageProbability S x y c z n - μ.real (B n)| =
            |μ.real (A n) - μ.real (B n)| := by rfl
        _ ≤ μ.real (symmDiff (A n) (B n)) :=
          abs_measureReal_sub_le_measureReal_symmDiff (hA n).nullMeasurableSet
            (hB n).nullMeasurableSet
        _ ≤ μ.real (D n) := measureReal_mono hn (measure_ne_top _ _)
  have hbridge : Tendsto
      (fun n => olsHC0WaldCoverageProbability S x y c z n - μ.real (B n))
      atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hgap_abs
  have hstat : Tendsto_dist (olsHC0TStatistic S x y c) (gaussianMeasure 0 1) μ
      (fun n => (measurable_olsHC0TStatistic S hx hy c n).aemeasurable) :=
    olsHC0TStatistic_tendsto_normal S hx hy hraw hQ c hpos
  exact Tendsto_dist.wald_coverage
    (fun n => (measurable_olsHC0TStatistic S hx hy c n).aemeasurable) hstat hz
    (olsHC0WaldCoverageProbability S x y c z)
    (by simpa [B, measureReal_def] using hbridge)

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram
matrix](hyp:hQ), [a contrast](hyp:c) with [positive asymptotic
variance](hyp:hpos), [a positive critical value](hyp:hz), and [the
calibration that its standard-normal central probability is `1-α`](hyp:hcal),
the [HC0 Wald interval has asymptotic coverage `1-α`](goal). -/
theorem olsHC0_wald_coverage_one_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c)
    {α z : ℝ} (hz : 0 < z)
    (hcal : ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal = 1 - α) :
    Tendsto (olsHC0WaldCoverageProbability S x y c z) atTop (𝓝 (1 - α)) := by
  rw [← hcal]
  exact olsHC0_wald_coverage S hx hy hraw hQ c hpos hz

end

end Causalean.Stat

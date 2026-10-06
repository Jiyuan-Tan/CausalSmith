/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.OLSAsymptotics.Score

/-! # Asymptotic normality of heteroskedastic OLS

This module proves that the data-defined OLS estimator is an exact empirical
score root whenever its sample Gram matrix is nonsingular.  The vector weak
law makes the exceptional singular event asymptotically negligible, so the
smooth-score Z-estimator theorem yields the heteroskedastic OLS central limit
theorem without assuming a CLT or an asymptotic-linear expansion.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal

noncomputable section

variable {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), and [a sample size](hyp:n), the [data-defined OLS
coefficient is measurable](goal). -/
@[fun_prop]
theorem measurable_olsBetaHat
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (n : ℕ) :
    Measurable (olsBetaHat S x y n) := by
  letI : MeasurableSpace (Matrix K K ℝ) := MeasurableSpace.pi
  letI : BorelSpace (Matrix K K ℝ) := ⟨by
    change MeasurableSpace.pi = borel (K → K → ℝ)
    exact BorelSpace.measurable_eq⟩
  have hM := S.measurable_sampleMeanVec (measurable_olsRawMoment hx hy) n
  have hQ : Measurable
      (fun ω => olsQFromMoments (olsEmpiricalMoments S x y n ω)) := by
    unfold olsQFromMoments
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply _).comp hM
  have hR : Measurable
      (fun ω => olsRFromMoments (olsEmpiricalMoments S x y n ω)) := by
    unfold olsRFromMoments
    exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hM
  have hInv : Measurable
      (fun ω => (olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹) := by
    rw [show (fun ω =>
        (olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹) =
      (fun ω => Ring.inverse (Matrix.det (olsQFromMoments
        (olsEmpiricalMoments S x y n ω))) •
          Matrix.adjugate (olsQFromMoments (olsEmpiricalMoments S x y n ω))) by
        funext ω
        exact Matrix.inv_def _]
    change Measurable ((fun ω => Ring.inverse (Matrix.det (olsQFromMoments
      (olsEmpiricalMoments S x y n ω)))) •
        (fun ω => Matrix.adjugate
          (olsQFromMoments (olsEmpiricalMoments S x y n ω))))
    simpa [Function.comp_def] using
      (measurable_inv.comp (continuous_id.matrix_det.measurable.comp hQ)).smul
        (continuous_id.matrix_adjugate.measurable.comp hQ)
  have hV : Measurable (fun ω =>
      (olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹ *ᵥ
        olsRFromMoments (olsEmpiricalMoments S x y n ω)) := by
    unfold Matrix.mulVec dotProduct
    exact measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hInv)).mul
        ((measurable_pi_apply j).comp hR)
  unfold olsBetaHat olsBetaFromMoments
  rw [show (fun ω =>
      (olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹.toEuclideanLin
        (WithLp.toLp 2 (olsRFromMoments (olsEmpiricalMoments S x y n ω)))) =
    (fun ω => WithLp.toLp 2
      ((olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹ *ᵥ
        olsRFromMoments (olsEmpiricalMoments S x y n ω))) by
      funext ω
      rw [Matrix.toEuclideanLin_apply]]
  exact (PiLp.continuous_toLp (2 : ℝ≥0∞) (fun _ : K => ℝ)).measurable.comp hV

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a coefficient](hyp:b), [a sample size](hyp:n), and [a sample
outcome](hyp:ω), the [empirical OLS score average equals `R̂-Q̂b`](goal). -/
theorem ols_sampleMean_score
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (n : ℕ) (ω : Ω) (b : EuclideanSpace ℝ K) :
    (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, olsScore x y b (S.Z t ω) =
      WithLp.toLp 2 (olsRHat S x y n ω -
        olsQHat S x y n ω *ᵥ b.ofLp) := by
  ext i
  simp only [PiLp.smul_apply, Finset.sum_apply, olsScore, olsResidual,
    PiLp.smul_apply, olsRHat, olsQHat, olsEmpiricalMoments,
    IIDSample.sampleMeanVec, olsRFromMoments, olsQFromMoments, olsRawMoment,
    Fin.prod_univ_four, olsMomentIndex, olsAugmented, Matrix.mulVec,
    dotProduct, Pi.sub_apply]
  simp [smul_eq_mul, olsRawMoment, Fin.prod_univ_four, olsMomentIndex,
    olsAugmented]
  have hpoint : ∀ t ∈ Finset.range n,
      (y (S.Z t ω) - ∑ j, x (S.Z t ω) j * b j) * x (S.Z t ω) i =
        x (S.Z t ω) i * y (S.Z t ω) -
          ∑ j, (x (S.Z t ω) i * x (S.Z t ω) j) * b j := by
    intro t _
    have hdist : (∑ j, x (S.Z t ω) j * b j) * x (S.Z t ω) i =
        ∑ j, (x (S.Z t ω) j * b j) * x (S.Z t ω) i :=
      map_sum (AddMonoidHom.mulRight (x (S.Z t ω) i)) _ Finset.univ
    rw [sub_mul, hdist]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, mul_sub]
  congr 1
  rw [Finset.sum_comm]
  have hout : (n : ℝ)⁻¹ *
      ∑ j, ∑ t ∈ Finset.range n,
        (x (S.Z t ω) i * x (S.Z t ω) j) * b j =
      ∑ j, (n : ℝ)⁻¹ * (∑ t ∈ Finset.range n,
        (x (S.Z t ω) i * x (S.Z t ω) j) * b j) :=
    map_sum (AddMonoidHom.mulLeft (n : ℝ)⁻¹) _ Finset.univ
  rw [hout]
  apply Finset.sum_congr rfl
  intro j _
  have hinner : (∑ t ∈ Finset.range n,
      (x (S.Z t ω) i * x (S.Z t ω) j) * b j) =
      (∑ t ∈ Finset.range n, x (S.Z t ω) i * x (S.Z t ω) j) * b j :=
    (map_sum (AddMonoidHom.mulRight (b j)) _ (Finset.range n)).symm
  rw [hinner]
  ring

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), [a sample outcome](hyp:ω), and [a nonsingular sample
Gram matrix](hyp:hdet), the [OLS coefficient solves the sample normal
equations](goal). -/
theorem ols_normalEquation
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (n : ℕ) (ω : Ω) (hdet : (olsQHat S x y n ω).det ≠ 0) :
    olsQHat S x y n ω *ᵥ (olsBetaHat S x y n ω).ofLp =
      olsRHat S x y n ω := by
  have hu : IsUnit (olsQHat S x y n ω).det := isUnit_iff_ne_zero.mpr hdet
  rw [olsBetaHat, olsBetaFromMoments, Matrix.toEuclideanLin_apply]
  change olsQHat S x y n ω *ᵥ
      ((olsQFromMoments (olsEmpiricalMoments S x y n ω))⁻¹ *ᵥ
        olsRFromMoments (olsEmpiricalMoments S x y n ω)) = _
  rw [Matrix.mulVec_mulVec]
  change (olsQHat S x y n ω * (olsQHat S x y n ω)⁻¹) *ᵥ
    olsRHat S x y n ω = olsRHat S x y n ω
  rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), and [a positive-definite population Gram
matrix](hyp:hQ), the [probability that the sample Gram matrix is singular
converges to zero](goal). -/
theorem olsQHat_singular_probability_tendsto_zero [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    Tendsto (fun n => μ {ω | (olsQHat S x y n ω).det = 0}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let M₀ := olsPopulationMoments P x y
  let d := (olsQFromMoments M₀).det
  have hd : d ≠ 0 := by
    have hu : IsUnit (olsQ P x y) := hQ.isUnit
    have hudet : IsUnit (olsQ P x y).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hu
    simpa [d, M₀, olsQ] using hudet.ne_zero
  have hM := S.sampleMeanVec_tendstoInMeasure
    (measurable_olsRawMoment hx hy)
    hraw
  have hcont : Continuous
      (fun M : OLSMoment K => (olsQFromMoments M).det) :=
    continuous_id.matrix_det.comp
      (continuous_pi fun i => continuous_pi fun j => continuous_apply _)
  have hdet := tendstoInMeasure_comp_continuousAt_const hcont.continuousAt hM
  rw [tendstoInMeasure_iff_dist] at hdet
  have heps : 0 < |d| / 2 := div_pos (abs_pos.mpr hd) (by norm_num)
  have ht := hdet (|d| / 2) heps
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hsing
  have hdist : |d| / 2 ≤ dist (olsQHat S x y n ω).det d := by
    rw [hsing, dist_zero_left]
    exact (half_lt_self (abs_pos.mpr hd)).le
  simpa [d, M₀, olsQHat, olsEmpiricalMoments, olsPopulationMoments] using hdist

private theorem ols_normalized_score_zero
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (n : ℕ) (ω : Ω) (hn : n ≠ 0)
    (hdet : (olsQHat S x y n ω).det ≠ 0) :
    (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n,
      olsScore x y (olsBetaHat S x y n ω) (S.Z t ω) = 0 := by
  have havg : (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
      olsScore x y (olsBetaHat S x y n ω) (S.Z t ω) = 0 := by
    rw [ols_sampleMean_score, ols_normalEquation S n ω hdet]
    simp
  have hsum : ∑ t ∈ Finset.range n,
      olsScore x y (olsBetaHat S x y n ω) (S.Z t ω) = 0 := by
    have hcast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h := congrArg (fun v : EuclideanSpace ℝ K => (n : ℝ) • v) havg
    simpa [smul_smul, hcast] using h
  rw [hsum, smul_zero]

private theorem ols_score_residual_isLittleOp [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ t ∈ Finset.range n,
          olsScore x y (olsBetaHat S x y n ω) (S.Z t ω)‖)
      (fun _ => (1 : ℝ)) μ := by
  have hsing := olsQHat_singular_probability_tendsto_zero
    S hx hy hraw hQ
  apply (Modes.isLittleOpF_iff_strict _ _ _ _
    (Eventually.of_forall fun _ => zero_lt_one)).2
  intro ε hε
  have hbound : ∀ n : ℕ,
      μ {ω | ε * (1 : ℝ) <
        |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n,
          olsScore x y (olsBetaHat S x y n ω) (S.Z t ω)‖|} ≤
      μ {ω | (olsQHat S x y n ω).det = 0} := by
    intro n
    apply measure_mono
    intro ω hω
    by_cases hn : n = 0
    · subst n
      simp at hω
      exact False.elim ((not_lt_of_ge hε.le) hω)
    by_contra hdet
    simp only [Set.mem_setOf_eq] at hω hdet
    have hz := ols_normalized_score_zero S n ω hn hdet
    rw [hz, norm_zero, abs_zero, mul_one] at hω
    exact (not_lt_of_ge hε.le) hω
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsing
    (fun _ => zero_le)
  exact hbound

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), and [a sample size](hyp:n), the [root-sample-size
rescaled OLS estimation error is almost-everywhere measurable](goal). -/
theorem aemeasurable_ols_rescaled
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (n : ℕ) :
    AEMeasurable
      (IsAsymLinearVec.rescaledEstimator (olsBetaHat S x y)
        (olsBeta P x y) (fun m => Finset.range m) n) μ := by
  unfold IsAsymLinearVec.rescaledEstimator
  exact (((measurable_olsBetaHat S hx hy n).sub measurable_const).const_smul
    (Real.sqrt ((Finset.range n).card : ℝ))).aemeasurable

/-- **Heteroskedastic OLS central limit theorem.** Under [iid
sampling](hyp:S), [measurable regressors](hyp:hx), [a measurable
outcome](hyp:hy), [integrable OLS raw moments through degree four](hyp:hraw), and [a
positive-definite population Gram matrix](hyp:hQ), the [law of
`√n(β̂ₙ-β)` converges to the centered Gaussian generated by the OLS score
influence function](goal). -/
theorem olsBetaHat_tendsto_normal [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    let reg := olsSmoothZRegularity hx hy hraw hQ
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ K))
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator (olsBetaHat S x y)
          (olsBeta P x y) (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map
          (aemeasurable_ols_rescaled S hx hy n)⟩)
      atTop
      (𝓝 ⟨gaussianLimit reg.influence_measurable reg.influence_integrable_sq,
        inferInstance⟩) := by
  dsimp only
  exact zEstimator_tendsto_normal_of_smoothScore
    (olsScore x y) (olsBeta P x y) P
    (olsSmoothZRegularity hx hy hraw hQ) S (olsBetaHat S x y)
    (olsBetaHat_consistent S hx hy hraw hQ)
    (ols_score_residual_isLittleOp S hx hy hraw hQ)
    (aemeasurable_ols_rescaled S hx hy)

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite design second
moment](hyp:hQ), for [coordinates `(i,j)`](hyp:i,j), [the covariance of the
Gaussian limit in `olsBetaHat_tendsto_normal` is the corresponding entry of
`V = Q⁻¹ΩQ⁻¹`](goal). -/
theorem olsGaussianLimit_covariance [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (i j : K) :
    let reg := olsSmoothZRegularity hx hy hraw hQ
    covarianceBilin
      (gaussianLimit reg.influence_measurable reg.influence_integrable_sq)
      (WithLp.toLp 2 (Pi.single i 1))
      (WithLp.toLp 2 (Pi.single j 1)) =
      olsAsymptoticCovariance P x y i j := by
  dsimp only
  rw [gaussianLimit_covarianceBilin]
  rw [olsSmoothZRegularity_influence_eq hx hy hraw hQ]
  convert olsInfluence_secondMoment hx hy hraw hQ i j using 1
  apply integral_congr_ae
  filter_upwards with z
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.single_apply]

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite design second
moment](hyp:hQ), the Gaussian limit variance of [the linear contrast
`c'β`](hyp:c) is [`c'Vc`](goal). -/
theorem olsGaussianLimit_contrastVariance [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K) :
    let reg := olsSmoothZRegularity hx hy hraw hQ
    covarianceBilin
      (gaussianLimit reg.influence_measurable reg.influence_integrable_sq) c c =
      olsContrastVariance (olsAsymptoticCovariance P x y) c := by
  dsimp only
  let e : K → EuclideanSpace ℝ K := fun i => WithLp.toLp 2 (Pi.single i 1)
  have hc : c = ∑ i, c i • e i := by
    ext k
    simp [e, Pi.single_apply]
  conv_lhs => rw [hc]
  simp_rw [map_sum, map_smul]
  simp only [smul_eq_mul]
  have hcov (i j : K) :
      covarianceBilin
        (gaussianLimit
          (olsSmoothZRegularity hx hy hraw hQ).influence_measurable
          (olsSmoothZRegularity hx hy hraw hQ).influence_integrable_sq)
        (e i) (e j) = olsAsymptoticCovariance P x y i j := by
    simpa [e] using olsGaussianLimit_covariance hx hy hraw hQ i j
  simp only [olsContrastVariance]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.sum_apply]
  simp_rw [_root_.smul_apply]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcov j i]
  ring

end

end Causalean.Stat

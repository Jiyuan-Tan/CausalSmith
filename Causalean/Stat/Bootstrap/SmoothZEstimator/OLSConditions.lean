/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Uniformization
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.WeakLawVector
public import Causalean.Stat.Bootstrap.SmoothZEstimator.OLS

/-!
# OLS bootstrap validity from population moments alone

The generic constructor in `SmoothZEstimator.OLS` asks the user for two bootstrap-side
hypotheses: that the resampled coefficient is consistent, and that it solves its own normal
equations, both in conditional probability.  This module discharges them from measurability,
integrability of every augmented regressor/outcome monomial through degree four, and a
positive-definite population Gram matrix, so that bootstrap asymptotic linearity and
percentile-interval coverage follow with no resampling-side assumptions at all.

Two deterministic facts carry the argument: the closed-form coefficient map is continuous wherever
the Gram matrix is nonsingular, and on any finite data set with nonsingular Gram matrix the
closed-form estimator satisfies the empirical score equation exactly.  A bootstrap weak law for
the raw moment vector then places the resample inside the neighbourhood where both apply.
-/

public section

namespace Causalean.Stat

open Filter Matrix MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {Omega X K : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [Fintype K] [DecidableEq K]
  {mu : Measure Omega} {P : Measure X}

/-! ### Deterministic ingredients

These two facts are pure finite-dimensional linear algebra: no measure, no sampling.  Being
deterministic is what lets them be applied to every resample at once, inside a conditional
probability. -/

/-- At [a raw-moment vector whose extracted Gram matrix is nonsingular](hyp:M,hdet), [the
closed-form OLS coefficient depends continuously on the raw moments](goal).

Matrix inversion is continuous at a unit, and the moment vector enters the coefficient only
through coordinate projections, one inversion, and a matrix-vector product. -/
theorem continuousAt_olsBetaFromMoments
    (M : OLSMoment K) (hdet : (olsQFromMoments M).det ≠ 0) :
    ContinuousAt (olsBetaFromMoments : OLSMoment K → EuclideanSpace ℝ K) M := by
  have hQ : Continuous (fun N : OLSMoment K => olsQFromMoments N) := by
    unfold olsQFromMoments
    exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
  have hR : Continuous (fun N : OLSMoment K => olsRFromMoments N) := by
    unfold olsRFromMoments
    exact continuous_pi fun i => continuous_apply _
  have hinv : ContinuousAt (fun N : OLSMoment K => (olsQFromMoments N)⁻¹) M := by
    apply (continuousAt_matrix_inv (olsQFromMoments M)
      (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))).comp
    exact hQ.continuousAt
  unfold olsBetaFromMoments
  change ContinuousAt (fun N => WithLp.toLp 2
    ((olsQFromMoments N)⁻¹ *ᵥ olsRFromMoments N)) M
  have hmul : Continuous
      (fun p : Matrix K K ℝ × (K → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : K => ℝ)).continuousAt.comp
    (hmul.continuousAt.comp (hinv.prodMk hR.continuousAt))

omit [MeasurableSpace X] in
/-- For [regressors and an outcome](hyp:x,y), [a finite data set](hyp:n,data), and [a nonsingular
empirical Gram matrix](hyp:hdet), [the closed-form sample OLS estimator satisfies its empirical
score equation exactly](goal) — not approximately, and with no probabilistic qualifier.

The empirical score at a coefficient is the residual moment `R̂ - Q̂ b`, which the closed-form
estimator annihilates by definition of the inverse. -/
theorem olsSampleEstimator_score_eq_zero_of_det_ne_zero
    (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (data : Fin n → X)
    (hdet : (olsQFromMoments
      (finMean (fun i ↦ olsRawMoment x y (data i)))).det ≠ 0) :
    zEstimatorSampleScore (olsScore x y)
      (olsSampleEstimator x y n data) data = 0 := by
  let M : OLSMoment K := finMean (fun i ↦ olsRawMoment x y (data i))
  have hscore (b : EuclideanSpace ℝ K) :
      zEstimatorSampleScore (olsScore x y) b data =
        WithLp.toLp 2 (olsRFromMoments M - olsQFromMoments M *ᵥ b.ofLp) := by
    ext i
    simp only [zEstimatorSampleScore, finMean, PiLp.smul_apply, olsScore,
      olsResidual, olsRFromMoments, olsQFromMoments, M, Matrix.mulVec,
      dotProduct, Pi.sub_apply]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, olsRawMoment, Fin.prod_univ_four,
      olsMomentIndex, olsAugmented, mul_one]
    have hpoint : ∀ t ∈ Finset.univ,
        (y (data t) - ∑ j, x (data t) j * b j) * x (data t) i =
          x (data t) i * y (data t) -
            ∑ j, (x (data t) i * x (data t) j) * b j := by
      intro t _
      have hdist : (∑ j, x (data t) j * b j) * x (data t) i =
          ∑ j, (x (data t) j * b j) * x (data t) i :=
        map_sum (AddMonoidHom.mulRight (x (data t) i)) _ Finset.univ
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
        ∑ j, ∑ t, (x (data t) i * x (data t) j) * b j =
        ∑ j, (n : ℝ)⁻¹ * (∑ t,
          (x (data t) i * x (data t) j) * b j) :=
      map_sum (AddMonoidHom.mulLeft (n : ℝ)⁻¹) _ Finset.univ
    rw [hout]
    apply Finset.sum_congr rfl
    intro j _
    have hinner : (∑ t,
        (x (data t) i * x (data t) j) * b j) =
        (∑ t, x (data t) i * x (data t) j) * b j :=
      (map_sum (AddMonoidHom.mulRight (b j)) _ Finset.univ).symm
    rw [hinner]
    ring
  have hu : IsUnit (olsQFromMoments M).det := by
    apply isUnit_iff_ne_zero.mpr
    exact hdet
  have hnormal :
      olsQFromMoments M *ᵥ (olsSampleEstimator x y n data).ofLp =
        olsRFromMoments M := by
    unfold olsSampleEstimator olsBetaFromMoments
    change olsQFromMoments M *ᵥ
      ((olsQFromMoments M)⁻¹ *ᵥ olsRFromMoments M) = olsRFromMoments M
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  rw [hscore, hnormal, sub_self]
  rfl

/-! ### Conditional convergence of the resampled moments -/

omit [DecidableEq K] in
/-- Under [iid sampling](hyp:S), [measurable regressors and outcome](hyp:x,y,hx,hy), and
[integrable raw OLS moments](hyp:hraw), [the raw-moment vector of an Efron resample converges to
the population raw-moment vector in bootstrap probability, itself in sampling probability](goal).

This is the finite-dimensional bootstrap weak law for the raw moments, stated in the nested form
that the smooth Z-estimator hypotheses consume.  The raw-moment coordinate type is transported to
a `Fin` type so the vector-valued weak law applies, and the resulting conditional probability is
measurable in the sample. -/
theorem olsRawMoment_bootstrap_tendstoInProbability
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
      Tendsto
        (fun n ↦ mu.real {omega |
          delta < (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon <
              ‖finMean (fun i ↦ olsRawMoment x y (xstar i)) -
                olsPopulationMoments P x y‖}})
        atTop (nhds 0) := by
  classical
  intro epsilon hepsilon delta hdelta
  let e := toEuclidean (E := OLSMoment K)
  let T := e.toContinuousLinearMap
  let g : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ (OLSMoment K))) :=
    fun z ↦ e (olsRawMoment x y z)
  have hg : Measurable g :=
    e.continuous.measurable.comp (measurable_olsRawMoment hx hy)
  have hg_int : Integrable g P := T.integrable_comp hraw
  have hint : (∫ z, g z ∂P) = e (olsPopulationMoments P x y) := by
    simpa [g, T, olsPopulationMoments] using T.integral_comp_comm hraw
  have hmean (n : ℕ) (xstar : Fin n → X) :
      finMean (fun i ↦ g (xstar i)) =
        e (finMean (fun i ↦ olsRawMoment x y (xstar i))) := by
    simp [g, finMean]
  let q : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | epsilon <
        ‖finMean (fun i ↦ olsRawMoment x y (xstar i)) -
          olsPopulationMoments P x y‖}
  have hq_meas (n : ℕ) : Measurable (q n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) :=
      {z | epsilon <
        ‖finMean (fun i ↦ olsRawMoment x y (z.2 i)) -
          olsPopulationMoments P x y‖}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold finMean
      fun_prop
    have hsamp : Measurable (fun omega ↦ S.sampleVector n omega) := by
      apply measurable_pi_iff.mpr
      intro i
      exact S.meas i
    change Measurable ((fun data : Fin n → X ↦
      (bootstrapResample data).real {xstar | (data, xstar) ∈ A}) ∘
        fun omega ↦ S.sampleVector n omega)
    exact (measurable_bootstrapResample_real_of_measurableSet A hA).comp hsamp
  have hq_ae : ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ q n omega) atTop (nhds 0) := by
    filter_upwards [bootstrapMeanVec_sub_populationMean_tendsto_zero_ae
      S g hg hg_int] with omega homega
    let C : ℝ := max ‖e.symm.toContinuousLinearMap‖ 1
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    let eta := epsilon / C
    have heta : 0 < eta := div_pos hepsilon hC
    have hlarge := homega eta heta
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ measureReal_nonneg
    · filter_upwards [eventually_ne_atTop 0] with n hn
      let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
        bootstrapResample_isProbabilityMeasure _ hn
      have hsubset :
          {xstar : Fin n → X | epsilon <
            ‖finMean (fun i ↦ olsRawMoment x y (xstar i)) -
              olsPopulationMoments P x y‖} ⊆
          {xstar : Fin n → X | eta <
            ‖finMean (fun i ↦ g (xstar i)) - ∫ z, g z ∂P‖} := by
        intro xstar hxstar
        let v := finMean (fun i ↦ olsRawMoment x y (xstar i)) -
          olsPopulationMoments P x y
        have hv : ‖v‖ ≤ ‖e v‖ * C := calc
          ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
          _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ :=
            e.symm.toContinuousLinearMap.le_opNorm _
          _ ≤ C * ‖e v‖ := mul_le_mul_of_nonneg_right
            (le_max_left _ _) (norm_nonneg _)
          _ = ‖e v‖ * C := mul_comm _ _
        change epsilon < ‖v‖ at hxstar
        change eta <
          ‖finMean (fun i ↦ g (xstar i)) - ∫ z, g z ∂P‖
        rw [hmean, hint, ← e.map_sub]
        exact (div_lt_iff₀ hC).2 (hxstar.trans_le hv)
      exact measureReal_mono hsubset (h₂ := measure_ne_top _ _)
    · exact hlarge
  exact measureReal_gt_tendsto_zero_of_ae_tendsto
    hq_meas hq_ae delta hdelta

/-! ### The two bootstrap-side conditions -/

/-- Under [iid sampling, measurable regressors and outcome, integrable raw OLS moments, and a
positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), [the resampled OLS estimator
eventually solves its own normal equations exactly in bootstrap probability, in sampling
probability](goal).

Positive definiteness makes the population Gram determinant a unit, so a whole neighbourhood of
the population moments keeps it nonzero; the bootstrap weak law puts the resample moments in that
neighbourhood, where the deterministic normal equations hold exactly. -/
theorem olsSampleEstimator_bootstrapEventuallySolvesExactly
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    BootstrapEventuallySolvesEstimatingEquationExactly S
      (olsScore x y) (olsSampleEstimator x y) := by
  let M₀ := olsPopulationMoments P x y
  have hdet : (olsQFromMoments M₀).det ≠ 0 := by
    have hu : IsUnit (olsQ P x y) := hQ.isUnit
    have hudet : IsUnit (olsQ P x y).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hu
    simpa [M₀, olsQ] using hudet.ne_zero
  have hdet_cont : Continuous
      (fun M : OLSMoment K ↦ (olsQFromMoments M).det) :=
    continuous_id.matrix_det.comp
      (continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_apply _)
  have hdet_nhds :
      {M : OLSMoment K | (olsQFromMoments M).det ≠ 0} ∈ nhds M₀ :=
    hdet_cont.continuousAt (isOpen_ne.mem_nhds hdet)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hdet_nhds
  let eta := r / 2
  have heta : 0 < eta := half_pos hr
  unfold BootstrapEventuallySolvesEstimatingEquationExactly
  intro delta hdelta
  have htail := olsRawMoment_bootstrap_tendstoInProbability
    S hx hy hraw eta heta delta hdelta
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ htail
  filter_upwards [eventually_ne_atTop 0] with n hn
  apply measureReal_mono
  · intro omega homega
    let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
      bootstrapResample_isProbabilityMeasure _ hn
    refine homega.trans_le (measureReal_mono ?_)
    intro xstar hscore
    by_contra hnot
    have hle :
        ‖finMean (fun i ↦ olsRawMoment x y (xstar i)) - M₀‖ ≤ eta :=
      le_of_not_gt hnot
    have hlt :
        dist (finMean (fun i ↦ olsRawMoment x y (xstar i))) M₀ < r := by
      rw [dist_eq_norm]
      exact hle.trans_lt (half_lt_self hr)
    have hdet_star := hball (Metric.mem_ball.mpr hlt)
    exact hscore (olsSampleEstimator_score_eq_zero_of_det_ne_zero
      x y n xstar hdet_star)
  · exact measure_ne_top _ _

/-- Under [iid sampling, measurable regressors and outcome, integrable raw OLS moments, and a
positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), [the root-sample-size score
residual of the resampled OLS estimator is negligible in bootstrap probability, in sampling
probability](goal). -/
theorem olsSampleEstimator_bootstrapSolves
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    BootstrapSolvesEstimatingEquationInProbability S
      (olsScore x y) (olsSampleEstimator x y) :=
  bootstrapSolvesEstimatingEquationInProbability_of_eventuallyExactly S
    (olsScore x y) (olsSampleEstimator x y)
    (olsSampleEstimator_bootstrapEventuallySolvesExactly S hx hy hraw hQ)

/-- Under [iid sampling, measurable regressors and outcome, integrable raw OLS moments, and a
positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), [the resampled OLS estimator
converges to the population OLS coefficient in bootstrap probability, in sampling
probability](goal).

The population Gram determinant is nonzero by positive definiteness, so the closed-form
coefficient map is continuous there and carries conditional raw-moment convergence to conditional
coefficient convergence. -/
theorem olsSampleEstimator_bootstrapConsistent
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    BootstrapEstimatorConsistent S
      (olsSampleEstimator x y) (olsBeta P x y) := by
  let M₀ := olsPopulationMoments P x y
  have hdet : (olsQFromMoments M₀).det ≠ 0 := by
    have hu : IsUnit (olsQ P x y) := hQ.isUnit
    have hudet : IsUnit (olsQ P x y).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hu
    simpa [M₀, olsQ] using hudet.ne_zero
  have hbeta := continuousAt_olsBetaFromMoments M₀ hdet
  unfold BootstrapEstimatorConsistent BootstrapTendstoInProbability
  intro epsilon hepsilon delta hdelta
  have hbeta_nhds :
      {M : OLSMoment K |
        dist (olsBetaFromMoments M) (olsBetaFromMoments M₀) < epsilon} ∈ nhds M₀ := by
    change olsBetaFromMoments ⁻¹'
      Metric.ball (olsBetaFromMoments M₀) epsilon ∈ nhds M₀
    exact hbeta (Metric.ball_mem_nhds (olsBetaFromMoments M₀) hepsilon)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hbeta_nhds
  let eta := r / 2
  have heta : 0 < eta := half_pos hr
  have htail := olsRawMoment_bootstrap_tendstoInProbability
    S hx hy hraw eta heta delta hdelta
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ htail
  filter_upwards [eventually_ne_atTop 0] with n hn
  apply measureReal_mono
  · intro omega homega
    let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
      bootstrapResample_isProbabilityMeasure _ hn
    refine homega.trans_le (measureReal_mono ?_)
    intro xstar hbeta_bad
    by_contra hnot
    have hle :
        ‖finMean (fun i ↦ olsRawMoment x y (xstar i)) - M₀‖ ≤ eta :=
      le_of_not_gt hnot
    have hlt :
        dist (finMean (fun i ↦ olsRawMoment x y (xstar i))) M₀ < r := by
      rw [dist_eq_norm]
      exact hle.trans_lt (half_lt_self hr)
    have hgood := hball (Metric.mem_ball.mpr hlt)
    change epsilon <
      ‖olsBetaFromMoments (finMean (fun i ↦ olsRawMoment x y (xstar i))) -
        olsBetaFromMoments M₀‖ at hbeta_bad
    exact (not_lt_of_ge hbeta_bad.le) (by
      simpa [dist_eq_norm, olsSampleEstimator, olsBeta, M₀] using hgood)
  · exact measure_ne_top _ _

namespace BootstrapAsymLinear

/-! ### User-facing endpoints -/

/-- Under [iid sampling, measurable regressors and outcome, integrable raw OLS moments, and a
positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), and for [a contrast with
positive influence variance](hyp:c,hVar), [the OLS contrast is bootstrap asymptotically
linear](goal).

This is `olsContrast` with both of its bootstrap-side hypotheses discharged: the user supplies
measurability, integrability of every augmented monomial through degree four, and a
positive-definite population Gram matrix, but nothing about the resampling scheme. -/
theorem olsContrast_of_moments
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef)
    (c : EuclideanSpace ℝ K →L[ℝ] ℝ)
    (hVar : 0 < ∫ z, (c (olsInfluence P x y z)) ^ 2 ∂P) :
    BootstrapAsymLinear S
      (fun n data ↦ c (olsSampleEstimator x y n data))
      (c (olsBeta P x y))
      (fun z ↦ c (olsInfluence P x y z)) :=
  olsContrast S hx hy hraw hQ c
    (olsSampleEstimator_bootstrapConsistent S hx hy hraw hQ)
    (olsSampleEstimator_bootstrapSolves S hx hy hraw hQ) hVar

/-- Under [iid sampling, measurable regressors and outcome, integrable raw OLS moments, and a
positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), for [a contrast with positive
influence variance](hyp:c,hVar), and at
[an interior nominal error level](hyp:alpha,halpha0,halpha1), [the percentile bootstrap interval
for the OLS contrast attains limiting coverage one minus that level](goal).

This endpoint assumes integrability of every augmented regressor/outcome monomial through degree
four, not merely the lower-order moments used in some classical OLS formulations. -/
theorem olsContrast_percentileCI_coverage_of_moments
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef)
    (c : EuclideanSpace ℝ K →L[ℝ] ℝ)
    (hVar : 0 < ∫ z, (c (olsInfluence P x y z)) ^ 2 ∂P)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Tendsto
      (fun n ↦ mu.real {omega |
        c (olsBeta P x y) ∈ percentileCI
          (fun m data ↦ c (olsSampleEstimator x y m data)) n alpha
          (S.sampleVector n omega)})
      atTop (nhds (1 - alpha)) :=
  (olsContrast_of_moments S hx hy hraw hQ c hVar).percentileCI_coverage
    halpha0 halpha1

end BootstrapAsymLinear

end

end Causalean.Stat

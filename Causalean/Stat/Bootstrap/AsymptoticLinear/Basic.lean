module

public import Causalean.Stat.Bootstrap.EfronResampling.Mean.Main
public import Causalean.Stat.Bootstrap.EfronResampling.Measurability
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Limit.ContinuousMapping

/-!
# Bootstrap distributions and intervals for asymptotically linear estimators

This module defines the centered estimator bootstrap statistic, its lower conditional quantile,
the percentile and basic confidence intervals, and the bundled sampling/bootstrap linearization
hypothesis used by the validity theorem.  It also records the measurability interface and the bridge
from the bundled sampling linearization to `IsAsymLinear`.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}

/-- The [centered bootstrap statistic](goal) for [an estimator](hyp:est) at [a sample
size](hyp:n) compares [the estimate on a same-size resample](hyp:xstar) with [the estimate on the
observed data](hyp:x), scaled by the square root of the sample size. -/
def centeredEstimatorBootstrapStatistic
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ) (n : ℕ)
    (x xstar : Fin n -> X) : ℝ :=
  Real.sqrt (n : ℝ) * (est n xstar - est n x)

/-- The [bootstrap quantile](goal) for [an estimator](hyp:est) at [a sample size](hyp:n) and
[quantile level](hyp:beta), based on [the observed data](hyp:x), is the lower quantile of the Efron
law of the centered estimator statistic. -/
def bootstrapQuantile (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (n : ℕ) (beta : ℝ) (x : Fin n -> X) : ℝ :=
  bootstrapLowerQuantile
    (centeredEstimatorBootstrapStatistic est n x) beta x

/-- The [percentile bootstrap confidence interval](goal) for [an estimator](hyp:est) at [a sample
size](hyp:n) and [nominal error level](hyp:alpha), based on [the observed data](hyp:x), adds the two
equal-tail centered-bootstrap quantiles, scaled by root sample size, to the estimate. -/
def percentileCI (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (n : ℕ) (alpha : ℝ) (x : Fin n -> X) : Set ℝ :=
  Icc
    (est n x + bootstrapQuantile est n (alpha / 2) x / Real.sqrt (n : ℝ))
    (est n x + bootstrapQuantile est n (1 - alpha / 2) x / Real.sqrt (n : ℝ))

/-- The [basic bootstrap confidence interval](goal) for [an estimator](hyp:est) at [a sample
size](hyp:n) and [nominal error level](hyp:alpha), based on [the observed data](hyp:x), reflects the
two equal-tail centered-bootstrap quantiles around the estimate. -/
def basicCI (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (n : ℕ) (alpha : ℝ) (x : Fin n -> X) : Set ℝ :=
  Icc
    (est n x - bootstrapQuantile est n (1 - alpha / 2) x / Real.sqrt (n : ℝ))
    (est n x - bootstrapQuantile est n (alpha / 2) x / Real.sqrt (n : ℝ))

/-- [An estimator](hyp:est) that is [measurable at every sample size](hyp:hest) induces [a
measurable centered bootstrap statistic as a function of the resample](goal) at [the chosen sample
size](hyp:n), with [the observed data](hyp:x) held fixed. -/
theorem measurable_centeredEstimatorBootstrapStatistic
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (hest : forall n, Measurable (est n)) (n : ℕ) (x : Fin n -> X) :
    Measurable (centeredEstimatorBootstrapStatistic est n x) := by
  -- Unfold the statistic; measurability is closed under subtraction and multiplication by the
  -- constant `sqrt n`.
  exact measurable_const.mul ((hest n).sub measurable_const)

/-- For [an estimator](hyp:est) that is [measurable at each sample size](hyp:hest), [a positive
sample size](hyp:hn), [an interior quantile level](hyp:hbeta0,hbeta1) and [observed data](hyp:x),
[the centered bootstrap quantile is the affine transform of the bootstrap quantile of the uncentered
estimator](goal): root sample size times its deviation from the observed estimate. -/
theorem bootstrapQuantile_eq_affine
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (hest : forall n, Measurable (est n)) {n : ℕ} (hn : n != 0)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1) (x : Fin n -> X) :
    bootstrapQuantile est n beta x =
      Real.sqrt (n : ℝ) *
        (bootstrapLowerQuantile (est n) beta x - est n x) := by
  -- `sqrt n` is positive.  Rewrite both lower quantiles as `sInf` sets and transport the CDF
  -- threshold set through the increasing affine map `y ↦ sqrt n * (y - est n x)`.
  have hn0 : n ≠ 0 := bne_iff_ne.mp hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  have hcenter := measurable_centeredEstimatorBootstrapStatistic est hest n x
  have hbeta1' : beta ≤ 1 := hbeta1.le
  have hcdf (t : ℝ) :
      bootstrapCDF (centeredEstimatorBootstrapStatistic est n x) x
          (Real.sqrt (n : ℝ) * (t - est n x)) =
        bootstrapCDF (est n) x t := by
    rw [bootstrapCDF_eq_average_indicators _ hcenter x _ hn0,
      bootstrapCDF_eq_average_indicators _ (hest n) x t hn0]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hiff : centeredEstimatorBootstrapStatistic est n x (x ∘ j) ≤
      Real.sqrt (n : ℝ) * (t - est n x) ↔ est n (x ∘ j) ≤ t := by
      unfold centeredEstimatorBootstrapStatistic
      rw [mul_le_mul_iff_of_pos_left hsqrt, sub_le_sub_iff_right]
    simp only [hiff]
  apply le_antisymm
  · change bootstrapLowerQuantile
        (centeredEstimatorBootstrapStatistic est n x) beta x ≤ _
    rw [bootstrapLowerQuantile_le_iff _ hcenter x hn0 beta _
      hbeta0 hbeta1', hcdf]
    exact (bootstrapLowerQuantile_le_iff (est n) (hest n) x hn0 beta _
      hbeta0 hbeta1').mp le_rfl
  · let qstar := bootstrapQuantile est n beta x
    have hreach : beta ≤ bootstrapCDF
        (centeredEstimatorBootstrapStatistic est n x) x qstar :=
      (bootstrapLowerQuantile_le_iff _ hcenter x hn0 beta qstar
        hbeta0 hbeta1').mp le_rfl
    have hcdf' : bootstrapCDF
        (centeredEstimatorBootstrapStatistic est n x) x qstar =
        bootstrapCDF (est n) x
          (qstar / Real.sqrt (n : ℝ) + est n x) := by
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt
      rw [← hcdf (qstar / Real.sqrt (n : ℝ) + est n x)]
      congr 2
      field_simp [hsqrt_ne] <;> ring
    have hq : bootstrapLowerQuantile (est n) beta x ≤
        qstar / Real.sqrt (n : ℝ) + est n x :=
      (bootstrapLowerQuantile_le_iff (est n) (hest n) x hn0 beta _
        hbeta0 hbeta1').mpr (by rwa [← hcdf'])
    change Real.sqrt (n : ℝ) *
        (bootstrapLowerQuantile (est n) beta x - est n x) ≤ qstar
    calc
      Real.sqrt (n : ℝ) *
          (bootstrapLowerQuantile (est n) beta x - est n x) ≤
          Real.sqrt (n : ℝ) *
            ((qstar / Real.sqrt (n : ℝ) + est n x) - est n x) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hq _) hsqrt.le
      _ = qstar := by field_simp [ne_of_gt hsqrt] <;> ring

/-- For [an estimator defined on samples of every size](hyp:est) that is [measurable at each
sample size](hyp:hest), [a sample size](hyp:n), and [an interior quantile level](hyp:hbeta0,hbeta1),
[the centered bootstrap quantile is a measurable function of the observed data](goal). -/
theorem measurable_bootstrapQuantile
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (hest : forall n, Measurable (est n)) (n : ℕ)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    Measurable (bootstrapQuantile est n beta) := by
  -- Split on `n = 0` (the statistic is constant) and otherwise use
  -- `bootstrapQuantile_eq_affine` plus `measurable_bootstrapLowerQuantile`.
  by_cases hn : n = 0
  · subst n
    let x0 : Fin 0 → X := fun i ↦ Fin.elim0 i
    have heq : bootstrapQuantile est 0 beta = fun _ ↦ bootstrapQuantile est 0 beta x0 := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    exact measurable_const
  · rw [show bootstrapQuantile est n beta = fun x ↦ Real.sqrt (n : ℝ) *
        (bootstrapLowerQuantile (est n) beta x - est n x) by
      funext x
      exact bootstrapQuantile_eq_affine est hest (bne_iff_ne.mpr hn) hbeta0 hbeta1 x]
    exact measurable_const.mul
      ((measurable_bootstrapLowerQuantile (est n) (hest n) hn beta).sub
        (hest n))

/-- The [sampling law of the centered, root-sample-size-scaled estimator](goal) for [an iid
sample](hyp:S), [an estimator](hyp:est), [a target value](hyp:theta0), and [a sample
size](hyp:n) is its pushforward law under the original sampling measure when [the estimator is
measurable at every sample size](hyp:hest). -/
def samplingEstimatorLaw (S : IIDSample Omega X mu P)
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ) (theta0 : ℝ)
    (hest : forall n, Measurable (est n)) (n : ℕ) : ProbabilityMeasure ℝ := by
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hx : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  exact ⟨mu.map (fun omega => Real.sqrt (n : ℝ) *
      (est n (S.sampleVector n omega) - theta0)),
    Measure.isProbabilityMeasure_map (by
      exact (measurable_const.mul
        ((hest n).comp hx |>.sub measurable_const)).aemeasurable)⟩

/-- The [conditional bootstrap law](goal) of [an estimator](hyp:est) at [the specified sample
size](hyp:n) and [observed data](hyp:x) uses the Efron law of its centered statistic when [the
estimator is measurable at every sample size](hyp:hest); at size zero it is a point mass at zero. -/
def bootstrapEstimatorLaw
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (hest : forall n, Measurable (est n)) (n : ℕ)
    (x : Fin n -> X) : ProbabilityMeasure ℝ :=
  if hn : n = 0 then
    ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩
  else
    ⟨bootstrapLaw
        (centeredEstimatorBootstrapStatistic est n x) x,
      bootstrapLaw_isProbabilityMeasure
        _ _ hn (measurable_centeredEstimatorBootstrapStatistic est hest n x)⟩

/-- [The bootstrap quantile equals the lower quantile of the bundled conditional
estimator-bootstrap law](goal) for [a measurable estimator](hyp:est,hest), [a positive sample
size](hyp:hn), [a quantile level](hyp:beta), and [observed data](hyp:x). -/
theorem bootstrapQuantile_eq_quantile_bootstrapEstimatorLaw
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ)
    (hest : forall n, Measurable (est n)) {n : ℕ} (hn : n != 0)
    (beta : ℝ) (x : Fin n -> X) :
    bootstrapQuantile est n beta x =
      quantile (bootstrapEstimatorLaw est hest n x : Measure ℝ) beta := by
  -- In the nonzero branch the bundled law is the literal `bootstrapLaw`; unfold
  -- `bootstrapLowerQuantile`, `bootstrapCDF`, and `quantile`, then use `cdf_eq_real`.
  have hn0 : n ≠ 0 := bne_iff_ne.mp hn
  let _ : IsProbabilityMeasure
      (bootstrapLaw (centeredEstimatorBootstrapStatistic est n x) x) :=
    bootstrapLaw_isProbabilityMeasure _ _ hn0
      (measurable_centeredEstimatorBootstrapStatistic est hest n x)
  have hlaw : (bootstrapEstimatorLaw est hest n x : Measure ℝ) =
      bootstrapLaw (centeredEstimatorBootstrapStatistic est n x) x := by
    simp [bootstrapEstimatorLaw, hn0]
  rw [hlaw]
  unfold bootstrapQuantile bootstrapLowerQuantile
    bootstrapCDF quantile quantileSet
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  rw [ProbabilityTheory.cdf_eq_real, Measure.real_def]

/-- An [iid sample](hyp:S), [estimator](hyp:est), [target value](hyp:theta0), and [influence
function](hyp:psi) are bootstrap asymptotically linear when [the estimator and influence function
are measurable](hyp:meas), [the influence function is centered](hyp:mean_zero), [its second moment
is positive and finite](hyp:var_pos_finite), [the sampling remainder vanishes in
probability](hyp:linear), and [the conditional bootstrap remainder vanishes in outer sampling
probability](hyp:boot_linear). -/
structure BootstrapAsymLinear (S : IIDSample Omega X mu P)
    (est : (n : ℕ) -> (Fin n -> X) -> ℝ) (theta0 : ℝ) (psi : X -> ℝ) : Prop where
  meas : (forall n, Measurable (est n)) ∧ Measurable psi
  mean_zero : (∫ x, psi x ∂P) = 0
  var_pos_finite :
    0 < (∫ x, (psi x) ^ 2 ∂P) ∧
      Integrable (fun x => (psi x) ^ 2) P
  linear : Tendsto_inProb
    (fun n omega =>
      Real.sqrt (n : ℝ) * (est n (S.sampleVector n omega) - theta0) -
        IsAsymLinear.normalizedSum S psi (fun m => Finset.range m) n omega)
    (fun _ => 0) mu
  boot_linear : forall epsilon : ℝ, 0 < epsilon ->
    Tendsto
      (fun n => mu.real {omega |
        epsilon < (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon < abs
            (centeredEstimatorBootstrapStatistic est n (S.sampleVector n omega) xstar -
              centeredBootstrapSum psi
                (S.sampleVector n omega) xstar)}})
      atTop (nhds 0)

namespace BootstrapAsymLinear

variable {S : IIDSample Omega X mu P}
  {est : (n : ℕ) -> (Fin n -> X) -> ℝ} {theta0 : ℝ} {psi : X -> ℝ}

/-- The [asymptotic variance](goal) associated with [a bootstrap-asymptotically-linear
estimator](hyp:h) is the second moment of its influence function. -/
def asymptoticVariance (h : BootstrapAsymLinear S est theta0 psi) : ℝ :=
  ∫ x, (psi x) ^ 2 ∂P

/-- The [limiting Gaussian law](goal) attached to [a bootstrap-asymptotically-linear
estimator](hyp:h) is centered and has variance equal to the influence-function second moment. -/
def asymptoticGaussian (h : BootstrapAsymLinear S est theta0 psi) :
    ProbabilityMeasure ℝ :=
  ⟨gaussianMeasure 0 h.asymptoticVariance, inferInstance⟩

/-- [Bootstrap asymptotic linearity](hyp:h) implies [ordinary full-sample asymptotic linearity for
the estimator evaluated on the iid sample vector](goal). -/
theorem isAsymLinear (h : BootstrapAsymLinear S est theta0 psi) :
    IsAsymLinear (fun n omega => est n (S.sampleVector n omega)) theta0 psi S
      (fun m => Finset.range m) := by
  -- Reuse `mean_zero` and square integrability.  Convert `h.linear` to `IsLittleOp _ 1` with
  -- `Tendsto_inProb.isLittleOp_one`, then simplify the range cardinality and the two existing
  -- normalized-sum/rescaled-estimator definitions.
  refine ⟨h.mean_zero, h.var_pos_finite.2, ?_⟩
  simpa [IsAsymLinear.normalizedSum, Finset.card_range] using h.linear.isLittleOp_one

/-- [The percentile interval's coverage event is measurable under the sampling
sigma-algebra](goal) for [a bootstrap-asymptotically-linear estimator](hyp:h) at [a sample
size](hyp:n) when [the nominal error level is interior](hyp:halpha0,halpha1). -/
theorem measurableSet_percentileCI_coverage
    (h : BootstrapAsymLinear S est theta0 psi) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (n : ℕ) :
    MeasurableSet {omega |
      theta0 ∈ percentileCI est n alpha (S.sampleVector n omega)} := by
  -- Prove measurability of `sampleVector` coordinatewise from `S.meas`; compose the two
  -- `measurable_bootstrapQuantile` results and unfold membership in `Icc`.
  have hx : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have ha2_pos : 0 < alpha / 2 := div_pos halpha0 (by norm_num)
  have ha2_lt_one : alpha / 2 < 1 := by linarith
  have h1a2_pos : 0 < 1 - alpha / 2 := by linarith
  have h1a2_lt_one : 1 - alpha / 2 < 1 := by linarith
  have hest_meas : Measurable (fun omega => est n (S.sampleVector n omega)) :=
    (h.meas.1 n).comp hx
  have hlo : Measurable (fun omega =>
      est n (S.sampleVector n omega) +
        bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)) :=
    hest_meas.add ((measurable_bootstrapQuantile est h.meas.1 n ha2_pos ha2_lt_one).comp hx
      |>.div_const _)
  have hhi : Measurable (fun omega =>
      est n (S.sampleVector n omega) +
        bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)) :=
    hest_meas.add ((measurable_bootstrapQuantile est h.meas.1 n h1a2_pos h1a2_lt_one).comp hx
      |>.div_const _)
  change MeasurableSet
    ({omega | est n (S.sampleVector n omega) +
        bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ) ≤ theta0} ∩
      {omega | theta0 ≤ est n (S.sampleVector n omega) +
        bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)})
  exact (measurableSet_le hlo measurable_const).inter
    (measurableSet_le measurable_const hhi)

/-- [The basic bootstrap interval's coverage event is measurable under the sampling
sigma-algebra](goal) for [a bootstrap-asymptotically-linear estimator](hyp:h) at [a sample
size](hyp:n) when [the nominal error level is interior](hyp:halpha0,halpha1). -/
theorem measurableSet_basicCI_coverage
    (h : BootstrapAsymLinear S est theta0 psi) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (n : ℕ) :
    MeasurableSet {omega |
      theta0 ∈ basicCI est n alpha (S.sampleVector n omega)} := by
  -- As for the percentile event, compose measurable estimator/quantile endpoints with the
  -- measurable sample vector and use `measurableSet_le` for both inequalities.
  have hx : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have ha2_pos : 0 < alpha / 2 := div_pos halpha0 (by norm_num)
  have ha2_lt_one : alpha / 2 < 1 := by linarith
  have h1a2_pos : 0 < 1 - alpha / 2 := by linarith
  have h1a2_lt_one : 1 - alpha / 2 < 1 := by linarith
  have hest_meas : Measurable (fun omega => est n (S.sampleVector n omega)) :=
    (h.meas.1 n).comp hx
  have hlo : Measurable (fun omega =>
      est n (S.sampleVector n omega) -
        bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)) :=
    hest_meas.sub ((measurable_bootstrapQuantile est h.meas.1 n h1a2_pos h1a2_lt_one).comp hx
      |>.div_const _)
  have hhi : Measurable (fun omega =>
      est n (S.sampleVector n omega) -
        bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)) :=
    hest_meas.sub ((measurable_bootstrapQuantile est h.meas.1 n ha2_pos ha2_lt_one).comp hx
      |>.div_const _)
  change MeasurableSet
    ({omega | est n (S.sampleVector n omega) -
        bootstrapQuantile est n (1 - alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ) ≤ theta0} ∩
      {omega | theta0 ≤ est n (S.sampleVector n omega) -
        bootstrapQuantile est n (alpha / 2) (S.sampleVector n omega) /
          Real.sqrt (n : ℝ)})
  exact (measurableSet_le hlo measurable_const).inter
    (measurableSet_le measurable_const hhi)

end BootstrapAsymLinear

end

end Causalean.Stat

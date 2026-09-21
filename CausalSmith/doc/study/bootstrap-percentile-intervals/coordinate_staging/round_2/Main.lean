module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.LimitLemmas
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Bootstrap laws and quantiles for asymptotically linear estimators

This module proves the distributional consequences of bootstrap asymptotic linearity. The sampling
and conditional bootstrap laws approach the same centered Gaussian law, hence approach one
another in Kolmogorov distance, and conditional quantiles converge in sampling probability.
-/

public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}
  {S : IIDSample Omega X mu P}
  {est : (n : ℕ) -> (Fin n -> X) -> ℝ} {theta0 : ℝ} {psi : X -> ℝ}

private theorem cdfKolmogorov_eq_iSup_rat (nu G : ProbabilityMeasure ℝ) :
    Causalean.Stat.cdfKolmogorov nu G =
      ⨆ q : ℚ, |cdf (nu : Measure ℝ) q - cdf (G : Measure ℝ) q| := by
  unfold Causalean.Stat.cdfKolmogorov
  have hbReal : BddAbove (range fun t : ℝ =>
      |cdf (nu : Measure ℝ) t - cdf (G : Measure ℝ) t|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (nu : Measure ℝ) t, cdf_le_one (nu : Measure ℝ) t,
        cdf_nonneg (G : Measure ℝ) t, cdf_le_one (G : Measure ℝ) t]
  have hbRat : BddAbove (range fun q : ℚ =>
      |cdf (nu : Measure ℝ) q - cdf (G : Measure ℝ) q|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨q, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (nu : Measure ℝ) (q : ℝ),
        cdf_le_one (nu : Measure ℝ) (q : ℝ),
        cdf_nonneg (G : Measure ℝ) (q : ℝ),
        cdf_le_one (G : Measure ℝ) (q : ℝ)]
  apply le_antisymm
  · refine ciSup_le fun t => ?_
    obtain ⟨u, _, hu_gt, hu_tend⟩ := Real.exists_seq_rat_strictAnti_tendsto t
    have hu_within : Tendsto (fun n => (u n : ℝ)) atTop (nhdsWithin t (Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hu_tend, Filter.Eventually.of_forall fun n => (hu_gt n).le⟩
    have hnu := ((cdf (nu : Measure ℝ)).right_continuous t).tendsto.comp hu_within
    have hG := ((cdf (G : Measure ℝ)).right_continuous t).tendsto.comp hu_within
    have habs : Tendsto
        (fun n => |cdf (nu : Measure ℝ) (u n) - cdf (G : Measure ℝ) (u n)|)
        atTop (nhds |cdf (nu : Measure ℝ) t - cdf (G : Measure ℝ) t|) :=
      (hnu.sub hG).abs
    exact le_of_tendsto habs
      (Filter.Eventually.of_forall fun n => le_ciSup hbRat (u n))
  · refine ciSup_le fun q => ?_
    exact le_ciSup hbReal (q : ℝ)

namespace BootstrapAsymLinear

/-- Given [a bootstrap-asymptotically-linear estimator](hyp:h), [its square-root-scaled sampling
laws converge weakly to its centered Gaussian influence-function law](goal). -/
theorem sampling_tendsto_gaussian (h : BootstrapAsymLinear S est theta0 psi) :
    Tendsto
      (samplingEstimatorLaw S est theta0 h.meas.1)
      atTop (nhds h.asymptoticGaussian) := by
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hx (n : ℕ) : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have hscaled (n : ℕ) : AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (fun n omega => est n (S.sampleVector n omega)) theta0
        (fun m => Finset.range m) n) mu := by
    unfold IsAsymLinear.rescaledEstimator
    exact (measurable_const.mul
      (((h.meas.1 n).comp (hx n)).sub measurable_const)).aemeasurable
  have hnormal := h.isAsymLinear.tendsto_normal h.meas.2 hscaled
  unfold Tendsto_dist at hnormal
  have hlaw : samplingEstimatorLaw S est theta0 h.meas.1 =
      fun n => ⟨mu.map
        (IsAsymLinear.rescaledEstimator
          (fun n omega => est n (S.sampleVector n omega)) theta0
          (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hscaled n)⟩ := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    unfold samplingEstimatorLaw IsAsymLinear.rescaledEstimator
    simp only [Finset.card_range]
  rw [hlaw]
  simpa [asymptoticGaussian, asymptoticVariance] using hnormal

/-- Given [a bootstrap-asymptotically-linear estimator](hyp:h), [the conditional bootstrap laws
of its centered estimator statistic converge in Kolmogorov distance in sampling probability to
its centered Gaussian influence-function law](goal). -/
theorem bootstrap_tendsto_gaussian (h : BootstrapAsymLinear S est theta0 psi) :
    Tendsto_inProb
      (fun n omega => Causalean.Stat.cdfKolmogorov
        (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
        h.asymptoticGaussian)
      (fun _ => 0) mu := by
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hvar : ProbabilityTheory.variance psi P = h.asymptoticVariance := by
    rw [ProbabilityTheory.variance_eq_integral h.meas.2.aemeasurable, h.mean_zero]
    simp [asymptoticVariance]
  have hpop_pos : 0 < Causalean.Stat.populationVariance psi P := by
    rw [Causalean.Stat.populationVariance, Real.toNNReal_pos, hvar]
    simpa [asymptoticVariance] using h.var_pos_finite.1
  let Gmean : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (Causalean.Stat.populationVariance psi P), inferInstance⟩
  have hG : Gmean = h.asymptoticGaussian := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [Gmean, asymptoticGaussian, gaussianMeasure, asymptoticVariance,
      Causalean.Stat.populationVariance, hvar]
  have hGcont : Continuous (cdf (h.asymptoticGaussian : Measure ℝ)) := by
    rw [← hG]
    exact Causalean.Stat.continuous_cdf_gaussianReal_zero hpop_pos
  have hlinearAE : ∀ᵐ omega ∂mu,
      Tendsto (fun n => Causalean.Stat.cdfKolmogorov
        (Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega)
        h.asymptoticGaussian) atTop (nhds 0) := by
    filter_upwards [Causalean.Stat.bootstrapMeanLaw_tendsto_gaussian_ae
      S psi h.meas.2 h.var_pos_finite.2] with omega homega
    rw [← hG]
    exact Causalean.Stat.tendsto_cdfKolmogorov_of_tendsto
      homega tendsto_const_nhds
      (Causalean.Stat.continuous_cdf_gaussianReal_zero hpop_pos)
  have hlinearLawMeas (n : ℕ) : Measurable (fun omega =>
      Causalean.Stat.cdfKolmogorov
        (Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega)
        h.asymptoticGaussian) := by
    by_cases hn : n = 0
    · subst n
      simp only [Causalean.Stat.bootstrapMeanLaw, ↓reduceDIte]
      exact measurable_const
    · rw [show (fun omega => Causalean.Stat.cdfKolmogorov
            (Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega)
            h.asymptoticGaussian) =
          fun omega => ⨆ q : ℚ,
            |Causalean.Stat.bootstrapCDF
                (Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega))
                (S.sampleVector n omega) q -
              cdf (h.asymptoticGaussian : Measure ℝ) q| by
          funext omega
          rw [cdfKolmogorov_eq_iSup_rat]
          congr 1
          funext q
          let _ : IsProbabilityMeasure
              (Causalean.Stat.bootstrapLaw
                (Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega))
                (S.sampleVector n omega)) :=
            Causalean.Stat.bootstrapLaw_isProbabilityMeasure _ _ hn
              (Causalean.Stat.measurable_centeredBootstrapSum psi h.meas.2 _)
          rw [Causalean.Stat.bootstrapMeanLaw_toMeasure hn,
            cdf_eq_real, Measure.real_def]
          rfl]
      apply Measurable.iSup
      intro q
      apply Measurable.abs
      apply Measurable.sub_const
      rw [show (fun omega =>
          Causalean.Stat.bootstrapCDF
            (Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega))
            (S.sampleVector n omega) (q : ℝ)) =
          fun omega => ((n : ℝ) ^ n)⁻¹ *
            ∑ j : Fin n → Fin n,
              if Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega)
                  (S.sampleVector n omega ∘ j) ≤ q then 1 else 0 by
        funext omega
        exact Causalean.Stat.bootstrapCDF_eq_average_indicators _
          (Causalean.Stat.measurable_centeredBootstrapSum psi h.meas.2 _) _ _ hn]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j hj
      have hmean : Measurable (fun omega =>
          (n : ℝ)⁻¹ * ∑ k : Fin n, psi (S.Z k omega)) :=
        measurable_const.mul (Finset.measurable_sum _
          (fun k _ => h.meas.2.comp (S.meas k)))
      have hstat : Measurable (fun omega =>
          Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega)
            (S.sampleVector n omega ∘ j)) := by
        unfold Causalean.Stat.centeredBootstrapSum Causalean.Stat.finAverage
        exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
          (h.meas.2.comp (S.meas (j i))).sub hmean))
      exact Measurable.ite
        (measurableSet_le hstat measurable_const) measurable_const measurable_const
  have hlinearProb : Tendsto_inProb (fun n omega =>
      Causalean.Stat.cdfKolmogorov
        (Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega)
        h.asymptoticGaussian) (fun _ => 0) mu := by
    unfold Tendsto_inProb
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hlinearLawMeas n).aestronglyMeasurable) hlinearAE

  let extend (n : ℕ) (omega : Omega) (xstar : Fin n → X) : ℕ → X :=
    fun i => if hi : i < n then xstar ⟨i, hi⟩ else S.Z i omega
  have hextMeas (n : ℕ) (omega : Omega) : Measurable (extend n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    unfold extend
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  let nu (n : ℕ) (omega : Omega) : ProbabilityMeasure (ℕ → X) :=
    if hn : n = 0 then
      (⟨Measure.dirac (fun i => S.Z i omega), Measure.dirac.isProbabilityMeasure⟩ :
        ProbabilityMeasure (ℕ → X))
    else
      let _ : IsProbabilityMeasure
          (Causalean.Stat.bootstrapResample (S.sampleVector n omega)) :=
        Causalean.Stat.bootstrapResample_isProbabilityMeasure _ hn
      (⟨(Causalean.Stat.bootstrapResample (S.sampleVector n omega)).map (extend n omega),
        Measure.isProbabilityMeasure_map (hextMeas n omega).aemeasurable⟩ :
        ProbabilityMeasure (ℕ → X))
  let linear (n : ℕ) (omega : Omega) (y : ℕ → X) : ℝ :=
    Causalean.Stat.centeredBootstrapSum psi (S.sampleVector n omega) (fun i => y i)
  let remainder (n : ℕ) (omega : Omega) (y : ℕ → X) : ℝ :=
    centeredEstimatorBootstrapStatistic est n (S.sampleVector n omega) (fun i => y i) -
      linear n omega y
  have hlinearMeas (n : ℕ) (omega : Omega) : Measurable (linear n omega) := by
    unfold linear
    exact (Causalean.Stat.measurable_centeredBootstrapSum psi h.meas.2 _).comp
      (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)
  have hremainderMeas (n : ℕ) (omega : Omega) : Measurable (remainder n omega) := by
    unfold remainder centeredEstimatorBootstrapStatistic
    exact (measurable_const.mul
      (((h.meas.1 n).comp
        (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)).sub
          measurable_const)).sub (hlinearMeas n omega)
  have hnueq {n : ℕ} (hn : n ≠ 0) (omega : Omega) :
      (nu n omega : Measure (ℕ → X)) =
        (Causalean.Stat.bootstrapResample (S.sampleVector n omega)).map
          (extend n omega) := by
    simp [nu, hn]
  have hlinlaw {n : ℕ} (hn : n ≠ 0) (omega : Omega) :
      (nu n omega).map (hlinearMeas n omega).aemeasurable =
        Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (linear n omega) (nu n omega : Measure (ℕ → X)) = _
    rw [hnueq hn omega,
      Measure.map_map (hlinearMeas n omega) (hextMeas n omega),
      Causalean.Stat.bootstrapMeanLaw_toMeasure hn]
    unfold Causalean.Stat.bootstrapLaw
    congr 1
    funext xstar
    simp [linear, extend]
  have hsumlaw {n : ℕ} (hn : n ≠ 0) (omega : Omega) :
      (nu n omega).map
          ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable =
        bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega) := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun y => linear n omega y + remainder n omega y)
        (nu n omega : Measure (ℕ → X)) = _
    rw [hnueq hn omega,
      Measure.map_map (g := fun y => linear n omega y + remainder n omega y)
        ((hlinearMeas n omega).add (hremainderMeas n omega)) (hextMeas n omega)]
    simp [bootstrapEstimatorLaw, hn, Causalean.Stat.bootstrapLaw]
    congr 1
    funext xstar
    simp [remainder, linear, extend]
  have hlinearMapped : Tendsto_inProb (fun n omega =>
      Causalean.Stat.cdfKolmogorov
        ((nu n omega).map (hlinearMeas n omega).aemeasurable)
        h.asymptoticGaussian) (fun _ => 0) mu := by
    unfold Tendsto_inProb at hlinearProb ⊢
    apply TendstoInMeasure.congr'
      (f := fun n omega => Causalean.Stat.cdfKolmogorov
        (Causalean.Stat.bootstrapMeanLaw S psi h.meas.2 n omega)
        h.asymptoticGaussian) (g := fun _ => 0) _ (Eventually.of_forall fun _ => rfl)
      hlinearProb
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact Filter.Eventually.of_forall fun omega =>
      congrArg (fun law => Causalean.Stat.cdfKolmogorov law h.asymptoticGaussian)
        (hlinlaw hn omega).symm
  have htail (epsilon : ℝ) {n : ℕ} (hn : n ≠ 0) (omega : Omega) :
      (nu n omega : Measure (ℕ → X)).real
          {y | epsilon < abs (remainder n omega y)} =
        (Causalean.Stat.bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon < abs
            (centeredEstimatorBootstrapStatistic est n (S.sampleVector n omega) xstar -
              Causalean.Stat.centeredBootstrapSum psi
                (S.sampleVector n omega) xstar)} := by
    rw [hnueq hn omega, Measure.real_def, Measure.real_def,
      Measure.map_apply_of_aemeasurable
        (hextMeas n omega).aemeasurable
        (measurableSet_lt measurable_const (hremainderMeas n omega).abs)]
    congr 2
    ext xstar
    simp only [mem_preimage, mem_ofPred_eq]
    simp [remainder, linear, extend]
  have hremainder (epsilon : ℝ) (hepsilon : 0 < epsilon) : Tendsto
      (fun n => mu.real {omega |
        epsilon < (nu n omega : Measure (ℕ → X)).real
          {y | epsilon < abs (remainder n omega y)}})
      atTop (nhds 0) := by
    apply (h.boot_linear epsilon hepsilon).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    congr 1
    ext omega
    simp only [mem_ofPred_eq]
    rw [htail epsilon hn omega]
  have hslutsky := conditionalSlutsky_cdfKolmogorov_inProb
    nu linear remainder hlinearMeas hremainderMeas h.asymptoticGaussian hGcont
    hlinearMapped hremainder
  unfold Tendsto_inProb at hslutsky ⊢
  apply TendstoInMeasure.congr'
    (f := fun n omega => Causalean.Stat.cdfKolmogorov
      ((nu n omega).map
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable)
      h.asymptoticGaussian) (g := fun _ => 0) _ (Eventually.of_forall fun _ => rfl)
    hslutsky
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact Filter.Eventually.of_forall fun omega =>
    congrArg (fun law => Causalean.Stat.cdfKolmogorov law h.asymptoticGaussian)
      (hsumlaw hn omega)

/-- Given [a bootstrap-asymptotically-linear estimator](hyp:h), [its conditional centered
bootstrap law and its centered finite-sample law approach one another in Kolmogorov distance in
sampling probability](goal). -/
theorem consistent (h : BootstrapAsymLinear S est theta0 psi) :
    Tendsto_inProb
      (fun n omega => Causalean.Stat.cdfKolmogorov
        (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
        (samplingEstimatorLaw S est theta0 h.meas.1 n))
      (fun _ => 0) mu := by
  -- Pólya applied to `sampling_tendsto_gaussian` gives deterministic Kolmogorov convergence of
  -- the sampling law to the Gaussian law.  Combine it with `bootstrap_tendsto_gaussian` and
  -- `cdfKolmogorov_triangle` (using symmetry of the distance).
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hv : 0 < h.asymptoticVariance.toNNReal := by
    rw [Real.toNNReal_pos]
    exact h.var_pos_finite.1
  have hG : h.asymptoticGaussian =
      (⟨gaussianReal 0 h.asymptoticVariance.toNNReal, inferInstance⟩ :
        ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  have hGcont : Continuous (cdf (h.asymptoticGaussian : Measure ℝ)) := by
    rw [hG]
    exact Causalean.Stat.continuous_cdf_gaussianReal_zero hv
  have hsampling : Tendsto
      (fun n => Causalean.Stat.cdfKolmogorov
        (samplingEstimatorLaw S est theta0 h.meas.1 n) h.asymptoticGaussian)
      atTop (nhds 0) :=
    Causalean.Stat.tendsto_cdfKolmogorov_of_tendsto
      (sampling_tendsto_gaussian h) tendsto_const_nhds hGcont
  have hsamplingProb : Tendsto_inProb
      (fun n (_ : Omega) => Causalean.Stat.cdfKolmogorov
        h.asymptoticGaussian (samplingEstimatorLaw S est theta0 h.meas.1 n))
      (fun _ => 0) mu := by
    unfold Tendsto_inProb
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_const
    · filter_upwards [] with omega
      apply hsampling.congr'
      filter_upwards [] with n
      unfold Causalean.Stat.cdfKolmogorov
      congr 1
      funext t
      rw [abs_sub_comm]
  have hsum : Tendsto_inProb
      (fun n omega =>
        Causalean.Stat.cdfKolmogorov
            (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
            h.asymptoticGaussian +
          Causalean.Stat.cdfKolmogorov h.asymptoticGaussian
            (samplingEstimatorLaw S est theta0 h.meas.1 n))
      (fun _ => 0) mu := by
    have hneg := Tendsto_inProb.comp_continuousAt
      (g := fun x : ℝ => -x) continuousAt_neg hsamplingProb
    have hsub := Tendsto_inProb.sub (bootstrap_tendsto_gaussian h) hneg
    simpa only [Pi.zero_apply, neg_zero, sub_neg_eq_add, sub_self] using hsub
  unfold Tendsto_inProb at hsum ⊢
  rw [tendstoInMeasure_iff_norm] at hsum ⊢
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hsum epsilon hepsilon) (fun _ => zero_le) (fun n => ?_)
  apply measure_mono
  intro omega homega
  simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs] at homega ⊢
  have htarget_nonneg := Causalean.Stat.cdfKolmogorov_nonneg
    (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
    (samplingEstimatorLaw S est theta0 h.meas.1 n)
  have hsum_nonneg : 0 ≤
      Causalean.Stat.cdfKolmogorov
          (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
          h.asymptoticGaussian +
        Causalean.Stat.cdfKolmogorov h.asymptoticGaussian
          (samplingEstimatorLaw S est theta0 h.meas.1 n) :=
    add_nonneg (Causalean.Stat.cdfKolmogorov_nonneg _ _)
      (Causalean.Stat.cdfKolmogorov_nonneg _ _)
  rw [abs_of_nonneg htarget_nonneg] at homega
  rw [abs_of_nonneg hsum_nonneg]
  exact homega.trans (cdfKolmogorov_triangle _ _ _)

/-- Given [a bootstrap-asymptotically-linear estimator](hyp:h) and [an interior probability
level](hyp:hbeta0,hbeta1), [its lower conditional bootstrap quantile converges in sampling
probability to the corresponding centered-Gaussian quantile](goal). -/
theorem quantile_tendsto (h : BootstrapAsymLinear S est theta0 psi)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    Tendsto_inProb
      (fun n omega => bootstrapQuantile est n beta (S.sampleVector n omega))
      (fun _ => Real.sqrt h.asymptoticVariance * Causalean.Mathlib.probit beta) mu := by
  -- Apply `quantile_tendsto_inProb_of_cdfKolmogorov` to `bootstrap_tendsto_gaussian`, use the
  -- measurable-quantile theorem and the eventual identity with `bootstrapEstimatorLaw`, then
  -- evaluate the Gaussian quantile by `quantile_gaussianReal_zero`.
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hvReal : 0 < h.asymptoticVariance := h.var_pos_finite.1
  have hv : 0 < h.asymptoticVariance.toNNReal := by
    rwa [Real.toNNReal_pos]
  let G : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 h.asymptoticVariance.toNNReal, inferInstance⟩
  have hG : h.asymptoticGaussian = G := by
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  have hx (n : ℕ) : Measurable (fun omega => S.sampleVector n omega) := by
    apply measurable_pi_iff.mpr
    intro i
    exact S.meas i
  have hqMeas (n : ℕ) : Measurable (fun omega =>
      Causalean.Stat.quantile
        (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega) : Measure ℝ) beta) := by
    by_cases hn : n = 0
    · subst n
      simp only [bootstrapEstimatorLaw, ↓reduceDIte]
      exact measurable_const
    · rw [show (fun omega => Causalean.Stat.quantile
            (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega) : Measure ℝ)
            beta) =
          fun omega => bootstrapQuantile est n beta (S.sampleVector n omega) by
          funext omega
          exact (bootstrapQuantile_eq_quantile_bootstrapEstimatorLaw est h.meas.1
            (bne_iff_ne.mpr hn) hbeta0 hbeta1 (S.sampleVector n omega)).symm]
      exact (measurable_bootstrapQuantile est h.meas.1 n hbeta0 hbeta1).comp (hx n)
  have hquantLaw : Tendsto_inProb
      (fun n omega => Causalean.Stat.quantile
        (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega) : Measure ℝ) beta)
      (fun _ => Causalean.Stat.quantile (G : Measure ℝ) beta) mu := by
    apply quantile_tendsto_inProb_of_cdfKolmogorov
      (nu := fun n omega => bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega))
      G hbeta0 hbeta1
    · exact (Causalean.Stat.continuous_cdf_gaussianReal_zero hv).continuousAt
    · have hstrict := Causalean.Stat.strictMono_cdf_gaussianReal_zero hv
      exact ⟨fun x hx => hstrict hx, fun x hx => hstrict hx⟩
    · exact hqMeas
    · simpa only [← hG] using bootstrap_tendsto_gaussian h
  unfold Tendsto_inProb at hquantLaw ⊢
  apply TendstoInMeasure.congr'
    (f := fun n omega => Causalean.Stat.quantile
      (bootstrapEstimatorLaw est h.meas.1 n (S.sampleVector n omega) : Measure ℝ) beta)
    (g := fun _ => Causalean.Stat.quantile (G : Measure ℝ) beta) _ _ hquantLaw
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact Filter.Eventually.of_forall fun omega =>
      (bootstrapQuantile_eq_quantile_bootstrapEstimatorLaw est h.meas.1
        (bne_iff_ne.mpr hn) hbeta0 hbeta1 (S.sampleVector n omega)).symm
  · exact Filter.Eventually.of_forall fun omega => by
      dsimp [G]
      rw [Causalean.Stat.quantile_gaussianReal_zero hv hbeta0 hbeta1]
      rw [Real.coe_toNNReal _ hvReal.le]

end BootstrapAsymLinear

end

end Causalean.Stat

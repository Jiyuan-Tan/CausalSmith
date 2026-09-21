module

public import Causalean.Stat.Bootstrap.EfronResampling.Mean.AlmostSure
public import Causalean.Stat.Quantile.CdfConvergence
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Same-size Bickel--Freedman consistency for the Efron bootstrap mean

This module formalizes the same-size specialization of the Bickel--Freedman mean result: the
observed sample and the Efron resample both have size `n`.  For a measurable real statistic of iid
observations with a finite second moment, the conditional bootstrap distribution of the centered
root-sample-size mean converges almost surely to the centered Gaussian with the population
variance.  At positive variance it is also uniformly close, in Kolmogorov distance, to the true
finite-sample distribution.  The final declarations specialize the result to real-valued
observations and the identity statistic.
-/

public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- Given [an iid sample](hyp:S), [a measurable observation statistic](hyp:ψ,hψ), and [an
integrable population square](hyp:hψ2), [the sampling laws of the square-root-scaled centered
sample mean converge to the centered Gaussian with the population variance](goal). -/
theorem samplingMeanLaw_tendsto_gaussian
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    Tendsto (samplingMeanLaw S ψ hψ) atTop
      (𝓝 (⟨gaussianReal 0 (populationVariance ψ P), inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hψmem : MemLp ψ 2 P :=
    (memLp_two_iff_integrable_sq hψ.aestronglyMeasurable).2 hψ2
  have hZ0 : MeasurePreserving (S.Z 0) μ P := ⟨S.meas 0, S.law⟩
  have hmem : MemLp (ψ ∘ S.Z 0) 2 μ := hψmem.comp_measurePreserving hZ0
  have hindep : iIndepFun (fun i ↦ ψ ∘ S.Z i) μ :=
    S.indep.comp (fun _ ↦ ψ) (fun _ ↦ hψ)
  have hident : ∀ i, IdentDistrib (ψ ∘ S.Z i) (ψ ∘ S.Z 0) μ μ := by
    intro i
    exact (S.identDist i).symm.comp hψ
  have hint : ∫ ω, ψ (S.Z 0 ω) ∂μ = ∫ x, ψ x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hψ.aestronglyMeasurable, S.law]
  have hvar : ProbabilityTheory.variance (ψ ∘ S.Z 0) μ =
      ProbabilityTheory.variance ψ P := by
    apply IdentDistrib.variance_eq
    refine ⟨(hψ.comp (S.meas 0)).aemeasurable, hψ.aemeasurable, ?_⟩
    rw [← Measure.map_map hψ (S.meas 0), S.law]
  let G : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (populationVariance ψ P), inferInstance⟩
  have hG : HasLaw id
      (gaussianReal 0 (ProbabilityTheory.variance (ψ ∘ S.Z 0) μ).toNNReal)
      (G : Measure ℝ) := by
    simpa [G, populationVariance, hvar] using (HasLaw.id (μ := (G : Measure ℝ)))
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ↦ ψ ∘ S.Z i) (P := μ) (P' := (G : Measure ℝ)) (Y := id)
    hG hmem hindep hident
  have heq : (fun n : ℕ ↦
      (⟨μ.map (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ *
          (∑ k ∈ Finset.range n, (ψ ∘ S.Z k) ω -
            (n : ℝ) * ∫ x, (ψ ∘ S.Z 0) x ∂μ)),
        Measure.isProbabilityMeasure_map (by fun_prop)⟩ : ProbabilityMeasure ℝ)) =ᶠ[atTop]
      samplingMeanLaw S ψ hψ := by
    filter_upwards with n
    apply ProbabilityMeasure.toMeasure_injective
    simp only [samplingMeanLaw, ProbabilityMeasure.coe_mk]
    congr 1
    funext ω
    unfold IIDSample.sampleMean
    simp only [Function.comp_apply]
    rw [hint]
    by_cases hn : n = 0
    · subst n
      simp
    · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have ht := hclt.tendsto.congr' heq
  have hmap :
      (⟨Measure.map id (G : Measure ℝ), Measure.isProbabilityMeasure_map (by fun_prop)⟩ :
        ProbabilityMeasure ℝ) = G := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_id
  rw [hmap] at ht
  change Tendsto (samplingMeanLaw S ψ hψ) atTop (𝓝 G)
  exact ht

/-- Given [an iid sample](hyp:S), [a measurable observation statistic](hyp:ψ,hψ), and [an
integrable population square](hyp:hψ2), [the conditional Efron-bootstrap law of the
square-root-scaled centered mean converges almost surely to the centered Gaussian with the
population variance](goal). -/
theorem bootstrapMeanLaw_tendsto_gaussian_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ bootstrapMeanLaw S ψ hψ n ω) atTop
        (𝓝 (⟨gaussianReal 0 (populationVariance ψ P), inferInstance⟩ :
          ProbabilityMeasure ℝ)) := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  filter_upwards [centeredEmpiricalSecondMoment_tendsto_ae S ψ hψ hψ2,
    centeredEmpiricalLindeberg_tendsto_ae S ψ hψ hψ2] with ω hsecond hlindeberg
  have hcenter : ∀ n,
      ∫ x, x ∂centeredEmpiricalLaw S ψ n ω = 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [centeredEmpiricalLaw]
    · exact integral_id_centeredEmpiricalLaw hn S ψ ω
  have hsecond' : Tendsto
      (fun n : ℕ ↦ ∫ x, x ^ 2 ∂centeredEmpiricalLaw S ψ n ω)
      atTop (𝓝 ((populationVariance ψ P : NNReal) : ℝ)) := by
    simpa [populationVariance, Real.toNNReal_of_nonneg (variance_nonneg ψ P)] using hsecond
  have hrow := Causalean.Stat.iidRowNormalizedSumLaw_tendsto_gaussian
    (fun n ↦ centeredEmpiricalLaw S ψ n ω) (populationVariance ψ P)
    (fun n ↦ memLp_id_centeredEmpiricalLaw S ψ n ω) hcenter hsecond' hlindeberg
  apply hrow.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (bootstrapMeanLaw_eq_iidRowNormalizedSumLaw hn S ψ hψ ω).symm

/-- Given [an iid sample](hyp:S), [a measurable observation statistic](hyp:ψ,hψ), [an
integrable population square](hyp:hψ2), and [strictly positive population variance](hyp:hvar),
[the conditional bootstrap and sampling laws approach one another almost surely in Kolmogorov
distance](goal). -/
theorem bootstrapMeanLaw_cdfKolmogorov_samplingMeanLaw_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P)
    (hvar : 0 < ProbabilityTheory.variance ψ P) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ Causalean.Stat.cdfKolmogorov
          (bootstrapMeanLaw S ψ hψ n ω) (samplingMeanLaw S ψ hψ n))
        atTop (𝓝 0) := by
  have hvar' : 0 < populationVariance ψ P := by
    simpa [populationVariance, Real.toNNReal_pos] using hvar
  filter_upwards [bootstrapMeanLaw_tendsto_gaussian_ae S ψ hψ hψ2] with ω hboot
  exact Causalean.Stat.tendsto_cdfKolmogorov_of_tendsto hboot
    (samplingMeanLaw_tendsto_gaussian S ψ hψ hψ2)
    (Causalean.Stat.continuous_cdf_gaussianReal_zero hvar')

/-- Given [an iid sample of real observations](hyp:S) whose [population square is integrable](hyp:hX2),
[the Efron-bootstrap law of its centered mean converges almost surely to the centered Gaussian
with the population variance](goal). -/
theorem bootstrapRealMeanLaw_tendsto_gaussian_ae
    {P : Measure ℝ}
    (S : IIDSample Ω ℝ μ P)
    (hX2 : Integrable (fun x : ℝ ↦ x ^ 2) P) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ bootstrapMeanLaw S id measurable_id n ω) atTop
        (𝓝 (⟨gaussianReal 0 (populationVariance id P), inferInstance⟩ :
          ProbabilityMeasure ℝ)) := by
  exact bootstrapMeanLaw_tendsto_gaussian_ae S id measurable_id hX2

/-- Given [an iid sample of real observations](hyp:S) with [an integrable population square](hyp:hX2)
and [strictly positive population variance](hyp:hvar), [the Efron-bootstrap and sampling laws of
the centered mean approach one another almost surely in Kolmogorov distance](goal). -/
theorem bootstrapRealMeanLaw_cdfKolmogorov_samplingMeanLaw_tendsto_ae
    {P : Measure ℝ}
    (S : IIDSample Ω ℝ μ P)
    (hX2 : Integrable (fun x : ℝ ↦ x ^ 2) P)
    (hvar : 0 < ProbabilityTheory.variance id P) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ Causalean.Stat.cdfKolmogorov
          (bootstrapMeanLaw S id measurable_id n ω)
          (samplingMeanLaw S id measurable_id n))
        atTop (𝓝 0) := by
  exact bootstrapMeanLaw_cdfKolmogorov_samplingMeanLaw_tendsto_ae
    S id measurable_id hX2 hvar

end

end Causalean.Stat

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Fibre

/-!
# Shared-prior random-scale Poisson predictive transfer

This module compares fixed-size iid prior predictives with finite-Poisson
prior predictives whose intensity varies with a shared latent parameter.  A
single ordered-prefix map transfers both experiments, and the error is the
prior-average probability of a short Poisson count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer

variable {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]

/-- The [fixed-size predictive](goal) averages iid samples of [length n](hyp:n)
from [a parameter-dependent mark kernel](hyp:P) over [a shared prior](hyp:pi).

The average is the intended mixture when the map from parameters to iid sample laws is almost
everywhere measurable under the prior; otherwise it is the zero measure by convention.
-/
noncomputable def fixedMixture (pi : Measure Theta) (P : Kernel Theta X)
    [∀ theta, IsProbabilityMeasure (P theta)] (n : ℕ) : Measure (Fin n → X) :=
  pi.bind (fun theta => Measure.pi (fun _ : Fin n => P theta))

/-- The [raw finite-Poisson predictive](goal) averages [a mark kernel](hyp:P)
over [a shared prior](hyp:pi), using [an intensity multiplier](hyp:u) times
[the parameter's nonnegative scale](hyp:S) as its conditional intensity.

The average is the intended mixture when the map from parameters to finite Poisson sample laws is
almost everywhere measurable under the prior; otherwise it is the zero measure by convention.
-/
noncomputable def rawMixture (pi : Measure Theta) (P : Kernel Theta X)
    [∀ theta, IsProbabilityMeasure (P theta)] (S : Theta → ℝ≥0) (u : ℝ≥0) :
    Measure (FiniteSample X) :=
  pi.bind (fun theta => finitePoissonSampleLaw (P theta) (u * S theta))

/-- Under [measurability of the raw fibres](hyp:hraw), applying [one fixed
fallback prefix](hyp:fallback) to [the prior](hyp:pi) mixture of [a mark
kernel](hyp:P) with [scale](hyp:S) and [multiplier](hyp:u) [equals mixing the
fibrewise prefix pushforwards](goal).
-/
theorem map_orderedPrefix_rawMixture
    (pi : Measure Theta) (P : Kernel Theta X)
    [∀ theta, IsProbabilityMeasure (P theta)] (S : Theta → ℝ≥0) (u : ℝ≥0)
    {n : ℕ} (fallback : Fin n → X)
    (hraw : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P theta) (u * S theta)) pi) :
    Measure.map (orderedPrefix fallback) (rawMixture pi P S u) =
      pi.bind (fun theta => Measure.map (orderedPrefix fallback)
        (finitePoissonSampleLaw (P theta) (u * S theta))) := by
  unfold rawMixture Measure.bind
  rw [← Measure.join_map_map (measurable_orderedPrefix fallback),
    (Measure.measurable_map _ (measurable_orderedPrefix fallback)).aemeasurable
      |>.map_map_of_aemeasurable hraw]
  rfl

/-- For [a probability prior](hyp:pi), [a probability mark kernel](hyp:P),
[a latent scale](hyp:S), [a nonnegative multiplier](hyp:u),
[a sample size and fallback](hyp:n,fallback), and [measurable fixed and raw
fibres](hyp:hfixed,hraw), [the fixed predictive differs from the retained raw
predictive in TV by at most the prior-average short-count probability](goal).
-/
theorem tvDist_fixedMixture_map_rawMixture_le
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (P : Kernel Theta X) [∀ theta, IsProbabilityMeasure (P theta)]
    (S : Theta → ℝ≥0) (u : ℝ≥0)
    (n : ℕ) (fallback : Fin n → X)
    (hfixed : AEMeasurable
      (fun theta => Measure.pi (fun _ : Fin n => P theta)) pi)
    (hraw : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P theta) (u * S theta)) pi) :
    Causalean.Stat.tvDist (fixedMixture pi P n)
        (Measure.map (orderedPrefix fallback) (rawMixture pi P S u)) ≤
      ∫ theta, (poissonMeasure (u * S theta) (Set.Iio n)).toReal ∂pi := by
  have hf := measurable_orderedPrefix fallback
  let bad : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Iio n
  have hbad : MeasurableSet bad :=
    (by measurability : MeasurableSet (Set.Iio n)).preimage measurable_finiteSample_count
  have hcount (theta : Theta) :
      finitePoissonSampleLaw (P theta) (u * S theta) bad =
        poissonMeasure (u * S theta) (Set.Iio n) := by
    rw [← finitePoissonSampleLaw_map_count (P theta) (u * S theta),
      Measure.map_apply measurable_finiteSample_count (by measurability)]
  have hfailure : AEMeasurable
      (fun theta => poissonMeasure (u * S theta) (Set.Iio n)) pi := by
    simpa only [Function.comp_def, hcount] using
      (Measure.measurable_coe hbad).comp_aemeasurable hraw
  have ifailure : Integrable
      (fun theta => (poissonMeasure (u * S theta) (Set.Iio n)).toReal) pi := by
    apply (integrable_const (1 : ℝ)).mono' hfailure.ennreal_toReal.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  let B := orderedPrefix fallback ⁻¹' A
  have hB : MeasurableSet B := hA.preimage hf
  have hmfixed := (Measure.measurable_coe hA).comp_aemeasurable hfixed
  have hmraw := (Measure.measurable_coe hB).comp_aemeasurable hraw
  have ifixed : Integrable
      (fun theta => (Measure.pi (fun _ : Fin n => P theta)).real A) pi := by
    apply (integrable_const (1 : ℝ)).mono' hmfixed.ennreal_toReal.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
  have iraw : Integrable
      (fun theta => (finitePoissonSampleLaw (P theta) (u * S theta)).real B) pi := by
    apply (integrable_const (1 : ℝ)).mono' hmraw.ennreal_toReal.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun theta => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
  have efixed : (fixedMixture pi P n).real A =
      ∫ theta, (Measure.pi (fun _ : Fin n => P theta)).real A ∂pi := by
    rw [fixedMixture, measureReal_def, Measure.bind_apply hA hfixed]
    exact (integral_toReal hmfixed
      (Filter.Eventually.of_forall fun theta => measure_lt_top _ _)).symm
  have eraw : (Measure.map (orderedPrefix fallback) (rawMixture pi P S u)).real A =
      ∫ theta, (finitePoissonSampleLaw (P theta) (u * S theta)).real B ∂pi := by
    rw [map_measureReal_apply hf hA, rawMixture, measureReal_def,
      Measure.bind_apply hB hraw]
    exact (integral_toReal hmraw
      (Filter.Eventually.of_forall fun theta => measure_lt_top _ _)).symm
  change |(fixedMixture pi P n).real A -
    (Measure.map (orderedPrefix fallback) (rawMixture pi P S u)).real A| ≤ _
  rw [efixed, eraw, ← integral_sub ifixed iraw]
  refine (abs_integral_le_integral_abs).trans (integral_mono (ifixed.sub iraw).abs ifailure ?_)
  intro theta
  let : IsProbabilityMeasure (Measure.map (orderedPrefix fallback)
      (finitePoissonSampleLaw (P theta) (u * S theta))) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  change |(Measure.pi (fun _ : Fin n => P theta)).real A -
    (finitePoissonSampleLaw (P theta) (u * S theta)).real B| ≤
      (poissonMeasure (u * S theta) (Set.Iio n)).toReal
  rw [show (finitePoissonSampleLaw (P theta) (u * S theta)).real B =
    (Measure.map (orderedPrefix fallback)
      (finitePoissonSampleLaw (P theta) (u * S theta))).real A from
        (map_measureReal_apply hf hA).symm]
  exact (Causalean.Stat.abs_measureReal_sub_le_tvDist hA).trans
    (tvDist_iid_map_orderedPrefix_le (P theta) (u * S theta) fallback)

/-- Given [two probability mark kernels](hyp:P0,P1) over [one probability
prior](hyp:pi), [a measurable shared scale](hyp:S,hS), [an intensity
multiplier](hyp:u), [a sample size and common fallback](hyp:n,fallback), and
[measurable fixed and raw fibres on both sides](hyp:hfixed0,hfixed1,hraw0,hraw1),
[the total-variation distance between the two fixed-size predictives is at most
the total-variation distance between the two raw finite-Poisson predictives plus twice the
prior average of the Poisson probability that the count is below the sample size](goal).

The same ordered-prefix map is used on both sides and remains valid at zero
intensity and for a zero-length prefix. -/
theorem fixedMixture_tv_le_randomScalePoisson
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (P0 P1 : Kernel Theta X)
    [∀ theta, IsProbabilityMeasure (P0 theta)]
    [∀ theta, IsProbabilityMeasure (P1 theta)]
    (S : Theta → ℝ≥0) (hS : Measurable S) (u : ℝ≥0)
    (n : ℕ) (fallback : Fin n → X)
    (hfixed0 : AEMeasurable
      (fun theta => Measure.pi (fun _ : Fin n => P0 theta)) pi)
    (hfixed1 : AEMeasurable
      (fun theta => Measure.pi (fun _ : Fin n => P1 theta)) pi)
    (hraw0 : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P0 theta) (u * S theta)) pi)
    (hraw1 : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P1 theta) (u * S theta)) pi) :
    Causalean.Stat.tvDist (fixedMixture pi P0 n) (fixedMixture pi P1 n) ≤
      Causalean.Stat.tvDist (rawMixture pi P0 S u) (rawMixture pi P1 S u) +
        2 * ∫ theta, (poissonMeasure (u * S theta) (Set.Iio n)).toReal ∂pi := by
  let f := orderedPrefix fallback
  let mu0 := fixedMixture pi P0 n
  let mu1 := fixedMixture pi P1 n
  let rho0 := rawMixture pi P0 S u
  let rho1 := rawMixture pi P1 S u
  let : IsProbabilityMeasure mu0 := isProbabilityMeasure_bind hfixed0
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let : IsProbabilityMeasure mu1 := isProbabilityMeasure_bind hfixed1
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let : IsProbabilityMeasure rho0 := isProbabilityMeasure_bind hraw0
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let : IsProbabilityMeasure rho1 := isProbabilityMeasure_bind hraw1
    (Filter.Eventually.of_forall fun _ => inferInstance)
  have hf : Measurable f := measurable_orderedPrefix fallback
  let : IsProbabilityMeasure (Measure.map f rho0) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure (Measure.map f rho1) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have herr0 := tvDist_fixedMixture_map_rawMixture_le pi P0 S u n fallback hfixed0 hraw0
  have herr1 := tvDist_fixedMixture_map_rawMixture_le pi P1 S u n fallback hfixed1 hraw1
  have hcontract : Causalean.Stat.tvDist (Measure.map f rho0) (Measure.map f rho1) ≤
      Causalean.Stat.tvDist rho0 rho1 := by
    simpa only [Measure.deterministic_comp_eq_map] using
      Causalean.Stat.tvDist_bind_le rho0 rho1 (Kernel.deterministic f hf)
  change Causalean.Stat.tvDist mu0 mu1 ≤ _
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  change |mu0.real A - mu1.real A| ≤ Causalean.Stat.tvDist rho0 rho1 +
    2 * ∫ theta, (poissonMeasure (u * S theta) (Set.Iio n)).toReal ∂pi
  have h0 := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := mu0) (ν := Measure.map f rho0) hA).trans herr0
  have h1 := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := mu1) (ν := Measure.map f rho1) hA).trans herr1
  have hc := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := Measure.map f rho0) (ν := Measure.map f rho1) hA).trans hcontract
  have htri := abs_sub_le (mu0.real A) ((Measure.map f rho0).real A) (mu1.real A)
  have htri' := abs_sub_le ((Measure.map f rho0).real A)
    ((Measure.map f rho1).real A) (mu1.real A)
  rw [abs_sub_comm ((Measure.map f rho1).real A) (mu1.real A)] at htri'
  linarith

end Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer

module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.CorrectionMoments
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw

/-! Poissonized classifier-cell counts and threshold probabilities. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

noncomputable def finiteSampleCellCount {n : ℕ}
    (s : FiniteSample (SampleObs n)) (k : Fin n) : ℕ :=
  finiteSampleHistogram (fun i => (s.points i).x) k

lemma measurable_sampleObs_x {n : ℕ} :
    Measurable (fun o : SampleObs n => o.x) := by
  exact measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)

lemma measurable_finiteSampleHistogram {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X] :
    Measurable (fun s : FiniteSample X => finiteSampleHistogram s.points) := by
  apply measurable_to_countable'
  intro c
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((Sigma.mk m) ⁻¹'
    {s : FiniteSample X | finiteSampleHistogram s.points = c})
  exact (Set.to_countable _).measurableSet

lemma measurable_finiteSampleCellCount {n : ℕ} (k : Fin n) :
    Measurable (fun s : FiniteSample (SampleObs n) => finiteSampleCellCount s k) := by
  let F : FiniteSample (SampleObs n) → FiniteSample (Fin n) :=
    finiteSampleMap (fun o => o.x)
  let H : FiniteSample (Fin n) → (Fin n → ℕ) :=
    fun s => finiteSampleHistogram s.points
  have hF : Measurable F := measurable_finiteSampleMap _ measurable_sampleObs_x
  have hH : Measurable H := measurable_finiteSampleHistogram
  exact (measurable_pi_apply k).comp (hH.comp hF)

lemma map_covariate_observedLaw_singleton_toNNReal (P : Law n) (k : Fin n) :
    ((Measure.map (fun o : SampleObs n => o.x) P.observedLaw) {k}).toNNReal =
      Real.toNNReal (P.cellMass k) := by
  apply NNReal.eq
  rw [ENNReal.coe_toNNReal_eq_toReal,
    Real.coe_toNNReal (P.cellMass k) (P.cellMass_range k).1]
  rw [Measure.map_apply measurable_sampleObs_x (MeasurableSet.singleton k)]
  have hevent : (fun o : SampleObs n => o.x) ⁻¹' ({k} : Set (Fin n)) =
      {o : SampleObs n | o.x = k} := by
    ext o
    simp
  rw [hevent]
  simpa [DiscreteAteHeterogeneityFrontier.realMass] using (P.cellMass_eq k).symm

/-- A cell count in a finite Poisson classifier sample is Poisson with rate
`lambda * cellMass`. -/
lemma map_finiteSampleCellCount_finitePoissonSampleLaw (P : Law n)
    (lam : ℝ≥0) (k : Fin n) :
    Measure.map (fun s : FiniteSample (SampleObs n) => finiteSampleCellCount s k)
        (finitePoissonSampleLaw P.observedLaw lam) =
      poissonMeasure (lam * Real.toNNReal (P.cellMass k)) := by
  let Q := Measure.map (fun o : SampleObs n => o.x) P.observedLaw
  let F : FiniteSample (SampleObs n) → FiniteSample (Fin n) :=
    finiteSampleMap (fun o => o.x)
  let H : FiniteSample (Fin n) → (Fin n → ℕ) :=
    fun s => finiteSampleHistogram s.points
  have hF : Measurable F := measurable_finiteSampleMap _ measurable_sampleObs_x
  have hH : Measurable H := measurable_finiteSampleHistogram
  have hfactor : (fun s : FiniteSample (SampleObs n) => finiteSampleCellCount s k) =
      Function.eval k ∘ H ∘ F := by
    funext s
    rfl
  letI : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map measurable_sampleObs_x.aemeasurable
  rw [hfactor]
  calc
    Measure.map (Function.eval k ∘ H ∘ F)
          (finitePoissonSampleLaw P.observedLaw lam) =
        Measure.map (Function.eval k)
          (Measure.map H (Measure.map F
            (finitePoissonSampleLaw P.observedLaw lam))) := by
              rw [Measure.map_map hH hF,
                Measure.map_map (measurable_pi_apply k) (hH.comp hF)]
    _ = Measure.map (Function.eval k)
          (Measure.map H (finitePoissonSampleLaw Q lam)) := by
            rw [map_finitePoissonSampleLaw_finiteSampleMap_local
              P.observedLaw (fun o : SampleObs n => o.x) measurable_sampleObs_x lam]
    _ = Measure.map (Function.eval k) (independentPoissonCountLaw Q lam) := by
      rw [finitePoissonSampleLaw_map_histogram Q lam]
    _ = poissonMeasure (lam * (Q {k}).toNNReal) := by
      unfold independentPoissonCountLaw
      rw [Measure.pi_map_eval]
      simp
    _ = poissonMeasure (lam * Real.toNNReal (P.cellMass k)) := by
      rw [map_covariate_observedLaw_singleton_toNNReal]

/-- The expectation of the implemented light-cell indicator under the
Poissonized classifier sample is the audit classification probability. -/
lemma classifierThreshold_integral (n : ℕ) (rho : ℝ) (P : Law n) (k : Fin n) :
    (∫ s : FiniteSample (SampleObs n),
      (if finiteSampleCellCount s k ≤ 256 * degree n rho then (1 : ℝ) else 0)
      ∂finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))) =
      classificationProbability n rho P k := by
  let f : ℕ → ℝ := fun q => if q ≤ 256 * degree n rho then 1 else 0
  rw [← integral_map (measurable_finiteSampleCellCount k).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [map_finiteSampleCellCount_finitePoissonSampleLaw]
  unfold classificationProbability
  rw [← Real.toNNReal_mul (show 0 ≤ blockMean n by
    unfold blockMean
    positivity)]
  have hf : f = ({q : ℕ | q ≤ 256 * degree n rho}).indicator
      (fun _ => (1 : ℝ)) := by
    funext q
    simp [f, indicator_apply]
  rw [hf]
  let A : Set ℕ := {q : ℕ | q ≤ 256 * degree n rho}
  have hA : MeasurableSet A := measurableSet_le measurable_id measurable_const
  calc
    (∫ y : ℕ, A.indicator (fun _ => (1 : ℝ)) y
        ∂poissonMeasure (Real.toNNReal (blockMean n * P.cellMass k))) =
        (poissonMeasure (Real.toNNReal (blockMean n * P.cellMass k))).real A •
          (1 : ℝ) := integral_indicator_const 1 hA
    _ = (poissonMeasure (Real.toNNReal (blockMean n * P.cellMass k)) A).toReal := by
      simp [measureReal_def]

/-- Integrating a two-branch scalar choice over the classifier sample gives
the Bernoulli mixture with the audit classification probability. -/
lemma classifierThreshold_choice_integral (n : ℕ) (rho : ℝ) (P : Law n)
    (k : Fin n) (light heavy : ℝ) :
    (∫ s : FiniteSample (SampleObs n),
      (if finiteSampleCellCount s k ≤ 256 * degree n rho then light else heavy)
      ∂finitePoissonSampleLaw P.observedLaw (Real.toNNReal (blockMean n))) =
      classificationProbability n rho P k * light +
        (1 - classificationProbability n rho P k) * heavy := by
  let I : FiniteSample (SampleObs n) → ℝ := fun s =>
    if finiteSampleCellCount s k ≤ 256 * degree n rho then 1 else 0
  let μ := finitePoissonSampleLaw P.observedLaw (Real.toNNReal (blockMean n))
  have hset : MeasurableSet {s : FiniteSample (SampleObs n) |
      finiteSampleCellCount s k ≤ 256 * degree n rho} :=
    measurableSet_le (measurable_finiteSampleCellCount k) measurable_const
  have hI : Integrable I
      μ := by
    apply Integrable.of_bound
      (Measurable.ite hset measurable_const measurable_const).aestronglyMeasurable
      1
    filter_upwards [] with s
    dsimp [I]
    split_ifs <;> simp
  have hrewrite : (fun s : FiniteSample (SampleObs n) =>
      if finiteSampleCellCount s k ≤ 256 * degree n rho then light else heavy) =
      fun s => I s * light + (1 - I s) * heavy := by
    funext s
    dsimp [I]
    split_ifs <;> ring
  have hOne : Integrable (fun _ : FiniteSample (SampleObs n) => (1 : ℝ)) μ :=
    integrable_const 1
  have hsubFun : (fun s : FiniteSample (SampleObs n) => 1 - I s) =
      (fun _ => (1 : ℝ)) - I := by
    funext s
    rfl
  have hsub : Integrable (fun s : FiniteSample (SampleObs n) => 1 - I s) μ := by
    rw [hsubFun]
    exact hOne.sub hI
  rw [hrewrite]
  change (∫ s, I s * light + (1 - I s) * heavy ∂μ) = _
  rw [integral_add (hI.mul_const light) (hsub.mul_const heavy),
    integral_mul_const, integral_mul_const]
  have hsubMean : (∫ s, 1 - I s ∂μ) = 1 - ∫ s, I s ∂μ := by
    rw [hsubFun]
    calc
      integral μ ((fun _ => (1 : ℝ)) - I) =
          integral μ (fun _ => (1 : ℝ)) - integral μ I :=
        integral_sub hOne hI
      _ = 1 - integral μ I := by simp
  rw [hsubMean]
  have hImean : (∫ s, I s
      ∂finitePoissonSampleLaw P.observedLaw (Real.toNNReal (blockMean n))) =
      classificationProbability n rho P k := by
    simpa only [I] using classifierThreshold_integral n rho P k
  rw [hImean]

/-- The same classifier identity applied to squared branch values. -/
-- keep: exact second-moment identity for an independently thresholded branch
lemma classifierThreshold_choice_sq_integral (n : ℕ) (rho : ℝ) (P : Law n)
    (k : Fin n) (light heavy : ℝ) :
    (∫ s : FiniteSample (SampleObs n),
      (if finiteSampleCellCount s k ≤ 256 * degree n rho then light else heavy) ^ 2
      ∂finitePoissonSampleLaw P.observedLaw (Real.toNNReal (blockMean n))) =
      classificationProbability n rho P k * light ^ 2 +
        (1 - classificationProbability n rho P k) * heavy ^ 2 := by
  rw [show (fun s : FiniteSample (SampleObs n) =>
      (if finiteSampleCellCount s k ≤ 256 * degree n rho then light else heavy) ^ 2) =
      fun s => if finiteSampleCellCount s k ≤ 256 * degree n rho then
        light ^ 2 else heavy ^ 2 by
    funext s
    split_ifs <;> rfl]
  exact classifierThreshold_choice_integral n rho P k (light ^ 2) (heavy ^ 2)

lemma classifierEstimation_choice_integrable {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (rho : ℝ) (P : Law n) (k : Fin n) (ν : Measure Y) [SFinite ν]
    (light heavy : Y → ℝ) (hlightMeas : Measurable light)
    (hheavyMeas : Measurable heavy) (hlight : Integrable light ν)
    (hheavy : Integrable heavy ν) :
    Integrable (fun p : FiniteSample (SampleObs n) × Y =>
      if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod ν) := by
  let μ := finitePoissonSampleLaw P.observedLaw (Real.toNNReal (blockMean n))
  have hset : MeasurableSet {p : FiniteSample (SampleObs n) × Y |
      finiteSampleCellCount p.1 k ≤ 256 * degree n rho} :=
    measurableSet_le ((measurable_finiteSampleCellCount k).comp measurable_fst)
      measurable_const
  have hmeas : Measurable (fun p : FiniteSample (SampleObs n) × Y =>
      if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2) :=
    Measurable.ite hset (hlightMeas.comp measurable_snd)
      (hheavyMeas.comp measurable_snd)
  have hmajor := (hlight.norm.comp_snd μ).add (hheavy.norm.comp_snd μ)
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with p
  split_ifs <;> simp [norm_nonneg]

/-- Product-law aggregation of an independent classifier and two correction
branches.  Integrability is exposed as a hypothesis so the correction moment
modules can discharge it with their second-moment envelopes. -/
lemma classifierEstimation_choice_integral {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (rho : ℝ) (P : Law n) (k : Fin n) (ν : Measure Y) [SFinite ν]
    (light heavy : Y → ℝ)
    (hsel : Integrable (fun p : FiniteSample (SampleObs n) × Y =>
      if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod ν)) :
    (∫ p : FiniteSample (SampleObs n) × Y,
      (if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2)
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod ν)) =
      classificationProbability n rho P k * (∫ y, light y ∂ν) +
        (1 - classificationProbability n rho P k) * (∫ y, heavy y ∂ν) := by
  rw [integral_prod _ hsel]
  have hinner (s : FiniteSample (SampleObs n)) :
      (∫ y, (if finiteSampleCellCount s k ≤ 256 * degree n rho then
        light y else heavy y) ∂ν) =
      if finiteSampleCellCount s k ≤ 256 * degree n rho then
        (∫ y, light y ∂ν) else (∫ y, heavy y ∂ν) := by
    split_ifs <;> rfl
  simp_rw [hinner]
  exact classifierThreshold_choice_integral n rho P k
    (∫ y, light y ∂ν) (∫ y, heavy y ∂ν)

/-- Product-law second moment of the independently selected correction. -/
lemma classifierEstimation_choice_sq_integral {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (rho : ℝ) (P : Law n) (k : Fin n) (ν : Measure Y) [SFinite ν]
    (light heavy : Y → ℝ)
    (hsel : Integrable (fun p : FiniteSample (SampleObs n) × Y =>
      (if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2) ^ 2)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod ν)) :
    (∫ p : FiniteSample (SampleObs n) × Y,
      (if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        light p.2 else heavy p.2) ^ 2
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod ν)) =
      classificationProbability n rho P k * (∫ y, (light y) ^ 2 ∂ν) +
        (1 - classificationProbability n rho P k) *
          (∫ y, (heavy y) ^ 2 ∂ν) := by
  rw [integral_prod _ hsel]
  have hinner (s : FiniteSample (SampleObs n)) :
      (∫ y, (if finiteSampleCellCount s k ≤ 256 * degree n rho then
        light y else heavy y) ^ 2 ∂ν) =
      if finiteSampleCellCount s k ≤ 256 * degree n rho then
        (∫ y, (light y) ^ 2 ∂ν) else (∫ y, (heavy y) ^ 2 ∂ν) := by
    split_ifs <;> rfl
  simp_rw [hinner]
  exact classifierThreshold_choice_integral n rho P k
    (∫ y, (light y) ^ 2 ∂ν) (∫ y, (heavy y) ^ 2 ∂ν)

noncomputable def idealSelectedCorrection {n : ℕ} (P : Law n) (k : Fin n)
    (t rho : ℝ)
    (p : FiniteSample (SampleObs n) × (FiniteSample ℝ × FiniteSample ℝ)) : ℝ :=
  if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
    idealLightCorrection P k t rho p.2 else idealHeavyCorrection P k t p.2

lemma idealSelectedCorrection_integrable {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    Integrable (idealSelectedCorrection P k t rho)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)) := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  unfold idealSelectedCorrection
  exact classifierEstimation_choice_integrable n rho P k
    (cellOutcomePoissonLaw P k) (idealLightCorrection P k t rho)
    (idealHeavyCorrection P k t) (measurable_idealLightCorrection P k t rho)
    (measurable_idealHeavyCorrection P k t)
    (idealLightCorrection_integrable M rho P k t hn hp hmean hvariance ht)
    (idealHeavyCorrection_integrable M P k t hn hp hvariance)

lemma idealSelectedCorrection_sq_integrable {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    Integrable (fun p => idealSelectedCorrection P k t rho p ^ 2)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)) := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  rw [show (fun p => idealSelectedCorrection P k t rho p ^ 2) =
      fun p => if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        idealLightCorrection P k t rho p.2 ^ 2 else
        idealHeavyCorrection P k t p.2 ^ 2 by
    funext p
    unfold idealSelectedCorrection
    split_ifs <;> rfl]
  exact classifierEstimation_choice_integrable n rho P k
    (cellOutcomePoissonLaw P k) (fun p => idealLightCorrection P k t rho p ^ 2)
    (fun p => idealHeavyCorrection P k t p ^ 2)
    ((measurable_idealLightCorrection P k t rho).pow_const 2)
    ((measurable_idealHeavyCorrection P k t).pow_const 2)
    (idealLightCorrection_sq_integrable M rho P k t hn hp hmean hvariance ht)
    (idealHeavyCorrection_sq_integrable M P k t hn hp hvariance)

/-- Exact bias contribution of a selected positive-mass cell. -/
lemma idealSelectedCorrection_first_moment {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ p, idealSelectedCorrection P k t rho p
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        upperAuditWeights n rho P k := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  have hsel : Integrable (fun p : FiniteSample (SampleObs n) ×
      (FiniteSample ℝ × FiniteSample ℝ) =>
      if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        idealLightCorrection P k t rho p.2 else idealHeavyCorrection P k t p.2)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)) := by
    rw [show (fun p : FiniteSample (SampleObs n) ×
        (FiniteSample ℝ × FiniteSample ℝ) =>
        if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
          idealLightCorrection P k t rho p.2 else idealHeavyCorrection P k t p.2) =
        idealSelectedCorrection P k t rho by
      funext p
      rfl]
    exact idealSelectedCorrection_integrable M rho P k t hn hp hmean hvariance ht
  unfold idealSelectedCorrection
  rw [classifierEstimation_choice_integral n rho P k (cellOutcomePoissonLaw P k)
    (idealLightCorrection P k t rho) (idealHeavyCorrection P k t)
    hsel]
  rw [show (∫ p, idealLightCorrection P k t rho p
      ∂cellOutcomePoissonLaw P k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        lightAuditWeight n rho P k by
    exact lightCorrection_first_moment_eq_weight M rho P k t hn hp hmean
      hvariance ht]
  rw [show (∫ p, idealHeavyCorrection P k t p
      ∂cellOutcomePoissonLaw P k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        heavyAuditWeight n P k by
    exact heavyCorrection_first_moment_eq_weight M P k t hn hp hvariance]
  unfold upperAuditWeights
  ring

/-- Exact selected-cell second moment under independent classifier and
estimation Poisson samples. -/
lemma idealSelectedCorrection_second_moment {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ p, idealSelectedCorrection P k t rho p ^ 2
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) =
      classificationProbability n rho P k *
        (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) +
      (1 - classificationProbability n rho P k) *
        (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
          heavyCoefficient n N0 N1 ^ 2
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  have hsel := idealSelectedCorrection_sq_integrable M rho P k t hn hp hmean
    hvariance ht
  rw [show (fun p => idealSelectedCorrection P k t rho p ^ 2) =
      fun p => (if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
        idealLightCorrection P k t rho p.2 else idealHeavyCorrection P k t p.2) ^ 2 by
    funext p
    rfl]
  rw [classifierEstimation_choice_sq_integral n rho P k
    (cellOutcomePoissonLaw P k) (idealLightCorrection P k t rho)
    (idealHeavyCorrection P k t) (by simpa only [idealSelectedCorrection] using hsel)]
  rw [show (∫ p, idealLightCorrection P k t rho p ^ 2
      ∂cellOutcomePoissonLaw P k) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k)) by
    exact lightCorrection_second_moment_cell M rho P k t _ _ hn hp hmean
      hvariance ht]
  rw [show (∫ p, idealHeavyCorrection P k t p ^ 2
      ∂cellOutcomePoissonLaw P k) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k)) by
    exact heavyCorrection_second_moment_cell M P k t _ _ hn hp hvariance]

lemma upperAuditWeights_eq_zero_of_cellMass_eq_zero {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hp : P.cellMass k = 0) :
    upperAuditWeights n rho P k = 0 := by
  unfold upperAuditWeights lightAuditWeight heavyAuditWeight armMass
  simp [hp]

/-- Once the cell means have been identified, their aggregate conditional
bias is exactly the audit-weight discrepancy paired with the cell effects. -/
lemma selectedCorrection_sum_bias_identity {n : ℕ} (rho t : ℝ) (P : Law n)
    (mean : Fin n → ℝ)
    (hmean : ∀ k, mean k =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        upperAuditWeights n rho P k) :
    t + ∑ k, mean k - DiscreteAteHeterogeneityFrontier.rawAteFormula P =
      ∑ k, (upperAuditWeights n rho P k - P.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) := by
  simp_rw [hmean]
  unfold DiscreteAteHeterogeneityFrontier.rawAteFormula
  have hmass := DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one P
  have htSum : (∑ k : Fin n, P.cellMass k * t) = t := by
    rw [← Finset.sum_mul, hmass, one_mul]
  calc
    t + ∑ k : Fin n,
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          upperAuditWeights n rho P k -
        ∑ k : Fin n, P.cellMass k *
          DiscreteAteHeterogeneityFrontier.cellEffect P k =
      ∑ k : Fin n, (P.cellMass k * t +
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          upperAuditWeights n rho P k -
        P.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P k) := by
          nth_rewrite 1 [← htSum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      ring

-- keep: global selected-correction bias bound exposed for estimator audits
lemma selectedCorrection_sum_bias_le {n : ℕ} (M rho t : ℝ) (P : Law n)
    (mean : Fin n → ℝ) (hn : 0 < n) (hM : 0 ≤ M)
    (hoverlap : FixedOverlap P) (henvelope : MeanEnvelope M P)
    (ht : AdmissiblePilotValue M t)
    (hmean : ∀ k, mean k =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        upperAuditWeights n rho P k) :
    |t + ∑ k, mean k - DiscreteAteHeterogeneityFrontier.rawAteFormula P| ≤
      2 * M * (196612 / (degree n rho : ℝ)) := by
  rw [selectedCorrection_sum_bias_identity rho t P mean hmean]
  calc
    |∑ k : Fin n, (upperAuditWeights n rho P k - P.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)| ≤
      ∑ k : Fin n, |(upperAuditWeights n rho P k - P.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, 2 * M *
        |upperAuditWeights n rho P k - P.cellMass k| := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hp : 0 < P.cellMass k
      · rw [abs_mul]
        have heffect := cellEffect_sub_pilot_abs_le P k t hp henvelope ht
        calc
          |upperAuditWeights n rho P k - P.cellMass k| *
              |DiscreteAteHeterogeneityFrontier.cellEffect P k - t| ≤
              |upperAuditWeights n rho P k - P.cellMass k| * (2 * M) :=
            mul_le_mul_of_nonneg_left heffect (abs_nonneg _)
          _ = 2 * M * |upperAuditWeights n rho P k - P.cellMass k| := by ring
      · have hp0 : P.cellMass k = 0 :=
          le_antisymm (le_of_not_gt hp) (P.cellMass_range k).1
        rw [hp0, upperAuditWeights_eq_zero_of_cellMass_eq_zero rho P k hp0]
        simp
    _ = 2 * M * (∑ k : Fin n,
        |upperAuditWeights n rho P k - P.cellMass k|) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * M * (196612 / (degree n rho : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (audit_weight_bias_bound_explicit rho P hn hoverlap) (by positivity)

/-- Algebraic variance form for an independently selected two-branch
correction, converting first and second moments into equation (42). -/
-- keep: paper equation (42) conversion from raw moments to mixture variance
lemma classifierMixtureVariance_moment_identity
    (alpha lightFirst heavyFirst lightSecond heavySecond : ℝ) :
    alpha * lightSecond + (1 - alpha) * heavySecond -
        (alpha * lightFirst + (1 - alpha) * heavyFirst) ^ 2 =
      classifierMixtureVariance alpha
        (lightSecond - lightFirst ^ 2) (heavySecond - heavyFirst ^ 2)
        lightFirst heavyFirst := by
  unfold classifierMixtureVariance
  ring

lemma classifierMixtureVariance_le_three_light
    {alpha lightSecond lightVariance heavyVariance lightMean heavyMean M p : ℝ}
    (ha : alpha ∈ Set.Icc (0 : ℝ) 1) (hL2 : 0 ≤ lightSecond)
    (hlightVar : lightVariance ≤ lightSecond)
    (hlightMean : lightMean ^ 2 ≤ lightSecond)
    (hheavyMean : heavyMean ^ 2 ≤ 4 * M ^ 2 * p ^ 2) :
    classifierMixtureVariance alpha lightVariance heavyVariance lightMean heavyMean ≤
      3 * alpha * lightSecond + (1 - alpha) * heavyVariance +
        8 * M ^ 2 * p ^ 2 * alpha * (1 - alpha) := by
  have hbeta : 0 ≤ 1 - alpha := sub_nonneg.mpr ha.2
  have hmix : 0 ≤ alpha * (1 - alpha) := mul_nonneg ha.1 hbeta
  have hdiff : (lightMean - heavyMean) ^ 2 ≤
      2 * (lightMean ^ 2 + heavyMean ^ 2) := by
    nlinarith [sq_nonneg (lightMean + heavyMean)]
  have hdiff' : (lightMean - heavyMean) ^ 2 ≤
      2 * lightSecond + 8 * M ^ 2 * p ^ 2 := by
    nlinarith
  have hcross := mul_le_mul_of_nonneg_left hdiff' hmix
  have hbetaOne : 1 - alpha ≤ 1 := sub_le_self 1 ha.1
  have hlightCross : alpha * (1 - alpha) * (2 * lightSecond) ≤
      2 * alpha * lightSecond := by
    calc
      alpha * (1 - alpha) * (2 * lightSecond) =
          (1 - alpha) * (2 * alpha * lightSecond) := by ring
      _ ≤ 1 * (2 * alpha * lightSecond) :=
        mul_le_mul_of_nonneg_right hbetaOne
          (mul_nonneg (mul_nonneg (by positivity) ha.1) hL2)
      _ = 2 * alpha * lightSecond := by ring
  have hvarPart := mul_le_mul_of_nonneg_left hlightVar ha.1
  unfold classifierMixtureVariance
  calc
    alpha * lightVariance + (1 - alpha) * heavyVariance +
          alpha * (1 - alpha) * (lightMean - heavyMean) ^ 2 ≤
        alpha * lightSecond + (1 - alpha) * heavyVariance +
          alpha * (1 - alpha) *
            (2 * lightSecond + 8 * M ^ 2 * p ^ 2) :=
      add_le_add (add_le_add hvarPart le_rfl) hcross
    _ = (alpha * lightSecond +
          alpha * (1 - alpha) * (2 * lightSecond)) +
        (1 - alpha) * heavyVariance +
          8 * M ^ 2 * p ^ 2 * alpha * (1 - alpha) := by ring
    _ ≤ (alpha * lightSecond + 2 * alpha * lightSecond) +
        (1 - alpha) * heavyVariance +
          8 * M ^ 2 * p ^ 2 * alpha * (1 - alpha) := by
      linarith
    _ = 3 * alpha * lightSecond + (1 - alpha) * heavyVariance +
          8 * M ^ 2 * p ^ 2 * alpha * (1 - alpha) := by ring

lemma variance_le_centered_second_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hfsq : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
      ∫ x, (f x - c) ^ 2 ∂μ := by
  have hconst : Integrable (fun _ : X => c ^ 2) μ := integrable_const _
  have hlinear : Integrable (fun x => 2 * c * f x) μ := by
    simpa only [mul_assoc] using hf.const_mul (2 * c)
  rw [show (fun x => (f x - c) ^ 2) =
      fun x => f x ^ 2 - 2 * c * f x + c ^ 2 by
    funext x
    ring]
  have hop : (fun x => f x ^ 2 - 2 * c * f x + c ^ 2) =
      ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
        (fun _ => c ^ 2) := by
    funext x
    rfl
  rw [hop]
  have hadd : integral μ (((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
      (fun _ => c ^ 2)) =
      integral μ ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
        integral μ (fun _ => c ^ 2) := by
    exact integral_add (hfsq.sub hlinear) hconst
  have hsub : integral μ ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) =
      integral μ (fun x => f x ^ 2) - integral μ (fun x => 2 * c * f x) := by
    exact integral_sub hfsq hlinear
  rw [hadd, hsub, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg ((∫ x, f x ∂μ) - c)]

/-- The heavy audit is the centered second-moment envelope for the actual
heavy correction.  The missing-arm guard changes its mean, so the centering
inequality is applied to the guarded count itself. -/
lemma heavyCorrection_variance_le_conditional {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hvariance : VarianceEnvelope M P) :
    let heavySecond :=
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))
    let heavyFirst := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
      heavyAuditWeight n P k
    heavySecond - heavyFirst ^ 2 ≤ heavyCellConditionalVariance P k t := by
  dsimp only
  let a : ℝ≥0 := Real.toNNReal (blockMean n * armMass P false k)
  let b : ℝ≥0 := Real.toNNReal (blockMean n * armMass P true k)
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  let p := P.cellMass k
  let f : ℕ × ℕ → ℝ := fun q => guardedTotalCount q.1 q.2 / blockMean n
  let μ : Measure (ℕ × ℕ) := (poissonMeasure a).prod (poissonMeasure b)
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hm : blockMean n ≠ 0 := (blockMean_pos n hn).ne'
  have hfsq : Integrable (fun q => f q ^ 2) μ := by
    rw [integrable_prod_iff (measurable_of_countable _).aestronglyMeasurable]
    constructor
    · filter_upwards with N0
      have h := (guardedTotalCount_center_sq_integrable_inner b N0 0).const_mul
        (1 / blockMean n ^ 2)
      exact h.congr (Filter.Eventually.of_forall fun N1 => by
        dsimp only [f]
        rw [sub_zero]
        field_simp)
    · have h := (guardedTotalCount_center_sq_integrable_outer a b 0).const_mul
        (1 / blockMean n ^ 2)
      have hnonneg (N0 : ℕ) : 0 ≤ ∫ N1 : ℕ,
          guardedTotalCount N0 N1 ^ 2 ∂poissonMeasure b :=
        integral_nonneg fun _ => sq_nonneg _
      exact h.congr (Filter.Eventually.of_forall fun N0 => by
        change 1 / blockMean n ^ 2 *
            (∫ N1 : ℕ, (guardedTotalCount N0 N1 - 0) ^ 2 ∂poissonMeasure b) =
          ∫ N1 : ℕ, ‖f (N0, N1) ^ 2‖ ∂poissonMeasure b
        rw [show (fun N1 : ℕ => ‖f (N0, N1) ^ 2‖) = fun N1 =>
            (1 / blockMean n ^ 2) * guardedTotalCount N0 N1 ^ 2 by
          funext N1
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          dsimp only [f]
          field_simp]
        rw [integral_const_mul]
        simp only [sub_zero])
  have hf : Integrable f μ := by
    have hmajor := hfsq.add (integrable_const (1 : ℝ))
    apply hmajor.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs]
    change |f q| ≤ f q ^ 2 + 1
    have hs := sq_nonneg (|f q| - 1)
    have habs := sq_abs (f q)
    nlinarith
  have hcenter : Integrable (fun q => (f q - p) ^ 2) μ := by
    exact (hfsq.add ((hf.const_mul (-2 * p)))).add (integrable_const (p ^ 2))
      |>.congr (Filter.Eventually.of_forall fun q => by
        change f q ^ 2 + (-2 * p) * f q + p ^ 2 = (f q - p) ^ 2
        ring)
  have hvar := variance_le_centered_second_moment μ f p hf hfsq
  rw [integral_prod _ hf, integral_prod _ hfsq, integral_prod _ hcenter] at hvar
  have hmean : (∫ (N0 : ℕ), ∫ (N1 : ℕ), f (N0, N1) ∂poissonMeasure b
      ∂poissonMeasure a) = heavyAuditWeight n P k := by
    rw [show (fun N0 : ℕ => ∫ (N1 : ℕ), f (N0, N1) ∂poissonMeasure b) =
        fun (N0 : ℕ) => ∫ (N1 : ℕ), (N0 : ℝ) * (N1 : ℝ) *
          heavyCoefficient n N0 N1 ∂poissonMeasure b by
      funext (N0 : ℕ)
      apply integral_congr_ae
      filter_upwards with N1
      dsimp only [f]
      exact (heavyWeightedCount_eq_guarded N0 N1 hn).symm]
    exact heavyWeightedCount_integral_armMass P k hn
  rw [hmean] at hvar
  have hd0 : 0 ≤ d ^ 2 := sq_nonneg d
  have hscaled := mul_le_mul_of_nonneg_left hvar hd0
  have hnoiseInner (N0 : ℕ) :=
    heavyOutcomeNoiseSecond_integrable_inner M P k b N0 hn hp hvariance
  have hnoiseOuter :=
    heavyOutcomeNoiseSecond_integrable_outer M P k a b hn hp hvariance
  have hsignalInner (N0 : ℕ) : Integrable (fun N1 : ℕ =>
      d ^ 2 * f (N0, N1) ^ 2) (poissonMeasure b) := by
    exact ((guardedTotalCount_center_sq_integrable_inner b N0 0).const_mul
      (d ^ 2 / blockMean n ^ 2)).congr
        (Filter.Eventually.of_forall fun N1 => by
          dsimp only [f, d]
          rw [sub_zero]
          field_simp)
  have hsignalOuter : Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      d ^ 2 * f (N0, N1) ^ 2 ∂poissonMeasure b) (poissonMeasure a) := by
    have h := (guardedTotalCount_center_sq_integrable_outer a b 0).const_mul
      (d ^ 2 / blockMean n ^ 2)
    exact h.congr (Filter.Eventually.of_forall fun N0 => by
      change d ^ 2 / blockMean n ^ 2 *
          (∫ N1 : ℕ, (guardedTotalCount N0 N1 - 0) ^ 2 ∂poissonMeasure b) =
        ∫ N1 : ℕ, d ^ 2 * f (N0, N1) ^ 2 ∂poissonMeasure b
      rw [show (fun N1 : ℕ => d ^ 2 * f (N0, N1) ^ 2) = fun N1 =>
          (d ^ 2 / blockMean n ^ 2) * guardedTotalCount N0 N1 ^ 2 by
        funext N1
        dsimp only [f]
        field_simp]
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with N1
      rw [sub_zero])
  have hsecond :
      (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
          heavyCoefficient n N0 N1 ^ 2 ∂poissonMeasure b ∂poissonMeasure a) =
        (∫ N0, ∫ N1, heavyOutcomeNoiseSecond P k N0 N1
          ∂poissonMeasure b ∂poissonMeasure a) +
        ∫ N0, ∫ N1, d ^ 2 * f (N0, N1) ^ 2
          ∂poissonMeasure b ∂poissonMeasure a := by
    rw [show (fun N0 : ℕ => ∫ N1,
        conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2
          ∂poissonMeasure b) = fun N0 => ∫ N1,
        heavyOutcomeNoiseSecond P k N0 N1 + d ^ 2 * f (N0, N1) ^ 2
          ∂poissonMeasure b by
      funext N0
      apply integral_congr_ae
      filter_upwards with N1
      rw [heavyConditionalSecond_decomposition P k t N0 N1 hn]
      dsimp only [d, f]
      field_simp]
    rw [show (fun N0 : ℕ => ∫ N1, heavyOutcomeNoiseSecond P k N0 N1 +
        d ^ 2 * f (N0, N1) ^ 2 ∂poissonMeasure b) = fun N0 =>
        (∫ N1, heavyOutcomeNoiseSecond P k N0 N1 ∂poissonMeasure b) +
        ∫ N1, d ^ 2 * f (N0, N1) ^ 2 ∂poissonMeasure b by
      funext N0
      exact integral_add (hnoiseInner N0) (hsignalInner N0)]
    exact integral_add hnoiseOuter hsignalOuter
  rw [hsecond]
  unfold heavyCellConditionalVariance
  change _ ≤ (∫ N0, ∫ N1, heavyOutcomeNoiseSecond P k N0 N1
      ∂poissonMeasure b ∂poissonMeasure a) +
    ∫ N0, ∫ N1, ((f (N0, N1) - p) * d) ^ 2
      ∂poissonMeasure b ∂poissonMeasure a
  have hscaled' : d ^ 2 *
      ((∫ N0, ∫ N1, f (N0, N1) ^ 2 ∂poissonMeasure b ∂poissonMeasure a) -
        heavyAuditWeight n P k ^ 2) ≤
      d ^ 2 * (∫ N0, ∫ N1, (f (N0, N1) - p) ^ 2
        ∂poissonMeasure b ∂poissonMeasure a) := by
    nlinarith
  have hsignalIntegral :
      (∫ N0, ∫ N1, d ^ 2 * f (N0, N1) ^ 2
        ∂poissonMeasure b ∂poissonMeasure a) =
      d ^ 2 * (∫ N0, ∫ N1, f (N0, N1) ^ 2
        ∂poissonMeasure b ∂poissonMeasure a) := by
    simp_rw [integral_const_mul]
  calc
    _ = (∫ N0, ∫ N1, heavyOutcomeNoiseSecond P k N0 N1
          ∂poissonMeasure b ∂poissonMeasure a) +
        d ^ 2 * ((∫ N0, ∫ N1, f (N0, N1) ^ 2
          ∂poissonMeasure b ∂poissonMeasure a) -
            heavyAuditWeight n P k ^ 2) := by
      rw [hsignalIntegral]
      dsimp only [d]
      ring
    _ ≤ (∫ N0, ∫ N1, heavyOutcomeNoiseSecond P k N0 N1
          ∂poissonMeasure b ∂poissonMeasure a) +
        d ^ 2 * (∫ N0, ∫ N1, (f (N0, N1) - p) ^ 2
          ∂poissonMeasure b ∂poissonMeasure a) := by linarith
    _ = _ := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with N0
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with N1
      ring

/-- The exact selected-cell variance, expressed using the light and heavy
audit second moments and their identified means. -/
lemma idealSelectedCorrection_variance_eq {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    let lightSecond :=
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))
    let heavySecond :=
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))
    let lightFirst := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
      lightAuditWeight n rho P k
    let heavyFirst := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
      heavyAuditWeight n P k
    (∫ p, idealSelectedCorrection P k t rho p ^ 2
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) -
      (∫ p, idealSelectedCorrection P k t rho p
        ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) ^ 2 =
      classifierMixtureVariance (classificationProbability n rho P k)
        (lightSecond - lightFirst ^ 2) (heavySecond - heavyFirst ^ 2)
        lightFirst heavyFirst := by
  dsimp only
  rw [idealSelectedCorrection_second_moment M rho P k t hn hp hmean hvariance ht,
    idealSelectedCorrection_first_moment M rho P k t hn hp hmean hvariance ht]
  unfold upperAuditWeights classifierMixtureVariance
  ring

/-- Global equation (44) once each selected-cell variance has been reduced to
the light audit, heavy centered variance, and classifier mixing term. -/
lemma selectedCorrection_variance_sum_le_of_cell {n : ℕ}
    (M rho t : ℝ) (P : Law n) (cellVariance : Fin n → ℝ)
    (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t)
    (hcell : ∀ k, cellVariance k ≤
      3 * classificationProbability n rho P k *
        (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) +
      (1 - classificationProbability n rho P k) *
        heavyCellConditionalVariance P k t +
      8 * M ^ 2 * P.cellMass k ^ 2 * classificationProbability n rho P k *
        (1 - classificationProbability n rho P k)) :
    (∑ k, cellVariance k) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) := by
  calc
    (∑ k, cellVariance k) ≤ ∑ k : Fin n,
        (3 * classificationProbability n rho P k *
          (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
            factorialCorrectionSquare n rho N0 N1
            ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
            ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) +
        (1 - classificationProbability n rho P k) *
          heavyCellConditionalVariance P k t +
        8 * M ^ 2 * P.cellMass k ^ 2 * classificationProbability n rho P k *
          (1 - classificationProbability n rho P k)) :=
      Finset.sum_le_sum (fun k _ => hcell k)
    _ = 3 * lightConditionalAudit n rho P t +
        (∑ k : Fin n, (1 - classificationProbability n rho P k) *
          heavyCellConditionalVariance P k t) +
        8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k)) := by
      unfold lightConditionalAudit
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
      ring
    _ ≤ 3 * lightConditionalAudit n rho P t + 115 * M ^ 2 / blockMean n +
        8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k)) := by
      gcongr
      exact sum_classifierWeighted_heavyVariance_le M rho P t hn hoverlap
        hmean hvariance ht
    _ ≤ 3 * (lightConditionalAudit n rho P t + 115 * M ^ 2 / blockMean n +
        8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k))) := by
      have hheavy : 0 ≤ 115 * M ^ 2 / blockMean n := by
        exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg M))
          (blockMean_pos n hn).le
      have hcross : 0 ≤ 8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k)) := by
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro k hk
        obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
        positivity
      linarith
    _ ≤ _ := by
      gcongr
      exact upperVarianceAuditBudget_le M rho P t hn hoverlap hmean hvariance ht

/-- Equation (46) in moment form: variance plus squared bias controls MSE. -/
-- keep: reusable paper equation (46) variance-plus-bias risk inequality
lemma mse_le_of_variance_and_bias {first second target V B : ℝ}
    (hvar : second - first ^ 2 ≤ V) (hbias : |first - target| ≤ B)
    (hB : 0 ≤ B) :
    second - 2 * target * first + target ^ 2 ≤ V + B ^ 2 := by
  have hbiasSq : (first - target) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hB).2 hbias
  calc
    second - 2 * target * first + target ^ 2 =
        (second - first ^ 2) + (first - target) ^ 2 := by ring
    _ ≤ V + B ^ 2 := add_le_add hvar hbiasSq

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

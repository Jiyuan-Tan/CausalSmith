module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExitIntegration
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

/-!
# Exact observed-history KL assembly

This module plugs the unequal-mass finite marked-Poisson identity into the
paper's stopped-recurrence and explicit intensity constructions.
-/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The explicit baseline inherits the assignment-law atom from its reference
law. -/
lemma SubjectLaw.baseline_assignmentLaw
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference) :
    AssignmentLaw (SubjectLaw.baseline reference lambda0 d0 hd0) := by
  intro a
  change (SubjectLaw.baseline reference lambda0 d0 hd0).latent.real
      (LatentSubject.treatment ⁻¹' {a}) = reference.p a
  have hmarg := (SubjectLaw.baseline_preserves_marginals
    reference lambda0 d0 hd0).1
  have hbase := Measure.map_apply measurable_latentSubject_treatment
    (measurableSet_singleton a)
    (μ := (SubjectLaw.baseline reference lambda0 d0 hd0).latent)
  have href := Measure.map_apply measurable_latentSubject_treatment
    (measurableSet_singleton a) (μ := reference.latent)
  simp only [measureReal_def]
  calc
    _ = ((Measure.map LatentSubject.treatment
          (SubjectLaw.baseline reference lambda0 d0 hd0).latent) {a}).toReal :=
      congrArg ENNReal.toReal hbase.symm
    _ = ((Measure.map LatentSubject.treatment reference.latent) {a}).toReal := by
      rw [hmarg]
    _ = (reference.latent (LatentSubject.treatment ⁻¹' {a})).toReal :=
      congrArg ENNReal.toReal href
    _ = _ := hAssignment a

/-- Fixed-exit KL between canonical stopped recurrence laws is exactly the KL
between their intensity measures restricted through the exit. -/
lemma klDiv_map_stopAt_canonicalRecurrenceLawOf
    (x : ℝ) (nu1 nu0 : Measure ℝ)
    (hfinite1 : IsFiniteMeasure nu1) (hfinite0 : IsFiniteMeasure nu0) :
    InformationTheory.klDiv
        (Measure.map (RecurConfig.stopAt x)
          (@canonicalRecurrenceLawOf nu1 hfinite1))
        (Measure.map (RecurConfig.stopAt x)
          (@canonicalRecurrenceLawOf nu0 hfinite0)) =
      InformationTheory.klDiv
        (nu1.restrict (Set.Iic x)) (nu0.restrict (Set.Iic x)) := by
  letI : IsFiniteMeasure nu1 := hfinite1
  letI : IsFiniteMeasure nu0 := hfinite0
  letI : IsFiniteMeasure (nu1.restrict (Set.Iic x)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (measure_ne_top _ _)
  letI : IsFiniteMeasure (nu0.restrict (Set.Iic x)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (measure_ne_top _ _)
  rw [canonicalRecurrenceLawOf_map_stopAt_restrict x nu1 (Measure.dirac 0),
    canonicalRecurrenceLawOf_map_stopAt_restrict x nu0 (Measure.dirac 0),
    Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.klDiv_finiteMeasureMarkedPoissonLaw_unequal]
  simp

/-- At a fixed exit record, the explicit perturbation-versus-baseline stopped
recurrence KL is zero on control and is the cumulative local Poisson KL on
treatment. -/
lemma SubjectLaw.baselinePerturb_fixedExit_stoppedKL
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) (e : ExitRecord)
    (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)) :
    InformationTheory.klDiv
        (Measure.map (RecurConfig.stopAt e.2.1)
          (@canonicalRecurrenceLawOf
            (treatmentPerturbIntensity
              (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 e.1)
            (hfinite e.1)))
        (Measure.map (RecurConfig.stopAt e.2.1)
          (@canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
            (baselineRecurrenceIntensity_isFinite lambda0))) =
      if e.1 then
        ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal
          (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      else 0 := by
  letI : IsFiniteMeasure (baselineRecurrenceIntensity lambda0) :=
    baselineRecurrenceIntensity_isFinite lambda0
  letI : IsFiniteMeasure
      ((baselineRecurrenceIntensity lambda0).restrict (Set.Iic e.2.1)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (measure_ne_top _ _)
  cases harm : e.1
  · simp only [harm, Bool.false_eq_true, ↓reduceIte]
    rw [klDiv_map_stopAt_canonicalRecurrenceLawOf]
    rw [treatmentPerturbIntensity_baseline_false reference lambda0 d0 hd0 lam1,
      InformationTheory.klDiv_self]
  · simp only [harm, ↓reduceIte]
    rw [klDiv_map_stopAt_canonicalRecurrenceLawOf]
    exact SubjectLaw.baselinePerturb_restrictedIntensity_klDiv
      reference lambda0 d0 hd0 lam1 e.2.1 hlam1_meas hlam1_pos hlambda0 hfinite

/-- Interval integrability of the positive local Poisson cost makes every
fixed-exit stopped recurrence KL finite, hence gives fibrewise absolute
continuity for the common-exit chain rule. -/
lemma SubjectLaw.baselinePerturb_fixedExit_stoppedKL_ne_top
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) (e : ExitRecord)
    (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hcost : IntervalIntegrable (fun t : ℝ =>
      lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
      volume 0 1) :
    InformationTheory.klDiv
        (Measure.map (RecurConfig.stopAt e.2.1)
          (@canonicalRecurrenceLawOf
            (treatmentPerturbIntensity
              (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 e.1)
            (hfinite e.1)))
        (Measure.map (RecurConfig.stopAt e.2.1)
          (@canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
            (baselineRecurrenceIntensity_isFinite lambda0))) ≠ ∞ := by
  rw [SubjectLaw.baselinePerturb_fixedExit_stoppedKL reference lambda0 d0 hd0
    lam1 e hlam1_meas hlam1_pos hlambda0 hfinite]
  cases harm : e.1
  · simp
  · simp only [← harm, ↓reduceIte]
    let cost : ℝ → ℝ := fun t =>
      lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0
    have hcostInt : Integrable cost
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      rw [← IntegrableOn]
      rw [← uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact intervalIntegrable_iff.mp hcost
    have hcostNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] cost := by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      exact poissonIntensityCost_nonneg (lam1 t) lambda0 (hlam1_pos t ht) hlambda0
    have hfull : (∫⁻ t, ENNReal.ofReal (cost t)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≠ ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hcostInt hcostNonneg]
      exact ENNReal.ofReal_ne_top
    exact ne_of_lt (lt_of_le_of_lt
      (lintegral_mono' Measure.restrict_le_self le_rfl)
      (lt_top_iff_ne_top.mpr hfull))

private lemma canonicalRecurrenceLawOf_congr (nu1 nu2 : Measure ℝ)
    [h1 : IsFiniteMeasure nu1] [h2 : IsFiniteMeasure nu2] (h : nu1 = nu2) :
    @canonicalRecurrenceLawOf nu1 h1 = @canonicalRecurrenceLawOf nu2 h2 := by
  subst nu2
  rfl

/-- Explicit treatment perturbations with the same arm intensity measures have the same latent law. -/
lemma SubjectLaw.perturbTreatment_latent_eq_of_intensity_eq (base : SubjectLaw) (f g : ℝ → ℝ)
    (hf : ∀ a, IsFiniteMeasure (treatmentPerturbIntensity base f a))
    (hg : ∀ a, IsFiniteMeasure (treatmentPerturbIntensity base g a))
    (heq : ∀ a, treatmentPerturbIntensity base f a =
      treatmentPerturbIntensity base g a) :
    (SubjectLaw.perturbTreatment base f hf).latent =
      (SubjectLaw.perturbTreatment base g hg).latent := by
  have hrec :
      (fun a => @canonicalRecurrenceLawOf
        (treatmentPerturbIntensity base f a) (hf a)) =
      (fun a => @canonicalRecurrenceLawOf
        (treatmentPerturbIntensity base g a) (hg a)) := by
    funext a
    exact canonicalRecurrenceLawOf_congr _ _ (heq a)
  unfold SubjectLaw.perturbTreatment
  dsimp only
  rw [hrec]

/-- Explicit treatment perturbations with the same arm intensity measures have the same observed law. -/
lemma SubjectLaw.perturbTreatment_observedLaw_eq_of_intensity_eq (base : SubjectLaw) (f g : ℝ → ℝ)
    (hf : ∀ a, IsFiniteMeasure (treatmentPerturbIntensity base f a))
    (hg : ∀ a, IsFiniteMeasure (treatmentPerturbIntensity base g a))
    (heq : ∀ a, treatmentPerturbIntensity base f a =
      treatmentPerturbIntensity base g a) :
    observedLaw (SubjectLaw.perturbTreatment base f hf) =
      observedLaw (SubjectLaw.perturbTreatment base g hg) := by
  unfold observedLaw
  rw [SubjectLaw.perturbTreatment_latent_eq_of_intensity_eq base f g hf hg heq]


/-- The explicit perturbation-versus-baseline observed KL is the common exit
average of the treated cumulative local Poisson cost. -/
lemma SubjectLaw.baselinePerturb_observedKL_eq_exitIntegral
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hcost : IntervalIntegrable (fun t : ℝ =>
      lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
      volume 0 1) :
    InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0)) =
      ∫⁻ e, (if e.1 then
        ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal
          (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) else 0)
        ∂SubjectLaw.baselineExitRecordLaw reference d0 := by
  letI : IsProbabilityMeasure (SubjectLaw.baselineExitRecordLaw reference d0) :=
    SubjectLaw.baselineExitRecordLaw_isProbability reference d0 hd0
  have hac : ∀ᵐ e ∂SubjectLaw.baselineExitRecordLaw reference d0,
      stoppedRecurrenceKernel
          (fun a => treatmentPerturbIntensity
            (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a)
          hfinite e ≪
        stoppedRecurrenceKernel
          (fun _ : Arm => baselineRecurrenceIntensity lambda0)
          (fun _ => baselineRecurrenceIntensity_isFinite lambda0) e := by
    filter_upwards with e
    simpa only [stoppedRecurrenceKernel_apply] using
      (InformationTheory.klDiv_ne_top_iff.mp
        (SubjectLaw.baselinePerturb_fixedExit_stoppedKL_ne_top
          reference lambda0 d0 hd0 lam1 e hlam1_meas hlam1_pos hlambda0
          hfinite hcost)).1
  rw [SubjectLaw.baselinePerturb_observedKL_eq_fixedExitIntegral
    reference lambda0 d0 hd0 lam1 hfinite hac]
  apply lintegral_congr
  intro e
  simpa only [stoppedRecurrenceKernel_apply] using
    SubjectLaw.baselinePerturb_fixedExit_stoppedKL
      reference lambda0 d0 hd0 lam1 e hlam1_meas hlam1_pos hlambda0 hfinite

/-- The baseline common-exit average of the cumulative treated cost equals
assignment probability times the survival-retention weighted local cost. -/
lemma SubjectLaw.baselineExitIntegral_eq_survivalRetention
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1) :
    (∫⁻ e, (if e.1 then
      ∫⁻ t in Set.Iic e.2.1, ENNReal.ofReal
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) else 0)
      ∂SubjectLaw.baselineExitRecordLaw reference d0) =
      ENNReal.ofReal ((SubjectLaw.baseline reference lambda0 d0 hd0).p true) *
        ∫⁻ t, ENNReal.ofReal
          (survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t) *
          (Set.Ioc (0 : ℝ) 1).indicator (fun s => ENNReal.ofReal
            (lam1 s * Real.log (lam1 s / lambda0) - lam1 s + lambda0)) t
          ∂volume := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let cost : ℝ → ℝ := fun t =>
    lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0
  let k : ℝ → ℝ≥0∞ :=
    (Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (cost t))
  have hcostMeas : Measurable cost := by unfold cost; fun_prop
  have hk : Measurable k := hcostMeas.ennreal_ofReal.indicator measurableSet_Ioc
  have hksupp : ∀ t, t ∉ Set.Ioc (0 : ℝ) 1 → k t = 0 := by
    intro t ht
    simp [k, ht]
  have hinner (x : ℝ) :
      (∫⁻ t in Set.Iic x, ENNReal.ofReal (cost t)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
        ∫⁻ t in Set.Iic x, k t ∂volume := by
    symm
    unfold k
    rw [lintegral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact inter_comm _ _
  calc
    _ = ∫⁻ e, (if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0)
        ∂SubjectLaw.baselineExitRecordLaw reference d0 := by
      apply lintegral_congr
      intro e
      split_ifs
      · exact hinner e.2.1
      · rfl
    _ = ∫⁻ e, (if e.1 then ∫⁻ t in Set.Iic e.2.1, k t ∂volume else 0)
        ∂exitRecordLaw Pbase := by
      rw [← SubjectLaw.baselineExitRecordLaw_eq_exitRecordLaw
        reference lambda0 d0 hd0]
    _ = _ := by
      exact lintegral_exitRecordLaw_treatment_eq_survival_retention
        Pbase
        (SubjectLaw.baseline_productIndependence reference lambda0 d0 hd0).1
        (SubjectLaw.baseline_assignmentLaw reference lambda0 d0 hd0 hAssignment)
        (SubjectLaw.baseline_deathHazard reference lambda0 d0 hd0)
        (SubjectLaw.baseline_productIndependence reference lambda0 d0 hd0).2.2
        k hk hksupp

/-- The one-subject observed-history KL of the explicit treatment perturbation
is exactly assignment probability times the survival-retention weighted local
Poisson cost, in extended-real form. -/
lemma SubjectLaw.baselinePerturb_observedKL_eq_lintegral
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hcost : IntervalIntegrable (fun t : ℝ =>
      lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
      volume 0 1) :
    InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0)) =
      ENNReal.ofReal ((SubjectLaw.baseline reference lambda0 d0 hd0).p true) *
        ∫⁻ t, ENNReal.ofReal
          (survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t) *
          (Set.Ioc (0 : ℝ) 1).indicator (fun s => ENNReal.ofReal
            (lam1 s * Real.log (lam1 s / lambda0) - lam1 s + lambda0)) t
          ∂volume := by
  rw [SubjectLaw.baselinePerturb_observedKL_eq_exitIntegral
      reference lambda0 d0 hd0 lam1 hlam1_meas hlam1_pos hlambda0 hfinite hcost,
    SubjectLaw.baselineExitIntegral_eq_survivalRetention
      reference lambda0 d0 hd0 hAssignment lam1 hlam1_meas]

/-- Real-valued form of the explicit one-subject observed KL identity. -/
lemma SubjectLaw.baselinePerturb_observedKL_toReal
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hAssignment : AssignmentLaw reference)
    (lam1 : ℝ → ℝ) (hlam1_meas : Measurable lam1)
    (hlam1_pos : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ lam1 t)
    (hlambda0 : 0 < lambda0)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity
        (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 a))
    (hcost : IntervalIntegrable (fun t : ℝ =>
      lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0)
      volume 0 1)
    (hweighted : IntervalIntegrable (fun t : ℝ =>
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
        (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0))
      volume 0 1) :
    (InformationTheory.klDiv
        (observedLaw (SubjectLaw.perturbTreatment
          (SubjectLaw.baseline reference lambda0 d0 hd0) lam1 hfinite))
        (observedLaw (SubjectLaw.baseline reference lambda0 d0 hd0))).toReal =
      (SubjectLaw.baseline reference lambda0 d0 hd0).p true *
        ∫ t in (0 : ℝ)..1,
          survival (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            retention (SubjectLaw.baseline reference lambda0 d0 hd0) true t *
            (lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let cost : ℝ → ℝ := fun t =>
    lam1 t * Real.log (lam1 t / lambda0) - lam1 t + lambda0
  let weighted : ℝ → ℝ := fun t =>
    survival Pbase true t * retention Pbase true t * cost t
  have hp : 0 ≤ Pbase.p true := by
    rw [← SubjectLaw.baseline_assignmentLaw reference lambda0 d0 hd0
      hAssignment true]
    exact measureReal_nonneg
  have hweight_nonneg (t : ℝ) :
      0 ≤ survival Pbase true t * retention Pbase true t := by
    exact mul_nonneg (Real.exp_nonneg _) measureReal_nonneg
  have hweighted_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ weighted t := by
    intro t ht
    exact mul_nonneg (hweight_nonneg t)
      (poissonIntensityCost_nonneg (lam1 t) lambda0
        (hlam1_pos t ht) hlambda0)
  have hrewrite :
      (∫⁻ t, ENNReal.ofReal (survival Pbase true t * retention Pbase true t) *
        (Set.Ioc (0 : ℝ) 1).indicator
          (fun s => ENNReal.ofReal (cost s)) t ∂volume) =
        ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (weighted t) ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro t
    simp only [Set.indicator_apply]
    split_ifs with ht
    · rw [← ENNReal.ofReal_mul (hweight_nonneg t)]
    · simp
  rw [SubjectLaw.baselinePerturb_observedKL_eq_lintegral
    reference lambda0 d0 hd0 hAssignment lam1 hlam1_meas hlam1_pos
    hlambda0 hfinite hcost, hrewrite]
  exact toReal_ofReal_mul_setLIntegral_ofReal
    (Pbase.p true) hp weighted hweighted hweighted_nonneg

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

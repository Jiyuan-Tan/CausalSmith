module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationContinuity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedStoppedMeanBridge
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.StoppedKL

/-! # Armwise promoted recurrent-event model -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

@[no_expose]
noncomputable def promotedArmIntensity (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (Set.Icc (0 : ℝ) 1 |>.piecewise (P.lam a) 0 t)

@[no_expose]
noncomputable def promotedArmHazard (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (Set.Icc (0 : ℝ) 1 |>.piecewise (P.hazard a) 0 t)

lemma promotedArmIntensity_coe {c : ClassConstants} {P : SubjectLaw}
  (hP : ModelClass c P) (a : Arm) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (promotedArmIntensity P a t : ℝ) = P.lam a t := by
  rw [promotedArmIntensity]
  simp only [Set.piecewise, if_pos ht]
  exact Real.coe_toNNReal _
    (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)

lemma promotedArmHazard_coe {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (promotedArmHazard P a t : ℝ) = P.hazard a t := by
  rw [promotedArmHazard]
  simp only [Set.piecewise, if_pos ht]
  exact Real.coe_toNNReal _ (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)

lemma measurable_promotedArmIntensity {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) : Measurable (promotedArmIntensity P a) := by
  exact ((hP.recurrenceContinuousOn a).measurable_piecewise
    continuous_const.continuousOn measurableSet_Icc).real_toNNReal

lemma measurable_promotedArmHazard {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) : Measurable (promotedArmHazard P a) := by
  exact ((hP.deathContinuousOn a).measurable_piecewise
    continuous_const.continuousOn measurableSet_Icc).real_toNNReal

lemma promotedArmIntensity_measure {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] :
    Measure.map Prod.fst
        (((finiteMeasureMass (recurrenceIntensity P a) : ℝ≥0∞) •
          (normalizedFiniteMeasure (recurrenceIntensity P a) (Measure.dirac 0)).prod
            (Measure.dirac (0 : ℝ)))) =
      (volume.restrict (Set.Ico (0 : ℝ) 1)).withDensity
        (fun t ↦ (promotedArmIntensity P a t : ℝ≥0∞)) := by
  letI : IsProbabilityMeasure (Measure.dirac (0 : ℝ)) := inferInstance
  rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul,
    ← ENNReal.smul_def, normalizedFiniteMeasure_reconstruct]
  unfold recurrenceIntensity
  rw [← restrict_Ico_eq_restrict_Ioc]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  rw [← promotedArmIntensity_coe hP a ht']
  simp

@[no_expose]
noncomputable def promotedArmModel {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    Causalean.Stat.RecurrentEvent.Model Unit (ℝ × ℝ) := by
  let ν := recurrenceIntensity P a
  let hν : IsFiniteMeasure ν := by
    rcases hP.poissonRecurrence a with ⟨_, _, hν, _⟩
    exact hν
  letI : IsFiniteMeasure ν := hν
  let pointLaw := (normalizedFiniteMeasure ν (Measure.dirac (0 : ℝ))).prod
    (Measure.dirac (0 : ℝ))
  let deathLaw := P.latent.map (fun z : LatentSubject ↦ z.death a)
  let censorLaw := P.latent.map (fun z : LatentSubject ↦ censorHorizon z a)
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure pointLaw := by dsimp [pointLaw]; infer_instance
  letI : IsProbabilityMeasure deathLaw :=
    Measure.isProbabilityMeasure_map (measurable_latentSubject_death a).aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map
      (measurable_censorHorizon.comp (measurable_id.prodMk measurable_const)).aemeasurable
  exact
    { armLaw := Measure.dirac ()
      armProb := inferInstance
      pointLaw := pointLaw
      pointProb := inferInstance
      poissonRate := finiteMeasureMass ν
      deathLaw := deathLaw
      deathProb := inferInstance
      censorLaw := censorLaw
      censorProb := inferInstance
      horizon := 1
      horizon_nonneg := by norm_num
      time := Prod.fst
      measurable_time := measurable_fst
      hazard := promotedArmHazard P a
      measurable_hazard := measurable_promotedArmHazard hP a
      hazard_integrable := by
        have hEq : Set.EqOn (fun t ↦ (promotedArmHazard P a t : ℝ))
            (P.hazard a) (Set.uIcc (0 : ℝ) 1) := by
          rw [Set.uIcc_of_le (by norm_num)]
          intro t ht
          exact promotedArmHazard_coe hP a ht
        exact (hP.deathHazard.1 a).congr fun t ht ↦
          (hEq (Set.uIoc_subset_uIcc ht)).symm
      intensity := promotedArmIntensity P a
      measurable_intensity := measurable_promotedArmIntensity hP a
      primitive_intensity := by
        simpa only [ν, pointLaw] using promotedArmIntensity_measure hP a
      death_survival := by
        intro t ht
        rw [Measure.map_apply (measurable_latentSubject_death a) measurableSet_Ici]
        have hreal := hP.deathHazard.2.2.2.1 a t ht
        rw [Causalean.Stat.RecurrentEvent.hazardSurvival]
        have hhaz : (∫ u in (0 : ℝ)..t, (promotedArmHazard P a u : ℝ)) =
            ∫ u in (0 : ℝ)..t, P.hazard a u := by
          apply intervalIntegral.integral_congr
          intro u hu
          have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
            have hut : u ∈ Set.uIcc (0 : ℝ) t := hu
            rw [Set.uIcc_of_le ht.1] at hut
            exact ⟨hut.1, hut.2.trans ht.2⟩
          exact promotedArmHazard_coe hP a hu'
        rw [hhaz]
        change P.latent {z | t ≤ z.death a} = ENNReal.ofReal (survival P a t)
        rw [← hreal]
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm }

@[simp] lemma promotedArmModel_horizon {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).horizon = 1 := by
  rfl

@[simp] lemma promotedArmModel_time {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).time = Prod.fst := by
  rfl

@[simp] lemma promotedArmModel_armLaw {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).armLaw = Measure.dirac () := by
  rfl

@[simp] lemma promotedArmModel_poissonRate {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] :
    (promotedArmModel P hP a).poissonRate =
      finiteMeasureMass (recurrenceIntensity P a) := by
  rfl

@[simp] lemma promotedArmModel_pointLaw {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] :
    (promotedArmModel P hP a).pointLaw =
      (normalizedFiniteMeasure (recurrenceIntensity P a) (Measure.dirac (0 : ℝ))).prod
        (Measure.dirac (0 : ℝ)) := by
  rfl

@[simp] lemma promotedArmModel_deathLaw {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).deathLaw =
      P.latent.map (fun z : LatentSubject ↦ z.death a) := by
  rfl

@[simp] lemma promotedArmModel_censorLaw {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).censorLaw =
      P.latent.map (fun z : LatentSubject ↦ censorHorizon z a) := by
  rfl

@[simp] lemma promotedArmModel_intensity {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).intensity = promotedArmIntensity P a := by
  rfl

@[simp] lemma promotedArmModel_hazard {c : ClassConstants} (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).hazard = promotedArmHazard P a := by
  rfl

/-- The promoted arm model uses exactly the paper arm's recurrence marginal. -/
lemma promotedArmModel_recurrenceLaw {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    P.latent.map (fun z : LatentSubject ↦ z.recur a) =
      (let M := promotedArmModel P hP a
       letI : IsProbabilityMeasure M.pointLaw := M.pointProb
       finitePoissonSampleLaw M.pointLaw M.poissonRate) := by
  rcases hP.poissonRecurrence a with ⟨_, _, hν, hrecur⟩
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  rw [hrecur]
  simp only [promotedArmModel]
  unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
    finiteMeasureMarkedPoissonLaw finiteMarkedPoissonSampleLaw
  rw [one_mul]

/-- The paper clinical-count mean is the death-stopped mean of its matching
promoted arm model. -/
lemma ModelClass.lintegral_clinicalCount_eq_promotedArmModel
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent) =
      (promotedArmModel P hP a).deathStoppedCountMean := by
  apply hP.lintegral_clinicalCount_eq_promoted a (promotedArmModel P hP a)
  · rfl
  · rfl
  · exact promotedArmModel_recurrenceLaw hP a
  · rfl


end CausalSmith.Stat.RecurrentEndpointCensorFrontier

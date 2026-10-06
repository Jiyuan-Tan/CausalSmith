module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathLocalDensity

/-!
# Global density of the reference death law

This module glues the paper density before time one to the shifted exponential
density after time one and verifies the canonical global hazard equation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Absolute continuity and nonnegative support remove the extra endpoints
from the original law restricted through time one. -/
lemma armDeathEventLaw_restrict_Iic_eq_Ico {P : SubjectLaw}
    (hDeath : DeathHazard P) (a : Arm) :
    (armDeathEventLaw P a).restrict (Set.Iic 1) =
      (armDeathEventLaw P a).restrict (Set.Ico 0 1) := by
  let μ := armDeathEventLaw P a
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, armDeathEventLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  apply Measure.restrict_congr_set
  have hnonneg : ∀ᵐ t ∂μ, t ∈ Set.Ici 0 :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).mpr
      (armDeathEventLaw_nonnegativeTimeLaw P hDeath a).2
  have hac : μ ≪ (volume : Measure ℝ) := by
    simpa only [μ, armDeathEventLaw] using hDeath.2.2.1 a
  have hone : ∀ᵐ t ∂μ, t ∉ ({1} : Set ℝ) := by
    rw [ae_iff]
    rw [show {t : ℝ | ¬t ∉ ({1} : Set ℝ)} = ({1} : Set ℝ) by ext; simp]
    exact hac (measure_singleton 1)
  filter_upwards [hnonneg, hone] with t ht0 ht1
  apply propext
  change (t ≤ 1 ↔ 0 ≤ t ∧ t < 1)
  have ht1' : t ≠ 1 := by simpa only [Set.mem_singleton_iff] using ht1
  constructor
  · intro ht
    exact ⟨ht0, lt_of_le_of_ne ht ht1'⟩
  · exact fun ht => ht.2.le

/-- The original strict tail mass at one is the ENNReal paper survival. -/
lemma armDeathEventLaw_apply_Ioi_one {P : SubjectLaw} (hDeath : DeathHazard P)
    (a : Arm) :
    armDeathEventLaw P a (Set.Ioi 1) = ENNReal.ofReal (survival P a 1) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (armDeathEventLaw P a) := by
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),
    ← measureReal_def, armDeathEventLaw_real_Ioi_one hDeath a]

/-- The unit gamma density after shifting is the expected exponential density. -/
lemma gammaPDF_one_one_sub {t : ℝ} (ht : 1 < t) :
    gammaPDF 1 1 (t - 1) = ENNReal.ofReal (Real.exp (-(t - 1))) := by
  rw [gammaPDF_eq]
  simp [sub_nonneg.mpr ht.le]

/-- The paper survival-times-hazard density, supported on the study window. -/
@[no_expose]
noncomputable def referenceLocalDensity (P : SubjectLaw) (a : Arm) (t : ℝ) : ENNReal :=
  Set.indicator (Set.Ico (0 : ℝ) 1)
    (fun s => ENNReal.ofReal (survival P a s * P.hazard a s)) t

/-- The exponential continuation density, supported strictly after time one. -/
@[no_expose]
noncomputable def referenceTailDensity (P : SubjectLaw) (a : Arm) (t : ℝ) : ENNReal :=
  Set.indicator (Set.Ioi (1 : ℝ))
    (fun s => ENNReal.ofReal (survival P a 1 * Real.exp (-(s - 1)))) t

/-- The reference splice is the sum of its local and exponential Lebesgue densities. -/
lemma referenceDeathLaw_eq_piecewise_withDensity {c : ClassConstants}
    {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    referenceDeathLaw P a = volume.withDensity
      (fun t => referenceLocalDensity P a t + referenceTailDensity P a t) := by
  have hgamma : Measurable (fun t : ℝ => gammaPDF 1 1 (t - 1)) := by
    change Measurable (fun t : ℝ => ENNReal.ofReal (gammaPDFReal 1 1 (t - 1)))
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal.comp (by fun_prop)
  have htailCore : Measurable (fun s : ℝ =>
      ENNReal.ofReal (survival P a 1 * Real.exp (-(s - 1)))) := by
    fun_prop
  have htail : Measurable (referenceTailDensity P a) := by
    exact htailCore.indicator measurableSet_Ioi
  have htailMeasure :
      armDeathEventLaw P a (Set.Ioi 1) • shiftedUnitExpLaw =
        volume.withDensity (referenceTailDensity P a) := by
    rw [armDeathEventLaw_apply_Ioi_one hP.deathHazard a,
      shiftedUnitExpLaw_eq_withDensity, ← withDensity_smul _ hgamma]
    apply withDensity_congr_ae
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht
    change ENNReal.ofReal (survival P a 1) * gammaPDF 1 1 (t - 1) =
      Set.indicator (Set.Ioi (1 : ℝ))
        (fun s => ENNReal.ofReal (survival P a 1 * Real.exp (-(s - 1)))) t
    by_cases ht1 : 1 < t
    · calc
        _ = ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))) := by
          rw [gammaPDF_one_one_sub ht1]
          exact (ENNReal.ofReal_mul (p := survival P a 1)
            (q := Real.exp (-(t - 1))) (le_of_lt (Real.exp_pos _))).symm
        _ = _ := (Set.indicator_of_mem (s := Set.Ioi (1 : ℝ)) ht1
          (fun s => ENNReal.ofReal
            (survival P a 1 * Real.exp (-(s - 1))))).symm
    · have hlt : t < 1 := lt_of_le_of_ne (le_of_not_gt ht1) ht
      rw [gammaPDF_of_neg (sub_neg.mpr hlt), mul_zero]
      exact (Set.indicator_apply_eq_zero.mpr (fun hmem => (ht1 hmem).elim)).symm
  calc
    referenceDeathLaw P a =
        (armDeathEventLaw P a).restrict (Set.Ico 0 1) +
          armDeathEventLaw P a (Set.Ioi 1) • shiftedUnitExpLaw := by
      rw [referenceDeathLaw, armDeathEventLaw_restrict_Iic_eq_Ico hP.deathHazard a]
    _ = (volume.restrict (Set.Ico 0 1)).withDensity
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) +
        volume.withDensity (referenceTailDensity P a) := by
      rw [armDeathEventLaw_restrict_Ico_eq_withDensity hP a, htailMeasure]
    _ = volume.withDensity (referenceLocalDensity P a) +
        volume.withDensity (referenceTailDensity P a) := by
      change (volume.restrict (Set.Ico 0 1)).withDensity
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) + _ =
        volume.withDensity (Set.indicator (Set.Ico 0 1)
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) + _
      rw [withDensity_indicator measurableSet_Ico]
    _ = volume.withDensity
        (fun t => referenceLocalDensity P a t + referenceTailDensity P a t) := by
      exact (withDensity_add_right (referenceLocalDensity P a) htail).symm

/-- The canonical hazard density agrees almost everywhere with the glued density. -/
lemma referenceDeathHazard_density_ae {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    (fun t => ENNReal.ofReal (referenceDeathHazard P a t *
      (referenceDeathLaw P a (Set.Ici t)).toReal)) =ᵐ[volume]
      (fun t => referenceLocalDensity P a t + referenceTailDensity P a t) := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with t ht
  by_cases ht0 : t < 0
  · have hnotLocal : t ∉ Set.Ico (0 : ℝ) 1 := fun h => (not_lt_of_ge h.1) ht0
    have hnotTail : t ∉ Set.Ioi (1 : ℝ) := by
      intro h
      change 1 < t at h
      linarith
    rw [referenceDeathHazard_eq_zero_of_neg P a ht0, zero_mul,
      ENNReal.ofReal_zero]
    change 0 = Set.indicator (Set.Ico (0 : ℝ) 1)
        (fun s => ENNReal.ofReal (survival P a s * P.hazard a s)) t +
      Set.indicator (Set.Ioi (1 : ℝ))
        (fun s => ENNReal.ofReal (survival P a 1 * Real.exp (-(s - 1)))) t
    simp [Set.indicator_apply_eq_zero, hnotLocal, hnotTail]
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t < 1
    · have hlocal : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht0', ht1⟩
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0', ht1.le⟩
      have hnotTail : t ∉ Set.Ioi (1 : ℝ) := not_lt_of_ge ht1.le
      rw [referenceDeathHazard_eq P a htIcc]
      change ENNReal.ofReal (P.hazard a t *
        (referenceDeathLaw P a).real (Set.Ici t)) = _
      rw [referenceDeathLaw_real_Ici hP.deathHazard a htIcc]
      change ENNReal.ofReal (P.hazard a t * survival P a t) =
        Set.indicator (Set.Ico (0 : ℝ) 1)
            (fun s => ENNReal.ofReal (survival P a s * P.hazard a s)) t +
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun s => ENNReal.ofReal
              (survival P a 1 * Real.exp (-(s - 1)))) t
      rw [Set.indicator_of_mem hlocal]
      have htailZero : Set.indicator (Set.Ioi (1 : ℝ))
          (fun s => ENNReal.ofReal
            (survival P a 1 * Real.exp (-(s - 1)))) t = 0 :=
        Set.indicator_apply_eq_zero.mpr
        (fun hmem : t ∈ Set.Ioi (1 : ℝ) => (hnotTail hmem).elim)
      rw [htailZero, add_zero, mul_comm]
    · have ht1' : 1 < t := lt_of_le_of_ne (le_of_not_gt ht1) ht.symm
      have hnotLocal : t ∉ Set.Ico (0 : ℝ) 1 := fun h => (not_lt_of_ge h.2.le) ht1'
      rw [referenceDeathHazard_eq_one_of_one_lt P a ht1', one_mul]
      change ENNReal.ofReal ((referenceDeathLaw P a).real (Set.Ici t)) = _
      rw [referenceDeathLaw_real_Ici_of_one_lt hP.deathHazard a ht1']
      change ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))) =
        Set.indicator (Set.Ico (0 : ℝ) 1)
            (fun s => ENNReal.ofReal (survival P a s * P.hazard a s)) t +
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun s => ENNReal.ofReal
              (survival P a 1 * Real.exp (-(s - 1)))) t
      have hlocalZero : Set.indicator (Set.Ico (0 : ℝ) 1)
          (fun s => ENNReal.ofReal (survival P a s * P.hazard a s)) t = 0 :=
        Set.indicator_apply_eq_zero.mpr
        (fun hmem : t ∈ Set.Ico (0 : ℝ) 1 => (hnotLocal hmem).elim)
      rw [hlocalZero, zero_add]
      exact (Set.indicator_of_mem (s := Set.Ioi (1 : ℝ)) ht1'
        (fun s => ENNReal.ofReal
          (survival P a 1 * Real.exp (-(s - 1))))).symm

/-- The reference law satisfies the canonical global hazard-density equation. -/
lemma referenceDeathLaw_eq_withDensity {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    referenceDeathLaw P a = volume.withDensity (fun s =>
      ENNReal.ofReal (referenceDeathHazard P a s *
        (referenceDeathLaw P a (Set.Ici s)).toReal)) := by
  calc
    referenceDeathLaw P a = volume.withDensity
        (fun t => referenceLocalDensity P a t + referenceTailDensity P a t) :=
      referenceDeathLaw_eq_piecewise_withDensity hP a
    _ = volume.withDensity (fun s =>
        ENNReal.ofReal (referenceDeathHazard P a s *
          (referenceDeathLaw P a (Set.Ici s)).toReal)) :=
      withDensity_congr_ae (referenceDeathHazard_density_ae hP a).symm

/-- The spliced reference law has the extended paper hazard in the canonical
counting-process sense. -/
lemma referenceDeathLaw_hasCensorHazard {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    Causalean.Stat.RecurrentEvent.CountingProcess.HasCensorHazard
      (referenceDeathLaw P a) (referenceDeathHazard P a) := by
  refine ⟨referenceDeathLaw_nonnegativeTimeLaw hP.deathHazard a,
    measurable_referenceDeathHazard hP a,
    referenceDeathHazard_nonneg hP a, ?_,
    referenceDeathLaw_eq_withDensity hP a⟩
  intro u
  exact referenceDeathHazard_integrableOn_Icc hP a u

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

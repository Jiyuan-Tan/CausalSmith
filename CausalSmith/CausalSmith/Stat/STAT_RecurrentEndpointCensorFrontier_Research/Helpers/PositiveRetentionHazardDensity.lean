module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionHazardRepresentative

/-!
# Benchmark death density from local integrability

The finite-horizon survival-density theorem applies to a measurable hazard
representative even when the source hazard is only locally integrable. The
auxiliary model below is used solely to identify its death marginal.
-/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The cumulative hazard of the representative equals the source cumulative
hazard at every time in the study window. -/
-- @node: positiveRetention_referenceHazard_integral_eq
lemma positiveRetention_referenceHazard_integral_eq (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..t, positiveRetention_referenceHazard P hDeath a u) =
      ∫ u in (0 : ℝ)..t, P.hazard a u := by
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  have heq := positiveRetention_referenceHazard_ae_eq P hDeath a
  have heq' := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 from fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩) heq
  apply integral_congr_ae
  filter_upwards [heq', ae_restrict_mem measurableSet_Ioc] with u hu humem
  exact hu.trans (referenceDeathHazard_eq P a ⟨humem.1.le, humem.2.trans ht.2⟩)

/-- The source death law has survival-times-hazard density before the horizon
under the benchmark assumptions alone. -/
-- @node: positiveRetention_armDeathEventLaw_restrict_Ico_eq_withDensity
lemma positiveRetention_armDeathEventLaw_restrict_Ico_eq_withDensity
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P)
    (hDeathBounds : DeathBounds c P) (a : Arm) :
    (armDeathEventLaw P a).restrict (Ico 0 1) =
      (volume.restrict (Ico 0 1)).withDensity
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) := by
  let d := positiveRetention_referenceHazard P hDeath a
  have hd0 : ∀ t, 0 ≤ d t := positiveRetention_referenceHazard_nonneg P hDeath a
  have hdi : IntervalIntegrable d volume 0 1 := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (positiveRetention_referenceHazard_integrableOn c P hDeath hDeathBounds a 1)
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Causalean.Stat.RecurrentEvent.hazardSurvival (fun u => Real.toNNReal (d u)) t =
        survival P a t := by
    unfold Causalean.Stat.RecurrentEvent.hazardSurvival survival
    simp only [Real.coe_toNNReal _ (hd0 _)]
    rw [positiveRetention_referenceHazard_integral_eq P hDeath a ht]
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (armDeathEventLaw P a) :=
    Measure.isProbabilityMeasure_map (measurable_latentSubject_death a).aemeasurable
  let M : Causalean.Stat.RecurrentEvent.Model Unit ℝ :=
    { armLaw := Measure.dirac ()
      armProb := inferInstance
      pointLaw := Measure.dirac 0
      pointProb := inferInstance
      poissonRate := 0
      deathLaw := armDeathEventLaw P a
      deathProb := inferInstance
      censorLaw := Measure.dirac 0
      censorProb := inferInstance
      horizon := 1
      horizon_nonneg := by norm_num
      time := id
      measurable_time := measurable_id
      hazard := fun u => Real.toNNReal (d u)
      measurable_hazard := (positiveRetention_referenceHazard_measurable P hDeath a).real_toNNReal
      hazard_integrable := by simpa only [Real.coe_toNNReal _ (hd0 _)] using hdi
      intensity := fun _ => 0
      measurable_intensity := measurable_const
      primitive_intensity := by simp
      death_survival := by
        intro t ht
        rw [hs t ht, ← hDeath.2.2.2.1 a t ht]
        unfold armDeathEventLaw
        rw [Measure.map_apply (measurable_latentSubject_death a) measurableSet_Ici]
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm }
  have hden := M.death_law_restrict_eq_withDensity
  change (armDeathEventLaw P a).restrict (Ico 0 1) = _ at hden
  rw [hden]
  apply withDensity_congr_ae
  have heq := ae_restrict_of_ae_restrict_of_subset
    (show Ico (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 from fun u hu => ⟨hu.1, hu.2.le⟩)
    (positiveRetention_referenceHazard_ae_eq P hDeath a)
  filter_upwards [heq, ae_restrict_mem measurableSet_Ico] with t heq ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  change ENNReal.ofReal
    (Causalean.Stat.RecurrentEvent.hazardSurvival (fun u => Real.toNNReal (d u)) t) *
      (Real.toNNReal (d t) : ENNReal) = _
  rw [hs t ht', ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (hd0 _)]
  rw [show d t = P.hazard a t from heq.trans (referenceDeathHazard_eq P a ht')]
  exact (ENNReal.ofReal_mul (p := survival P a t) (q := P.hazard a t)
    (Real.exp_pos _).le).symm

-- @node: positiveRetention_referenceDeathLaw_eq_piecewise_withDensity
lemma positiveRetention_referenceDeathLaw_eq_piecewise_withDensity (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) :
    referenceDeathLaw P a = volume.withDensity
      (fun t => (Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) t + (Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))))) t) := by
  have hgamma : Measurable (fun t : ℝ => gammaPDF 1 1 (t - 1)) := by
    change Measurable (fun t : ℝ => ENNReal.ofReal (gammaPDFReal 1 1 (t - 1)))
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal.comp (by fun_prop)
  have htailCore : Measurable (fun s : ℝ =>
      ENNReal.ofReal (survival P a 1 * Real.exp (-(s - 1)))) := by
    fun_prop
  have htail : Measurable ((Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1)))))) := by
    exact htailCore.indicator measurableSet_Ioi
  have htailMeasure :
      armDeathEventLaw P a (Set.Ioi 1) • shiftedUnitExpLaw =
        volume.withDensity ((Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1)))))) := by
    rw [armDeathEventLaw_apply_Ioi_one hDeath a,
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
      rw [referenceDeathLaw, armDeathEventLaw_restrict_Iic_eq_Ico hDeath a]
    _ = (volume.restrict (Set.Ico 0 1)).withDensity
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) +
        volume.withDensity ((Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1)))))) := by
      rw [positiveRetention_armDeathEventLaw_restrict_Ico_eq_withDensity c P hDeath hDeathBounds a, htailMeasure]
    _ = volume.withDensity ((Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)))) +
        volume.withDensity ((Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1)))))) := by
      change (volume.restrict (Set.Ico 0 1)).withDensity
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) + _ =
        volume.withDensity (Set.indicator (Set.Ico 0 1)
          (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) + _
      rw [withDensity_indicator measurableSet_Ico]
    _ = volume.withDensity
        (fun t => (Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) t + (Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))))) t) := by
      exact (withDensity_add_right ((Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)))) htail).symm

/-- The canonical hazard density agrees almost everywhere with the glued density. -/
-- @node: positiveRetention_referenceDeathHazard_density_ae
lemma positiveRetention_referenceDeathHazard_density_ae (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    (fun t => ENNReal.ofReal (referenceDeathHazard P a t *
      (referenceDeathLaw P a (Set.Ici t)).toReal)) =ᵐ[volume]
      (fun t => (Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) t + (Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))))) t) := by
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
      rw [referenceDeathLaw_real_Ici hDeath a htIcc]
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
      rw [referenceDeathLaw_real_Ici_of_one_lt hDeath a ht1']
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
-- @node: positiveRetention_referenceDeathLaw_eq_withDensity
lemma positiveRetention_referenceDeathLaw_eq_withDensity (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P) (a : Arm) :
    referenceDeathLaw P a = volume.withDensity (fun s =>
      ENNReal.ofReal (referenceDeathHazard P a s *
        (referenceDeathLaw P a (Set.Ici s)).toReal)) := by
  calc
    referenceDeathLaw P a = volume.withDensity
        (fun t => (Set.indicator (Ico (0 : ℝ) 1)
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t))) t + (Set.indicator (Ioi (1 : ℝ))
        (fun t => ENNReal.ofReal (survival P a 1 * Real.exp (-(t - 1))))) t) :=
      positiveRetention_referenceDeathLaw_eq_piecewise_withDensity c P hDeath hDeathBounds a
    _ = volume.withDensity (fun s =>
        ENNReal.ofReal (referenceDeathHazard P a s *
          (referenceDeathLaw P a (Set.Ici s)).toReal)) :=
      withDensity_congr_ae (positiveRetention_referenceDeathHazard_density_ae P hDeath a).symm


/-- The measurable benchmark representative satisfies the complete canonical
hazard law, derived from the source survival and absolute continuity. -/
-- @node: positiveRetention_referenceDeathLaw_hasCensorHazard
lemma positiveRetention_referenceDeathLaw_hasCensorHazard (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (a : Arm) :
    Causalean.Stat.RecurrentEvent.CountingProcess.HasCensorHazard
      (referenceDeathLaw P a) (positiveRetention_referenceHazard P hDeath a) := by
  refine ⟨referenceDeathLaw_nonnegativeTimeLaw hDeath a,
    positiveRetention_referenceHazard_measurable P hDeath a,
    positiveRetention_referenceHazard_nonneg P hDeath a,
    positiveRetention_referenceHazard_integrableOn c P hDeath hDeathBounds a, ?_⟩
  calc
    referenceDeathLaw P a = volume.withDensity (fun t =>
      ENNReal.ofReal (referenceDeathHazard P a t *
        (referenceDeathLaw P a (Ici t)).toReal)) :=
      positiveRetention_referenceDeathLaw_eq_withDensity c P hDeath hDeathBounds a
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [positiveRetention_referenceHazard_ae_eq_global P hDeath a] with t ht
      rw [ht]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

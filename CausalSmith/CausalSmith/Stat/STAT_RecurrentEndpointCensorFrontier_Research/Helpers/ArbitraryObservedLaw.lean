module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedKL

/-!
# Observed-law factorization for arbitrary admissible subject laws

This module derives the armwise product laws needed to reduce an arbitrary
subject law satisfying the paper's independence atoms to the canonical
stopped-recurrence kernels.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Death time capped at the study horizon. -/
@[no_expose]
noncomputable def cappedDeathTime (d : ℝ) : ℝ := min d 1

@[fun_prop]
lemma measurable_cappedDeathTime : Measurable cappedDeathTime :=
  measurable_id.min measurable_const

/-- The capped death time together with whether death occurred by the
horizon. -/
@[no_expose]
noncomputable def cappedDeathRecord (d : ℝ) : ℝ × Bool :=
  (cappedDeathTime d, decide (d ≤ 1))

@[fun_prop]
lemma measurable_cappedDeathRecord : Measurable cappedDeathRecord := by
  exact measurable_cappedDeathTime.prodMk
    (Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const)

/-- Same-arm recurrence, death, and censor coordinates have their threefold
product law under the recurrence/death and censoring independence atoms. -/
lemma arm_recur_death_censor_map_eq_prod (P : SubjectLaw)
    (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        ((z.recur a, z.death a), z.censor a)) =
      ((P.latent.map (fun z : LatentSubject => z.recur a)).prod
        (P.latent.map (fun z : LatentSubject => z.death a))).prod
          (P.latent.map (fun z : LatentSubject => z.censor a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hRD := (hRecurDeath a).map_prod_eq_prod_map_map
    (measurable_latentSubject_recur a).aemeasurable
    (measurable_latentSubject_death a).aemeasurable
  have hRC := (hCensor a).symm.map_prod_eq_prod_map_map
    ((measurable_latentSubject_recur a).prodMk
      (measurable_latentSubject_death a)).aemeasurable
    (measurable_latentSubject_censor a).aemeasurable
  calc
    _ = (P.latent.map (fun z : LatentSubject => (z.recur a, z.death a))).prod
        (P.latent.map (fun z : LatentSubject => z.censor a)) := hRC
    _ = _ := by rw [hRD]

/-- Random assignment factors from all latent potential-outcome coordinates. -/
lemma treatment_rest_map_eq_prod (P : SubjectLaw)
    (hRandom : RandomAssignment P) :
    P.latent.map (fun z : LatentSubject =>
        (z.treatment, (z.recur, z.death, z.censor))) =
      (P.latent.map LatentSubject.treatment).prod
        (P.latent.map (fun z : LatentSubject => (z.recur, z.death, z.censor))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  exact hRandom.map_prod_eq_prod_map_map
    measurable_latentSubject_treatment.aemeasurable
    measurable_latentSubject_rest.aemeasurable

/-- Equal hazard functions under the death-hazard atom determine the law of
the death time capped at the study horizon. -/
lemma map_cappedDeathTime_eq_of_hazard_eq
    (P Q : SubjectLaw) (hP : DeathHazard P) (hQ : DeathHazard Q)
    (hHazard : P.hazard = Q.hazard) (a : Arm) :
    P.latent.map (fun z : LatentSubject => cappedDeathTime (z.death a)) =
      Q.latent.map (fun z : LatentSubject => cappedDeathTime (z.death a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Q.latent := ⟨Q.prob⟩
  apply Measure.ext_of_Ici
  intro x
  have hm : Measurable
      (fun z : LatentSubject => cappedDeathTime (z.death a)) :=
    measurable_cappedDeathTime.comp (measurable_latentSubject_death a)
  rw [Measure.map_apply hm measurableSet_Ici,
    Measure.map_apply hm measurableSet_Ici]
  by_cases hx0 : x ≤ 0
  · have hsubP : (fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0 ⊆
        (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x := by
      intro z hz
      change x ≤ min (z.death a) 1
      exact le_min (hx0.trans hz) (hx0.trans (by norm_num))
    have hsubQ : (fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0 ⊆
        (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x := by
      intro z hz
      change x ≤ min (z.death a) 1
      exact le_min (hx0.trans hz) (hx0.trans (by norm_num))
    have htailP := hP.2.2.2.1 a 0 (by constructor <;> norm_num)
    have htailQ := hQ.2.2.2.1 a 0 (by constructor <;> norm_num)
    change (P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0)).toReal =
      survival P a 0 at htailP
    change (Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0)).toReal =
      survival Q a 0 at htailQ
    have hsurvP : survival P a 0 = 1 := by simp [survival]
    have hsurvQ : survival Q a 0 = 1 := by simp [survival]
    have hzeroP : P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0) = 1 := by
      apply (ENNReal.toReal_eq_one_iff _).mp
      simpa [measureReal_def, hsurvP] using htailP
    have hzeroQ : Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0) = 1 := by
      apply (ENNReal.toReal_eq_one_iff _).mp
      simpa [measureReal_def, hsurvQ] using htailQ
    apply le_antisymm
    · calc
        P.latent _ ≤ P.latent Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ = Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0) := hzeroQ.symm
        _ ≤ Q.latent _ := measure_mono hsubQ
    · calc
        Q.latent _ ≤ Q.latent Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ = P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0) := hzeroP.symm
        _ ≤ P.latent _ := measure_mono hsubP
  · by_cases hx1 : x ≤ 1
    · have hsetP :
          (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x =
            (fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x := by
        ext z
        simp [cappedDeathTime, hx1]
      have hsetQ :
          (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x =
            (fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x := by
        ext z
        simp [cappedDeathTime, hx1]
      have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge hx0).le, hx1⟩
      have hp := hP.2.2.2.1 a x hx
      have hq := hQ.2.2.2.1 a x hx
      change (P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x)).toReal =
        survival P a x at hp
      change (Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x)).toReal =
        survival Q a x at hq
      have hreal :
          (P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x)).toReal =
            (Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici x)).toReal := by
        rw [hp, hq]
        simp only [survival, hHazard]
      rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hreal with h | h | h
      · simpa only [hsetP, hsetQ] using h
      · exact (measure_ne_top _ _ h.2).elim
      · exact (measure_ne_top _ _ h.1).elim
    · have hemptyP :
          (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x = ∅ := by
        ext z
        simp [cappedDeathTime, lt_of_not_ge hx1]
      have hemptyQ :
          (fun z : LatentSubject => cappedDeathTime (z.death a)) ⁻¹' Set.Ici x = ∅ := by
        ext z
        simp [cappedDeathTime, lt_of_not_ge hx1]
      simpa only [hemptyP, hemptyQ] using
        (show P.latent ∅ = Q.latent ∅ by simp)

/-- Equal hazards also determine the capped death time jointly with its
horizon death indicator.  Absolute continuity removes the only ambiguous
point, death exactly at time one. -/
lemma map_cappedDeathRecord_eq_of_hazard_eq
    (P Q : SubjectLaw) (hP : DeathHazard P) (hQ : DeathHazard Q)
    (hHazard : P.hazard = Q.hazard) (a : Arm) :
    P.latent.map (fun z : LatentSubject => cappedDeathRecord (z.death a)) =
      Q.latent.map (fun z : LatentSubject => cappedDeathRecord (z.death a)) := by
  let reconstruct : ℝ → ℝ × Bool := fun d => (d, decide (d < 1))
  have hreconstruct : Measurable reconstruct := by
    exact measurable_id.prodMk
      (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const measurable_const)
  have hPae : (fun z : LatentSubject => cappedDeathRecord (z.death a)) =ᵐ[P.latent]
      fun z => reconstruct (cappedDeathTime (z.death a)) := by
    have hne : ∀ᵐ z ∂P.latent, z.death a ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp only [not_ne_iff]
      change P.latent ((fun z : LatentSubject => z.death a) ⁻¹' {(1 : ℝ)}) = 0
      rw [← Measure.map_apply (measurable_latentSubject_death a)
        (measurableSet_singleton (1 : ℝ))]
      exact (hP.2.2.1 a) (measure_singleton (1 : ℝ))
    filter_upwards [hne] with z hz
    by_cases hd : z.death a < 1
    · simp [cappedDeathRecord, cappedDeathTime, reconstruct, hd, hd.le]
    · have hgt : 1 < z.death a := lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm hz)
      simp [cappedDeathRecord, cappedDeathTime, reconstruct, hgt, hgt.le,
        not_le_of_gt hgt]
  have hQae : (fun z : LatentSubject => cappedDeathRecord (z.death a)) =ᵐ[Q.latent]
      fun z => reconstruct (cappedDeathTime (z.death a)) := by
    have hne : ∀ᵐ z ∂Q.latent, z.death a ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp only [not_ne_iff]
      change Q.latent ((fun z : LatentSubject => z.death a) ⁻¹' {(1 : ℝ)}) = 0
      rw [← Measure.map_apply (measurable_latentSubject_death a)
        (measurableSet_singleton (1 : ℝ))]
      exact (hQ.2.2.1 a) (measure_singleton (1 : ℝ))
    filter_upwards [hne] with z hz
    by_cases hd : z.death a < 1
    · simp [cappedDeathRecord, cappedDeathTime, reconstruct, hd, hd.le]
    · have hgt : 1 < z.death a := lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm hz)
      simp [cappedDeathRecord, cappedDeathTime, reconstruct, hgt, hgt.le,
        not_le_of_gt hgt]
  calc
    _ = P.latent.map (fun z : LatentSubject =>
        reconstruct (cappedDeathTime (z.death a))) := Measure.map_congr hPae
    _ = Measure.map reconstruct
        (P.latent.map (fun z : LatentSubject => cappedDeathTime (z.death a))) := by
      exact (Measure.map_map hreconstruct
        (measurable_cappedDeathTime.comp
          (measurable_latentSubject_death a))).symm
    _ = Measure.map reconstruct
        (Q.latent.map (fun z : LatentSubject => cappedDeathTime (z.death a))) := by
      rw [map_cappedDeathTime_eq_of_hazard_eq P Q hP hQ hHazard a]
    _ = Q.latent.map (fun z : LatentSubject =>
        reconstruct (cappedDeathTime (z.death a))) := by
      exact Measure.map_map hreconstruct
        (measurable_cappedDeathTime.comp (measurable_latentSubject_death a))
    _ = _ := (Measure.map_congr hQae).symm

/-- Reconstruct the observed exit time and death indicator from a capped
death record and an extended censor time. -/
@[no_expose]
noncomputable def armExitFromCapped
    (q : (ℝ × Bool) × ENNReal) : ℝ × Bool :=
  let ch := censorHorizonValue q.2
  (min q.1.1 ch, if ch = 1 then q.1.2 else decide (q.1.1 ≤ ch))

@[fun_prop]
lemma measurable_armExitFromCapped : Measurable armExitFromCapped := by
  have hch : Measurable (fun q : (ℝ × Bool) × ENNReal =>
      censorHorizonValue q.2) := measurable_censorHorizonValue.comp measurable_snd
  have hd : Measurable (fun q : (ℝ × Bool) × ENNReal => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hb : Measurable (fun q : (ℝ × Bool) × ENNReal => q.1.2) :=
    measurable_snd.comp measurable_fst
  exact (hd.min hch).prodMk (Measurable.ite
    (measurableSet_eq_fun hch measurable_const) hb
    (Measurable.ite (measurableSet_le hd hch) measurable_const measurable_const))

lemma censorHorizonValue_le_one (c : ENNReal) : censorHorizonValue c ≤ 1 := by
  unfold censorHorizonValue
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- The reconstruction from capped death data is pointwise equal to the
original armwise exit pair. -/
lemma armExitFromCapped_eq (d : ℝ) (c : ENNReal) :
    armExitFromCapped (cappedDeathRecord d, c) =
      (min d (censorHorizonValue c), decide (d ≤ censorHorizonValue c)) := by
  let ch := censorHorizonValue c
  have hch : ch ≤ 1 := censorHorizonValue_le_one c
  by_cases heq : ch = 1
  · have hmin : min (min d 1) ch = min d ch := by
      rw [heq, min_assoc, min_self]
    change
      (min (min d 1) ch, if ch = 1 then decide (d ≤ 1)
        else decide (min d 1 ≤ ch)) = (min d ch, decide (d ≤ ch))
    apply Prod.ext
    · exact hmin
    · simp [heq]
  · have hlt : ch < 1 := lt_of_le_of_ne hch heq
    have hmin : min (min d 1) ch = min d ch := by
      rw [min_assoc, min_eq_right hch]
    have hiff : min d 1 ≤ ch ↔ d ≤ ch := by
      constructor
      · intro h
        rcases (min_le_iff.mp h) with h | h
        · exact h
        · exact (not_le_of_gt hlt h).elim
      · intro h
        exact (min_le_left d 1).trans h
    change
      (min (min d 1) ch, if ch = 1 then decide (d ≤ 1)
        else decide (min d 1 ≤ ch)) = (min d ch, decide (d ≤ ch))
    apply Prod.ext
    · exact hmin
    · simp only [heq, ↓reduceIte]
      exact Bool.decide_congr hiff

/-- A finite assignment mixture is determined by its assignment law and its
selected-coordinate laws. -/
lemma map_select_prod_eq {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [Countable α] [MeasurableSingletonClass α]
    (μP μQ : Measure α) (νP νQ : Measure β)
    [SFinite νP] [SFinite νQ]
    (f : α → β → γ) (hf : ∀ a, Measurable (f a))
    (hμ : μP = μQ) (hν : ∀ a, Measure.map (f a) νP = Measure.map (f a) νQ) :
    Measure.map (fun q : α × β => (q.1, f q.1 q.2)) (μP.prod νP) =
      Measure.map (fun q : α × β => (q.1, f q.1 q.2)) (μQ.prod νQ) := by
  have hmap : Measurable (fun q : α × β => (q.1, f q.1 q.2)) := by
    apply measurable_from_prod_countable_right
    intro a
    exact measurable_const.prodMk (hf a)
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.map_apply hmap hs,
    Measure.prod_apply (hmap hs), Measure.prod_apply (hmap hs), hμ]
  apply lintegral_congr
  intro a
  have hsection : MeasurableSet {b : β | (a, f a b) ∈ s} :=
    hs.preimage (measurable_const.prodMk (hf a))
  have htarget : MeasurableSet {g : γ | (a, g) ∈ s} :=
    hs.preimage (measurable_const.prodMk measurable_id)
  have hp := congrArg (fun m : Measure γ => m {g | (a, g) ∈ s}) (hν a)
  have hp' : νP ((f a) ⁻¹' {g : γ | (a, g) ∈ s}) =
      νQ ((f a) ⁻¹' {g : γ | (a, g) ∈ s}) := by
    rw [← Measure.map_apply (hf a) htarget,
      ← Measure.map_apply (hf a) htarget]
    exact hp
  convert hp' using 1 <;> rfl

/-- The frozen assignment probabilities determine the treatment marginal. -/
lemma treatment_map_eq_of_assignment
    (P Q : SubjectLaw) (hP : AssignmentLaw P) (hQ : AssignmentLaw Q)
    (hp : P.p = Q.p) :
    P.latent.map LatentSubject.treatment =
      Q.latent.map LatentSubject.treatment := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Q.latent := ⟨Q.prob⟩
  apply Measure.ext_of_measureReal_singleton
  intro a
  change (P.latent.map LatentSubject.treatment {a}).toReal =
    (Q.latent.map LatentSubject.treatment {a}).toReal
  rw [Measure.map_apply measurable_latentSubject_treatment
      (measurableSet_singleton a),
    Measure.map_apply measurable_latentSubject_treatment
      (measurableSet_singleton a)]
  change P.latent.real {z | z.treatment = a} =
    Q.latent.real {z | z.treatment = a}
  rw [hP a, hQ a, hp]

/-- Exit data in one arm, as a function of the treatment-independent latent
block. -/
@[expose] public noncomputable def restArmExit (a : Arm)
    (r : (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) : ℝ × Bool :=
  (min (r.2.1 a) (censorHorizonValue (r.2.2 a)),
    decide (r.2.1 a ≤ censorHorizonValue (r.2.2 a)))

@[simp]
lemma restArmExit_apply (a : Arm)
    (r : (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) :
    restArmExit a r =
      (min (r.2.1 a) (censorHorizonValue (r.2.2 a)),
        decide (r.2.1 a ≤ censorHorizonValue (r.2.2 a))) := rfl

@[fun_prop]
lemma measurable_restArmExit (a : Arm) : Measurable (restArmExit a) := by
  unfold restArmExit
  have hd : Measurable (fun r :
      (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)) => r.2.1 a) :=
    (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun r :
      (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)) =>
        censorHorizonValue (r.2.2 a)) :=
    measurable_censorHorizonValue.comp
      ((measurable_pi_apply a).comp (measurable_snd.comp measurable_snd))
  exact (hd.min hc).prodMk (Measurable.ite
    (measurableSet_le hd hc) measurable_const measurable_const)

/-- Full Poisson recurrence identifies each arm's complete recurrence
configuration marginal when the arm intensities agree. -/
private lemma canonicalRecurrenceLawOf_eq
    (ν μ : Measure ℝ) [hν : IsFiniteMeasure ν] [hμ : IsFiniteMeasure μ]
    (h : ν = μ) :
    @canonicalRecurrenceLawOf ν hν = @canonicalRecurrenceLawOf μ hμ := by
  subst μ
  rfl

lemma recur_arm_map_eq_of_lam_eq
    (P Q : SubjectLaw) (hP : PoissonRecurrence P) (hQ : PoissonRecurrence Q)
    (hLam : P.lam = Q.lam) (a : Arm) :
    P.latent.map (fun z : LatentSubject => z.recur a) =
      Q.latent.map (fun z : LatentSubject => z.recur a) := by
  rcases (hP a).2.2 with ⟨hfinP, hmapP⟩
  rcases (hQ a).2.2 with ⟨hfinQ, hmapQ⟩
  rw [hmapP, hmapQ]
  have hi : recurrenceIntensity P a = recurrenceIntensity Q a := by
    simp only [recurrenceIntensity, hLam]
  exact canonicalRecurrenceLawOf_eq _ _ hi

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

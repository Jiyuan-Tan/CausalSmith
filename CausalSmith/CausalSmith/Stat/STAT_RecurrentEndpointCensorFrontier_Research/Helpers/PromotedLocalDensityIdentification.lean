module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PrimitiveCountCompaction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExitIntegration

/-! # Local promoted event-measure and density identification -/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Equality of lower-ray masses through `T`, together with no mass below
zero, identifies restrictions to `[0,T]`. -/
lemma restrict_Icc_eq_of_Iic_eq
    (μ ν : Measure ℝ) {T : ℝ} (hT0 : 0 ≤ T)
    (hμneg : μ (Set.Iio 0) = 0) (hνneg : ν (Set.Iio 0) = 0)
    (hμfin : μ (Set.Icc 0 T) < ∞)
    (hcdf : ∀ u, 0 ≤ u → u ≤ T → μ (Set.Iic u) = ν (Set.Iic u)) :
    μ.restrict (Set.Icc 0 T) = ν.restrict (Set.Icc 0 T) := by
  letI : Fact (μ (Set.Icc 0 T) < ∞) := ⟨hμfin⟩
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases ht : t < 0
  · have he : Set.Iic t ∩ Set.Icc 0 T = ∅ := by
      ext x
      constructor
      · rintro ⟨hxt, hx0, -⟩
        have hxt' : x ≤ t := hxt
        exact False.elim (by linarith)
      · intro hx
        exact hx.elim
    rw [he, measure_empty, measure_empty]
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    let u := min t T
    have hu0 : 0 ≤ u := le_min ht0 hT0
    have huT : u ≤ T := min_le_right _ _
    have he : Set.Iic t ∩ Set.Icc 0 T = Set.Icc 0 u := by
      ext x
      constructor
      · rintro ⟨hxt, hx0, hxT⟩
        exact ⟨hx0, le_min hxt hxT⟩
      · rintro ⟨hx0, hxu⟩
        exact ⟨hxu.trans (min_le_left _ _), hx0,
          hxu.trans (min_le_right _ _)⟩
    rw [he]
    have hsub : Set.Icc 0 u ⊆ Set.Iic u := fun x hx ↦ hx.2
    have hdiff : Set.Iic u \ Set.Icc 0 u ⊆ Set.Iio 0 := by
      intro x hx
      simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Icc, Set.mem_Iio] at hx ⊢
      exact lt_of_not_ge (fun hx0 ↦ hx.2 ⟨hx0, hx.1⟩)
    rw [measure_eq_measure_of_null_sdiff hsub (measure_mono_null hdiff hμneg),
      measure_eq_measure_of_null_sdiff hsub (measure_mono_null hdiff hνneg),
      hcdf u hu0 huT]

/-- Promoted recurrence-event mass is finite on every compact sub-horizon
interval. -/
lemma promotedArmModel_recurrenceEventMeasure_Icc_lt_top
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (promotedArmModel P hP a).recurrenceEventMeasure () (Set.Icc 0 T) < ∞ := by
  let M := promotedArmModel P hP a
  letI := M.armProb
  letI := M.deathProb
  letI := M.censorProb
  have hsubset : Set.Icc (0 : ℝ) T ⊆ Set.Iic T := fun _ hx ↦ hx.2
  apply (measure_mono hsubset).trans_lt
  change M.recurrenceEventMeasure () (Set.Iic T) < ∞
  rw [M.recurrence_event_measure_primitive () (Set.Iic T) measurableSet_Iic,
    M.recurrence_primitive_strict_tail () (Set.Iic T) measurableSet_Iic]
  let s : Set ℝ := Set.Iic T ∩ Set.Ico 0 M.horizon
  have hsfin : volume s < ∞ := by
    apply lt_of_le_of_lt (measure_mono Set.inter_subset_right)
    simp [s, M, Real.volume_Ico]
  letI : Fact (volume s < ∞) := ⟨hsfin⟩
  have hmono : (∫⁻ t in s, M.armLaw {()} * M.deathLaw (Set.Ioi t) *
      M.censorLaw (Set.Ioi t) * (M.intensity t : ℝ≥0∞) ∂volume) ≤
      ∫⁻ _t in s, (Real.toNNReal c.lambdaMax : ℝ≥0∞) ∂volume := by
    apply setLIntegral_mono measurable_const
    intro t ht
    have hprob : M.armLaw {()} * M.deathLaw (Set.Ioi t) *
        M.censorLaw (Set.Ioi t) ≤ 1 := by
      have hab : M.armLaw {()} * M.deathLaw (Set.Ioi t) ≤ 1 * 1 :=
        mul_le_mul prob_le_one prob_le_one bot_le bot_le
      have habc : M.armLaw {()} * M.deathLaw (Set.Ioi t) *
          M.censorLaw (Set.Ioi t) ≤ (1 * 1) * 1 :=
        mul_le_mul hab prob_le_one bot_le bot_le
      simpa using habc
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨ht.2.1, ?_⟩
      have hle := ht.2.2.le
      have hM : M.horizon = 1 := promotedArmModel_horizon P hP a
      rw [hM] at hle
      exact hle
    have hiR : (M.intensity t : ℝ) ≤ c.lambdaMax := by
      rw [promotedArmModel_intensity, promotedArmIntensity_coe hP a htIcc]
      exact (hP.recurrenceBounds a t htIcc).2
    have hmax0 : 0 ≤ c.lambdaMax :=
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
    have hiNN : M.intensity t ≤ Real.toNNReal c.lambdaMax := by
      change (M.intensity t : ℝ) ≤ (Real.toNNReal c.lambdaMax : ℝ)
      simpa [Real.coe_toNNReal _ hmax0] using hiR
    have hi : (M.intensity t : ℝ≥0∞) ≤
        (Real.toNNReal c.lambdaMax : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hiNN
    calc
      _ ≤ 1 * (M.intensity t : ℝ≥0∞) := by gcongr
      _ ≤ 1 * (Real.toNNReal c.lambdaMax : ℝ≥0∞) := by gcongr
      _ = _ := by simp
  have hconst : (∫⁻ _t in s,
      (Real.toNNReal c.lambdaMax : ℝ≥0∞) ∂volume) < ∞ := by
    change (∫⁻ _t, (Real.toNNReal c.lambdaMax : ℝ≥0∞)
      ∂volume.restrict s) < ∞
    exact lintegral_const_lt_top ENNReal.coe_ne_top
  exact hmono.trans_lt hconst

/-- Promoted death-event mass is finite on every compact sub-horizon interval. -/
lemma promotedArmModel_deathEventMeasure_Icc_lt_top
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (promotedArmModel P hP a).deathEventMeasure () (Set.Icc 0 T) < ∞ := by
  have hsubset : Set.Icc (0 : ℝ) T ⊆ Set.Iic T := fun _ hx ↦ hx.2
  apply (measure_mono hsubset).trans_lt
  change (promotedArmModel P hP a).deathEventMeasure () (Set.Iic T) < ∞
  rw [hP.promotedArmModel_deathEventMeasure_Iic a hT1]
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  exact (prob_le_one.trans_lt ENNReal.one_lt_top)

/-- A promoted arm has no risk-set mass before time zero. -/
lemma promotedArmModel_riskSetMeasure_Iio_zero
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) :
    (promotedArmModel P hP a).riskSetMeasure () (Set.Iio 0) = 0 := by
  let M := promotedArmModel P hP a
  unfold Causalean.Stat.RecurrentEvent.Model.riskSetMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  have he : Set.Ico (0 : ℝ) M.horizon ∩ Set.Iio 0 = ∅ := by
    ext t
    constructor
    · rintro ⟨ht, ht0⟩
      exact False.elim (lt_irrefl 0 (ht.1.trans_lt ht0))
    · intro ht
      exact ht.elim
  rw [Measure.restrict_restrict measurableSet_Iio, inter_comm, he,
    Measure.restrict_empty, lintegral_zero_measure]

lemma promotedArmModel_deathEventMeasure_Iio_zero
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) :
    (promotedArmModel P hP a).deathEventMeasure () (Set.Iio 0) = 0 := by
  let M := promotedArmModel P hP a
  rw [M.death_event_density, withDensity_apply _ measurableSet_Iio]
  rw [show (M.riskSetMeasure ()).restrict (Set.Iio 0) = 0 by
    exact Measure.restrict_eq_zero.mpr
      (promotedArmModel_riskSetMeasure_Iio_zero hP a)]
  simp

lemma promotedArmModel_recurrenceEventMeasure_Iio_zero
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) :
    (promotedArmModel P hP a).recurrenceEventMeasure () (Set.Iio 0) = 0 := by
  let M := promotedArmModel P hP a
  rw [M.recurrence_event_density, withDensity_apply _ measurableSet_Iio]
  rw [show (M.riskSetMeasure ()).restrict (Set.Iio 0) = 0 by
    exact Measure.restrict_eq_zero.mpr
      (promotedArmModel_riskSetMeasure_Iio_zero hP a)]
  simp

/-- Equal paper observed laws identify promoted death-event measures on each
compact sub-horizon interval. -/
lemma promotedArmModel_deathEventMeasure_restrict_Icc_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ((promotedArmModel P hP a).deathEventMeasure ()).restrict (Set.Icc 0 T) =
      ((promotedArmModel Q hQ a).deathEventMeasure ()).restrict (Set.Icc 0 T) := by
  apply restrict_Icc_eq_of_Iic_eq _ _ hT0
    (promotedArmModel_deathEventMeasure_Iio_zero hP a)
    (promotedArmModel_deathEventMeasure_Iio_zero hQ a)
    (promotedArmModel_deathEventMeasure_Icc_lt_top hP a hT0 hT1)
  intro u hu0 huT
  exact promotedArmModel_deathEventMeasure_Iic_eq_of_observedLaw_eq
    hP hQ hobs a (huT.trans_lt hT1)

/-- Equal paper observed laws identify promoted recurrence-event measures on
each compact sub-horizon interval. -/
lemma promotedArmModel_recurrenceEventMeasure_restrict_Icc_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ((promotedArmModel P hP a).recurrenceEventMeasure ()).restrict (Set.Icc 0 T) =
      ((promotedArmModel Q hQ a).recurrenceEventMeasure ()).restrict (Set.Icc 0 T) := by
  apply restrict_Icc_eq_of_Iic_eq _ _ hT0
    (promotedArmModel_recurrenceEventMeasure_Iio_zero hP a)
    (promotedArmModel_recurrenceEventMeasure_Iio_zero hQ a)
    (promotedArmModel_recurrenceEventMeasure_Icc_lt_top hP a hT0 hT1)
  intro u _ _
  exact promotedArmModel_recurrenceEventMeasure_Iic_eq_of_observedLaw_eq
    hP hQ hobs a u

/-- Equal paper observed laws identify the promoted hazard and recurrence
intensity almost everywhere on every compact interval below the horizon. -/
lemma promotedArmModel_densities_ae_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (promotedArmModel P hP a).hazard t =
          (promotedArmModel Q hQ a).hazard t ∧
        (promotedArmModel P hP a).intensity t =
          (promotedArmModel Q hQ a).intensity t := by
  let M := promotedArmModel P hP a
  let N := promotedArmModel Q hQ a
  let s : Set ℝ := Set.Icc 0 T
  let wM : ℝ → ℝ≥0∞ := fun t =>
    M.armLaw {()} * M.deathLaw (Set.Ici t) * M.censorLaw (Set.Ici t)
  have hrisk : M.riskSetMeasure () = N.riskSetMeasure () :=
    promotedArmModel_riskSetMeasure_eq_of_observedLaw_eq hP hQ hobs a
  have hdeath : (M.deathEventMeasure ()).restrict s =
      (N.deathEventMeasure ()).restrict s :=
    promotedArmModel_deathEventMeasure_restrict_Icc_eq_of_observedLaw_eq
      hP hQ hobs a hT0 hT1
  have hrec : (M.recurrenceEventMeasure ()).restrict s =
      (N.recurrenceEventMeasure ()).restrict s :=
    promotedArmModel_recurrenceEventMeasure_restrict_Icc_eq_of_observedLaw_eq
      hP hQ hobs a hT0 hT1
  have htail (ν : Measure ℝ) : Measurable (fun t : ℝ => ν (Set.Ici t)) :=
    Antitone.measurable (fun x y hxy => measure_mono (Set.Ici_subset_Ici.mpr hxy))
  have hw : Measurable wM := by
    dsimp [wM]
    exact (measurable_const.mul (htail M.deathLaw)).mul (htail M.censorLaw)
  letI := M.armProb
  letI := M.deathProb
  letI := M.censorProb
  have hfinite : ∀ t, wM t ≠ ⊤ := by
    intro t
    dsimp [wM]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (measure_ne_top M.armLaw {()})
        (measure_ne_top M.deathLaw (Set.Ici t)))
      (measure_ne_top M.censorLaw (Set.Ici t))
  have hsM : s ⊆ Set.Ico (0 : ℝ) M.horizon := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have hM : M.horizon = 1 := promotedArmModel_horizon P hP a
    rw [hM]
    exact ht.2.trans_lt hT1
  have heq : (M.riskSetMeasure ()).restrict s =
      (volume.restrict s).withDensity wM := by
    change ((volume.restrict (Set.Ico 0 M.horizon)).withDensity wM).restrict s = _
    rw [restrict_withDensity measurableSet_Icc,
      Measure.restrict_restrict_of_subset hsM]
  haveI : SigmaFinite ((M.riskSetMeasure ()).restrict s) := by
    rw [heq]
    exact SigmaFinite.withDensity_of_ne_top
      (Filter.Eventually.of_forall hfinite)
  have hmh : (fun t => (M.hazard t : ℝ≥0∞)) =ᵐ[(M.riskSetMeasure ()).restrict s]
      (fun t => (N.hazard t : ℝ≥0∞)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      M.measurable_hazard.coe_nnreal_ennreal.aemeasurable
      N.measurable_hazard.coe_nnreal_ennreal.aemeasurable).mp
    calc
      _ = (M.deathEventMeasure ()).restrict s := by
        rw [← restrict_withDensity measurableSet_Icc, ← M.death_event_density]
      _ = (N.deathEventMeasure ()).restrict s := hdeath
      _ = _ := by
        rw [N.death_event_density, restrict_withDensity measurableSet_Icc, ← hrisk]
  have hmi : (fun t => (M.intensity t : ℝ≥0∞)) =ᵐ[(M.riskSetMeasure ()).restrict s]
      (fun t => (N.intensity t : ℝ≥0∞)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      M.measurable_intensity.coe_nnreal_ennreal.aemeasurable
      N.measurable_intensity.coe_nnreal_ennreal.aemeasurable).mp
    calc
      _ = (M.recurrenceEventMeasure ()).restrict s := by
        rw [← restrict_withDensity measurableSet_Icc, ← M.recurrence_event_density]
      _ = (N.recurrenceEventMeasure ()).restrict s := hrec
      _ = _ := by
        rw [N.recurrence_event_density, restrict_withDensity measurableSet_Icc, ← hrisk]
  have hcM : ∀ t ∈ s, 0 < M.censorLaw (Set.Ici t) := by
    intro t ht
    rw [promotedArmModel_censorLaw, Measure.map_apply]
    · have hevent : (fun z : LatentSubject ↦ censorHorizon z a) ⁻¹' Set.Ici t =
          {z | ENNReal.ofReal t ≤ z.censor a} := by
        ext z
        exact le_censorHorizonValue_iff (z.censor a) t ht.1
          (ht.2.trans_lt hT1).le
      rw [hevent]
      have hp := retention_pos_of_modelClass c P hP a t ht.1
        (ht.2.trans_lt hT1)
      unfold retention at hp
      exact (ENNReal.toReal_pos_iff.mp hp).1
    · fun_prop
    · exact measurableSet_Ici
  have hpos : ∀ t ∈ s, wM t ≠ 0 := by
    intro t ht
    have hd : 0 < M.deathLaw (Set.Ici t) := by
      have htle : t ≤ M.horizon := by
        have hM : M.horizon = 1 := promotedArmModel_horizon P hP a
        rw [hM]
        exact (ht.2.trans_lt hT1).le
      rw [M.death_survival t ⟨ht.1, htle⟩]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    have ha : 0 < M.armLaw ({()} : Set Unit) := by simp [M]
    exact (ENNReal.mul_pos
      (ne_of_gt (ENNReal.mul_pos (ne_of_gt ha) (ne_of_gt hd)))
      (ne_of_gt (hcM t ht))).ne'
  have hmh' := (ae_withDensity_iff hw).mp (heq ▸ hmh)
  have hmi' := (ae_withDensity_iff hw).mp (heq ▸ hmi)
  filter_upwards [hmh', hmi', ae_restrict_mem measurableSet_Icc] with t hh hi ht
  exact ⟨by exact_mod_cast (hh (hpos t ht)),
    by exact_mod_cast (hi (hpos t ht))⟩

/-- The promoted a.e. result transports back to the paper hazard and
recurrence-intensity fields. -/
lemma ModelClass.densities_ae_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      P.hazard a t = Q.hazard a t ∧ P.lam a t = Q.lam a t := by
  have hprom := promotedArmModel_densities_ae_eq_of_observedLaw_eq
    hP hQ hobs a hT0 hT1
  filter_upwards [hprom, ae_restrict_mem measurableSet_Icc] with t heq ht
  have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT1.le⟩
  have hhprom : promotedArmHazard P a t = promotedArmHazard Q a t := by
    simpa only [promotedArmModel_hazard] using heq.1
  have hiprom : promotedArmIntensity P a t = promotedArmIntensity Q a t := by
    simpa only [promotedArmModel_intensity] using heq.2
  constructor
  · calc
      P.hazard a t = (promotedArmHazard P a t : ℝ) :=
        (promotedArmHazard_coe hP a ht1).symm
      _ = (promotedArmHazard Q a t : ℝ) :=
        congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hhprom
      _ = Q.hazard a t := promotedArmHazard_coe hQ a ht1
  · calc
      P.lam a t = (promotedArmIntensity P a t : ℝ) :=
        (promotedArmIntensity_coe hP a ht1).symm
      _ = (promotedArmIntensity Q a t : ℝ) :=
        congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hiprom
      _ = Q.lam a t := promotedArmIntensity_coe hQ a ht1

/-- On a nondegenerate compact sub-horizon interval, continuity upgrades the
a.e. identified paper densities to pointwise equality. -/
lemma ModelClass.densities_eqOn_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {T : ℝ} (hT0 : 0 < T) (hT1 : T < 1) :
    Set.EqOn (P.hazard a) (Q.hazard a) (Set.Icc (0 : ℝ) T) ∧
      Set.EqOn (P.lam a) (Q.lam a) (Set.Icc (0 : ℝ) T) := by
  have hae := hP.densities_ae_eq_of_observedLaw_eq hQ hobs a hT0.le hT1
  have hh : P.hazard a =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] Q.hazard a :=
    hae.mono fun _ h ↦ h.1
  have hi : P.lam a =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] Q.lam a :=
    hae.mono fun _ h ↦ h.2
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hT1.le⟩
  constructor
  · exact Measure.eqOn_Icc_of_ae_eq volume hT0.ne hh
      ((hP.deathContinuousOn a).mono hsub)
      ((hQ.deathContinuousOn a).mono hsub)
  · exact Measure.eqOn_Icc_of_ae_eq volume hT0.ne hi
      ((hP.recurrenceContinuousOn a).mono hsub)
      ((hQ.recurrenceContinuousOn a).mono hsub)


end CausalSmith.Stat.RecurrentEndpointCensorFrontier

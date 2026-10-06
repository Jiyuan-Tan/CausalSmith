module
public import Causalean.Stat.RecurrentEvent.HazardDensity
public import Causalean.Stat.RecurrentEvent.Observation

/-!
# Primitive representation of observed death events

The observed death-time pushforward is reduced to the independent primitive
arm, death, and censor laws before the hazard-density step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) determine [the
observed armwise death-event measure](goal), the distribution of exit times
whose recorded exit is death. -/
noncomputable def Model.deathEventMeasure (M : Model A X) (a : A) : Measure ℝ :=
  Measure.map (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) => y.2.1)
    (M.observedLaw.restrict {y | y.1 = a ∧ y.2.2.1 = true})

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) have [an observed
death-event measure equal to the primitive death-time law restricted to
assigned subjects whose death occurs before censoring and the horizon](goal). -/
theorem Model.death_event_measure_primitive (M : Model A X) (a : A) :
    M.deathEventMeasure a =
      Measure.map (fun ω : Outcome A X => ω.2.2.1)
        (M.primitiveLaw.restrict
          {ω | ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon}) := by
  let s : Set (A × (ℝ × (Bool × (ℕ → ℝ)))) :=
    {y | y.1 = a ∧ y.2.2.1 = true}
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  have hpre : M.observe ⁻¹' s =
      {ω : Outcome A X | ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧
        ω.2.2.1 < M.horizon} := by
    ext ω
    simp [s, Model.observe]
  have hmeas : Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) => y.2.1) := by
    fun_prop
  have htime : Measurable (fun ω : Outcome A X => ω.2.2.1) := by
    fun_prop
  unfold Model.deathEventMeasure Model.observedLaw
  rw [Measure.restrict_map M.measurable_observe hs,
    Measure.map_map hmeas M.measurable_observe, hpre]
  apply Measure.map_congr
  apply ae_restrict_of_forall_mem (hs := by
    rw [← hpre]
    exact hs.preimage M.measurable_observe)
  intro ω hω
  have hd : ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon := ⟨hω.2.1, hω.2.2⟩
  have hdh : ω.2.2.1 ≤ M.horizon := le_of_lt hd.2
  simp [Function.comp, Model.observe, Model.stopTime, hd, hdh]

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) have [a primitive
recorded-death measure equal to the open-horizon death law weighted by
assignment mass and censoring retention](goal). -/
theorem Model.death_primitive_weighted (M : Model A X) (a : A) :
    Measure.map (fun ω : Outcome A X => ω.2.2.1)
        (M.primitiveLaw.restrict
          {ω | ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon}) =
      (M.deathLaw.restrict (Ico 0 M.horizon)).withDensity
        (fun t => M.armLaw {a} * M.censorLaw (Ici t)) := by
  letI := M.armProb
  letI := M.pointProb
  letI := M.deathProb
  letI := M.censorProb
  have hzero : M.deathLaw (Ici (0 : ℝ)) = 1 := by
    simpa [hazardSurvival] using
      (M.death_survival 0 ⟨le_rfl, M.horizon_nonneg⟩)
  have hnonneg : ∀ᵐ t ∂M.deathLaw, 0 ≤ t := by
    rw [ae_iff]
    have hc : M.deathLaw (Ici (0 : ℝ))ᶜ = 0 := by
      rw [measure_compl measurableSet_Ici (by simp), hzero]
      simp
    have hset : {t : ℝ | ¬ 0 ≤ t} = (Ici (0 : ℝ))ᶜ := by
      ext t
      simp
    simpa only [hset] using hc
  apply Measure.ext
  intro s hs
  let E : Set (ℝ × ℝ) := {p | p.1 ∈ s ∧ p.1 ≤ p.2 ∧ p.1 < M.horizon}
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  have htime : Measurable (fun ω : Outcome A X => ω.2.2.1) := by
    fun_prop
  have hset : {ω : Outcome A X |
      (ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon) ∧
        ω.2.2.1 ∈ s} =
      ({a} : Set A) ×ˢ (univ ×ˢ E) := by
    ext ω
    simp [E, and_comm, and_assoc]
  have hleft :
      (Measure.map (fun ω : Outcome A X => ω.2.2.1)
        (M.primitiveLaw.restrict
          {ω | ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon})) s =
        M.armLaw {a} * (M.deathLaw.prod M.censorLaw) E := by
    rw [Measure.map_apply htime hs, Measure.restrict_apply (hs.preimage htime)]
    rw [Set.inter_comm]
    change M.primitiveLaw {ω : Outcome A X |
      (ω.1 = a ∧ ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon) ∧
        ω.2.2.1 ∈ s} = _
    rw [hset]
    unfold Model.primitiveLaw
    rw [Measure.prod_prod, Measure.prod_prod]
    simp
  rw [hleft]
  have hsection (t : ℝ) : M.censorLaw (Prod.mk t ⁻¹' E) =
      (s ∩ Iio M.horizon).indicator (fun u => M.censorLaw (Ici u)) t := by
    by_cases ht : t ∈ s ∩ Iio M.horizon
    · have heq : Prod.mk t ⁻¹' E = Ici t := by
        ext c
        have hlt : t < M.horizon := ht.2
        simp [E, ht.1, hlt]
      simp [heq, ht]
    · have heq : Prod.mk t ⁻¹' E = ∅ := by
        ext c
        have hfail : t ∉ s ∨ ¬ t < M.horizon := by
          simpa [Set.mem_inter_iff] using (not_and_or.mp ht)
        rcases hfail with hns | hge
        · simp [E, hns]
        · simp [E, hge]
      simp [heq, ht]
  have hprod : (M.deathLaw.prod M.censorLaw) E =
      ∫⁻ t in s ∩ Iio M.horizon, M.censorLaw (Ici t) ∂M.deathLaw := by
    rw [Measure.prod_apply hE]
    simp_rw [hsection]
    exact lintegral_indicator (hs.inter measurableSet_Iio) _
  have hsupport : M.deathLaw.restrict (s ∩ Iio M.horizon) =
      M.deathLaw.restrict (s ∩ Ico 0 M.horizon) := by
    apply Measure.restrict_congr_set
    filter_upwards [hnonneg] with t ht
    change (t ∈ s ∧ t < M.horizon) = (t ∈ s ∧ 0 ≤ t ∧ t < M.horizon)
    apply propext
    tauto
  have htail : Measurable (fun t : ℝ => M.censorLaw (Ici t)) := by
    let F : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}
    have hF : MeasurableSet F := by
      dsimp [F]
      measurability
    have hf := measurable_measure_prodMk_left (ν := M.censorLaw) hF
    convert hf using 1
    funext t
    congr 1
  rw [hprod, withDensity_apply _ hs]
  rw [lintegral_const_mul (M.armLaw {a}) htail]
  rw [Measure.restrict_restrict hs]
  rw [hsupport]


end Causalean.Stat.RecurrentEvent

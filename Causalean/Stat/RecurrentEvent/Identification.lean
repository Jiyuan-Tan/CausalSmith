module
public import Causalean.Stat.RecurrentEvent.DeathDensity
public import Causalean.Stat.RecurrentEvent.RecurrenceDensity

/-!
# Identification of recurrent-event intensities

Equal observed stopped-history laws identify hazard and recurrence intensity
almost everywhere where the common observable risk set is positive.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [Two recurrent-event models](hyp:M,N), [an arm](hyp:a), and [a
nonnegative compact sub-horizon time](hyp:T,hT0,hTM,hTN) with [equal
stopped-history laws](hyp:hobs), [positive assignment mass](hyp:haM,haN),
and [positive censoring retention throughout that interval](hyp:hcM,hcN)
have [equal death hazards and recurrence intensities Lebesgue-almost
everywhere on the interval](goal). -/
theorem Model.identify_densities (M : Model A X) (N : Model A Y) (a : A)
    (T : ℝ) (hT0 : 0 ≤ T) (hTM : T < M.horizon) (hTN : T < N.horizon)
    (hobs : M.observedLaw = N.observedLaw)
    (haM : 0 < M.armLaw {a}) (haN : 0 < N.armLaw {a})
    (hcM : ∀ t ∈ Icc (0 : ℝ) T, 0 < M.censorLaw (Ici t))
    (hcN : ∀ t ∈ Icc (0 : ℝ) T, 0 < N.censorLaw (Ici t)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      M.hazard t = N.hazard t ∧ M.intensity t = N.intensity t := by
  let s : Set ℝ := Icc 0 T
  let wM : ℝ → ℝ≥0∞ := fun t => M.armLaw {a} * M.deathLaw (Ici t) * M.censorLaw (Ici t)
  let wN : ℝ → ℝ≥0∞ := fun t => N.armLaw {a} * N.deathLaw (Ici t) * N.censorLaw (Ici t)
  have hsM : s ⊆ Ico 0 M.horizon := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTM⟩
  have hsN : s ⊆ Ico 0 N.horizon := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTN⟩
  have hw : ∀ t ∈ s, wM t = wN t := by
    intro t ht
    calc
      wM t = M.riskProbability a t := (M.risk_factorization a t ⟨ht.1, le_trans ht.2 hTM.le⟩).symm
      _ = N.riskProbability a t := by simp [Model.riskProbability, hobs]
      _ = wN t := N.risk_factorization a t ⟨ht.1, le_trans ht.2 hTN.le⟩
  have hrisk : (M.riskSetMeasure a).restrict s = (N.riskSetMeasure a).restrict s := by
    change ((volume.restrict (Ico 0 M.horizon)).withDensity wM).restrict s =
      ((volume.restrict (Ico 0 N.horizon)).withDensity wN).restrict s
    rw [restrict_withDensity measurableSet_Icc, restrict_withDensity measurableSet_Icc,
      Measure.restrict_restrict_of_subset hsM, Measure.restrict_restrict_of_subset hsN]
    exact withDensity_congr_ae ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hw t ht)
  have hdeath : M.deathEventMeasure a = N.deathEventMeasure a := by
    simp only [Model.deathEventMeasure, hobs]
  have hrec : M.recurrenceEventMeasure a = N.recurrenceEventMeasure a := by
    simp only [Model.recurrenceEventMeasure, hobs]
  have htail (ν : Measure ℝ) : Measurable (fun t : ℝ => ν (Ici t)) :=
    Antitone.measurable (fun x y hxy => measure_mono (Ici_subset_Ici.mpr hxy))
  have hmeas : Measurable wM := by
    dsimp [wM]
    exact (measurable_const.mul (htail M.deathLaw)).mul (htail M.censorLaw)
  letI := M.armProb
  letI := M.deathProb
  letI := M.censorProb
  have hfinite : ∀ t, wM t ≠ ⊤ := by
    intro t
    dsimp [wM]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (measure_ne_top M.armLaw {a})
        (measure_ne_top M.deathLaw (Ici t)))
      (measure_ne_top M.censorLaw (Ici t))
  haveI : SigmaFinite ((M.riskSetMeasure a).restrict s) := by
    have heq : (M.riskSetMeasure a).restrict s = (volume.restrict s).withDensity wM := by
      change ((volume.restrict (Ico 0 M.horizon)).withDensity wM).restrict s = _
      rw [restrict_withDensity measurableSet_Icc, Measure.restrict_restrict_of_subset hsM]
    rw [heq]
    exact SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall hfinite)
  have hmh : (fun t => (M.hazard t : ℝ≥0∞)) =ᵐ[(M.riskSetMeasure a).restrict s]
      (fun t => (N.hazard t : ℝ≥0∞)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      M.measurable_hazard.coe_nnreal_ennreal.aemeasurable
      N.measurable_hazard.coe_nnreal_ennreal.aemeasurable).mp
    calc
      _ = (M.deathEventMeasure a).restrict s := by
        rw [← restrict_withDensity measurableSet_Icc, ← M.death_event_density]
      _ = (N.deathEventMeasure a).restrict s := by rw [hdeath]
      _ = _ := by
        rw [N.death_event_density, restrict_withDensity measurableSet_Icc, ← hrisk]
  have hmi : (fun t => (M.intensity t : ℝ≥0∞)) =ᵐ[(M.riskSetMeasure a).restrict s]
      (fun t => (N.intensity t : ℝ≥0∞)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      M.measurable_intensity.coe_nnreal_ennreal.aemeasurable
      N.measurable_intensity.coe_nnreal_ennreal.aemeasurable).mp
    calc
      _ = (M.recurrenceEventMeasure a).restrict s := by
        rw [← restrict_withDensity measurableSet_Icc, ← M.recurrence_event_density]
      _ = (N.recurrenceEventMeasure a).restrict s := by rw [hrec]
      _ = _ := by
        rw [N.recurrence_event_density, restrict_withDensity measurableSet_Icc, ← hrisk]
  have hpos : ∀ t ∈ s, wM t ≠ 0 := by
    intro t ht
    have hd : 0 < M.deathLaw (Ici t) := by
      rw [M.death_survival t ⟨ht.1, le_trans ht.2 hTM.le⟩]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    exact (ENNReal.mul_pos (ne_of_gt (ENNReal.mul_pos (ne_of_gt haM) (ne_of_gt hd)))
      (ne_of_gt (hcM t ht))).ne'
  have heq : (M.riskSetMeasure a).restrict s = (volume.restrict s).withDensity wM := by
    change ((volume.restrict (Ico 0 M.horizon)).withDensity wM).restrict s = _
    rw [restrict_withDensity measurableSet_Icc, Measure.restrict_restrict_of_subset hsM]
  have hmh' := (ae_withDensity_iff hmeas).mp (heq ▸ hmh)
  have hmi' := (ae_withDensity_iff hmeas).mp (heq ▸ hmi)
  filter_upwards [hmh', hmi', ae_restrict_mem measurableSet_Icc] with t hh hi ht
  exact ⟨by exact_mod_cast (hh (hpos t ht)), by exact_mod_cast (hi (hpos t ht))⟩


end Causalean.Stat.RecurrentEvent

module
public import Causalean.Stat.RecurrentEvent.RecurrenceEventPrimitive
public import Causalean.Stat.RecurrentEvent.RiskSet
public import Causalean.Stat.RecurrentEvent.TailRetention

/-!
# Observable recurrence-event intensity density

A finite Poisson recurrence sample stopped at independent death and censor
times has observable event intensity relative to the armwise risk set.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) have [an observable
recurrence-event measure with primitive Poisson intensity as density relative
to the armwise risk-set measure](goal). -/
theorem Model.recurrence_event_density (M : Model A X) (a : A) :
    M.recurrenceEventMeasure a =
      (M.riskSetMeasure a).withDensity (fun t => (M.intensity t : ℝ≥0∞)) := by
  letI := M.deathProb
  letI := M.censorProb
  let μ : Measure ℝ := volume.restrict (Ico 0 M.horizon)
  let w : ℝ → ℝ≥0∞ := fun t =>
    M.armLaw {a} * M.deathLaw (Ici t) * M.censorLaw (Ici t)
  let h : ℝ → ℝ≥0∞ := fun t => (M.intensity t : ℝ≥0∞)
  have hdeath : Measurable (fun t : ℝ => M.deathLaw (Ici t)) :=
    Antitone.measurable (fun _ _ hxy => measure_mono (Ici_subset_Ici.mpr hxy))
  have hcensor : Measurable (fun t : ℝ => M.censorLaw (Ici t)) :=
    Antitone.measurable (fun _ _ hxy => measure_mono (Ici_subset_Ici.mpr hxy))
  have hw : Measurable w := (measurable_const.mul hdeath).mul hcensor
  have hh : Measurable h := M.measurable_intensity.coe_nnreal_ennreal
  apply Measure.ext
  intro s hs
  calc
    M.recurrenceEventMeasure a s =
        ∫⁻ t in s ∩ Ico (0 : ℝ) M.horizon,
          M.armLaw {a} * M.deathLaw (Ioi t) * M.censorLaw (Ioi t) * h t
            ∂volume := by
      rw [M.recurrence_event_measure_primitive a s hs,
        M.recurrence_primitive_strict_tail a s hs]
    _ = ∫⁻ t in s ∩ Ico (0 : ℝ) M.horizon, w t * h t ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_measure_Ioi_eq_Ici M.deathLaw),
        ae_restrict_of_ae (ae_measure_Ioi_eq_Ici M.censorLaw)] with t hd hc
      simp only [w, hd, hc]
    _ = (μ.withDensity (w * h)) s := by
      rw [withDensity_apply _ hs]
      simp only [μ]
      rw [Measure.restrict_restrict hs]
      congr 1
    _ = ((μ.withDensity w).withDensity h) s := by
      rw [withDensity_mul₀ hw.aemeasurable hh.aemeasurable]
    _ = ((M.riskSetMeasure a).withDensity h) s := by
      rfl


end Causalean.Stat.RecurrentEvent

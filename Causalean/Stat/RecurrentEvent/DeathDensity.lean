module
public import Causalean.Stat.RecurrentEvent.DeathEventPrimitive
public import Causalean.Stat.RecurrentEvent.HazardDensity
public import Causalean.Stat.RecurrentEvent.RiskSet

/-!
# Observable death-event hazard density

Independent death and censor blocks yield the observable death-event law
with hazard density relative to the armwise risk-set measure.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) have [an observable
death-event measure with the death hazard as density relative to the armwise
risk-set measure](goal), including the empty zero-horizon case. -/
theorem Model.death_event_density (M : Model A X) (a : A) :
    M.deathEventMeasure a =
      (M.riskSetMeasure a).withDensity (fun t => (M.hazard t : ℝ≥0∞)) := by
  let μ : Measure ℝ := volume.restrict (Ico 0 M.horizon)
  let w : ℝ → ℝ≥0∞ := fun t => M.armLaw {a} * M.censorLaw (Ici t)
  let s : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (hazardSurvival M.hazard t)
  let h : ℝ → ℝ≥0∞ := fun t => (M.hazard t : ℝ≥0∞)
  have hcensor : Measurable (fun t : ℝ => M.censorLaw (Ici t)) :=
    Antitone.measurable (fun _ _ hxy => measure_mono (Ici_subset_Ici.mpr hxy))
  have hw : Measurable w := measurable_const.mul hcensor
  have hh : Measurable h := M.measurable_hazard.coe_nnreal_ennreal
  have hs : AEMeasurable s μ := by
    apply aemeasurable_restrict_of_antitoneOn measurableSet_Ico
    intro x hx y hy hxy
    change ENNReal.ofReal (hazardSurvival M.hazard y) ≤
      ENNReal.ofReal (hazardSurvival M.hazard x)
    rw [← M.death_survival x ⟨hx.1, hx.2.le⟩,
      ← M.death_survival y ⟨hy.1, hy.2.le⟩]
    exact measure_mono (Ici_subset_Ici.mpr hxy)
  have hf : AEMeasurable (s * h) μ := hs.mul hh.aemeasurable
  calc
    M.deathEventMeasure a = (M.deathLaw.restrict (Ico 0 M.horizon)).withDensity w := by
      rw [M.death_event_measure_primitive, M.death_primitive_weighted]
    _ = (μ.withDensity (s * h)).withDensity w := by
      rw [M.death_law_restrict_eq_withDensity]
      rfl
    _ = μ.withDensity ((s * h) * w) := (withDensity_mul₀ hf hw.aemeasurable).symm
    _ = μ.withDensity ((w * s) * h) := by
      congr 1
      funext t
      simp only [Pi.mul_apply]
      ac_rfl
    _ = (μ.withDensity (w * s)).withDensity h :=
      withDensity_mul₀ (hw.aemeasurable.mul hs) hh.aemeasurable
    _ = (M.riskSetMeasure a).withDensity h := by
      congr 1
      unfold Model.riskSetMeasure μ w s
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      simp only [Pi.mul_apply]
      rw [M.death_survival t ⟨ht.1, ht.2.le⟩]
      ac_rfl


end Causalean.Stat.RecurrentEvent

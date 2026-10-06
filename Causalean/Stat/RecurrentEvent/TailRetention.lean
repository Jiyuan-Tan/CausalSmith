module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Strict and weak retention for finite exit laws

A finite real-time law has only countably many atoms. Therefore its strict
and weak tail probabilities agree at Lebesgue-almost every time. This is the
endpoint conversion used for strict stopping of recurrence points.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent

/-- [A finite exit-time law](hyp:ν) has [equal strict and weak retention
probabilities at Lebesgue-almost every time](goal), including when the law
has atoms. -/
theorem ae_measure_Ioi_eq_Ici (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ᵐ t ∂(volume : Measure ℝ), ν (Ioi t) = ν (Ici t) := by
  have hcount : {t : ℝ | 0 < ν {t}}.Countable := by
    simpa only [id_eq, ofPred_eq_eq_singleton] using
      (Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id)
  filter_upwards [hcount.ae_notMem (volume : Measure ℝ)] with t ht
  have hz : ν {t} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp ht)
  have hdecomp : Ici t = {t} ∪ Ioi t := by
    simpa only [Icc_self] using
      (Icc_union_Ioi_eq_Ici (a := t) (b := t) le_rfl).symm
  have hdisj : Disjoint ({t} : Set ℝ) (Ioi t) := by
    simp
  calc
    ν (Ioi t) = ν {t} + ν (Ioi t) := by simp [hz]
    _ = ν ({t} ∪ Ioi t) := (measure_union hdisj measurableSet_Ioi).symm
    _ = ν (Ici t) := by rw [← hdecomp]

end Causalean.Stat.RecurrentEvent

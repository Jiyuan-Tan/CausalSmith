module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessBridge
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationContinuity

/-!
# A global reference extension of the paper's death hazard

This module extends the paper's arm-specific death hazard from its identified
window `[0, 1]` to a measurable, nonnegative, locally integrable hazard on the
real line.  The extension is zero before time zero and one after time one.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The paper hazard on `[0, 1]`, extended by zero before zero and one after one. -/
noncomputable def referenceDeathHazard (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 1).piecewise (P.hazard a) 0 t + if 1 < t then 1 else 0

/-- The reference death hazard agrees with the paper hazard throughout the study window. -/
lemma referenceDeathHazard_eq (P : SubjectLaw) (a : Arm) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    referenceDeathHazard P a t = P.hazard a t := by
  rw [referenceDeathHazard, if_neg]
  · simp [Set.piecewise, ht]
  · exact not_lt_of_ge ht.2

/-- The reference death hazard is measurable on the whole real line. -/
@[fun_prop] lemma measurable_referenceDeathHazard {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) : Measurable (referenceDeathHazard P a) := by
  unfold referenceDeathHazard
  exact ((hP.deathContinuousOn a).measurable_piecewise
      continuous_const.continuousOn measurableSet_Icc).add
    (measurable_const.ite measurableSet_Ioi measurable_const)

/-- The reference death hazard is nonnegative at every time. -/
lemma referenceDeathHazard_nonneg {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) (t : ℝ) :
    0 ≤ referenceDeathHazard P a t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · rw [referenceDeathHazard_eq P a ht]
    exact (hP.deathBounds a t ht).1.trans' c.dMin_pos.le
  · unfold referenceDeathHazard
    simp only [Set.piecewise, if_neg ht]
    split <;> norm_num

/-- The reference death hazard vanishes strictly before time zero. -/
lemma referenceDeathHazard_eq_zero_of_neg (P : SubjectLaw) (a : Arm) {t : ℝ}
    (ht : t < 0) : referenceDeathHazard P a t = 0 := by
  have ht1 : t ≤ 1 := ht.le.trans (by norm_num)
  simp [referenceDeathHazard, Set.piecewise, not_le.mpr ht, ht1]

/-- The reference death hazard is one strictly after the study window. -/
lemma referenceDeathHazard_eq_one_of_one_lt (P : SubjectLaw) (a : Arm) {t : ℝ}
    (ht : 1 < t) : referenceDeathHazard P a t = 1 := by
  simp [referenceDeathHazard, Set.piecewise, ht, not_le.mpr ht]

/-- The reference death hazard is integrable on every compact interval starting at zero. -/
lemma referenceDeathHazard_integrableOn_Icc {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) (u : ℝ) :
    IntegrableOn (referenceDeathHazard P a) (Set.Icc 0 u) := by
  apply IntegrableOn.of_bound (C := max c.dMax 1) measure_Icc_lt_top
  · exact (measurable_referenceDeathHazard hP a).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (referenceDeathHazard_nonneg hP a t)]
    by_cases ht0 : t < 0
    · rw [referenceDeathHazard_eq_zero_of_neg P a ht0]
      positivity
    by_cases ht1 : t ≤ 1
    · rw [referenceDeathHazard_eq P a ⟨le_of_not_gt ht0, ht1⟩]
      exact (hP.deathBounds a t ⟨le_of_not_gt ht0, ht1⟩).2.trans
        (le_max_left _ _)
    · rw [referenceDeathHazard_eq_one_of_one_lt P a (lt_of_not_ge ht1)]
      exact le_max_right _ _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

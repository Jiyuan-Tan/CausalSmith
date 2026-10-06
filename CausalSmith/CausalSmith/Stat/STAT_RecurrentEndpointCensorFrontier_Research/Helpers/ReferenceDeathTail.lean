module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ShiftedExponentialDensity

/-!
# Survival function of the reference death law

This module proves that the exponential splice preserves the paper death
survival throughout the study window and has the intended exponential tail.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A unit exponential is nonnegative almost surely. -/
lemma unitExp_nonnegative : ∀ᵐ e ∂expMeasure 1, 0 ≤ e := by
  rw [ae_iff]
  rw [show {a : ℝ | ¬0 ≤ a} = Set.Iio 0 by ext; simp]
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- The shifted exponential continuation lies at or after time one. -/
lemma shiftedUnitExpLaw_apply_Ici_of_le_one {s : ℝ} (hs : s ≤ 1) :
    shiftedUnitExpLaw (Set.Ici s) = 1 := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  rw [shiftedUnitExpLaw, Measure.map_apply (by fun_prop) measurableSet_Ici]
  apply (mem_ae_iff_prob_eq_one (measurableSet_Ici.preimage (by fun_prop))).mp
  filter_upwards [unitExp_nonnegative] with e he
  change s ≤ 1 + e
  linarith

/-- On the study window, the reference law has exactly the original inclusive tail. -/
lemma referenceDeathLaw_apply_Ici_eq_original (P : SubjectLaw) (a : Arm)
    {s : ℝ} (hs : s ≤ 1) :
    referenceDeathLaw P a (Set.Ici s) = armDeathEventLaw P a (Set.Ici s) := by
  let μ := armDeathEventLaw P a
  rw [referenceDeathLaw, Measure.add_apply,
    Measure.restrict_apply measurableSet_Ici, Measure.smul_apply,
    shiftedUnitExpLaw_apply_Ici_of_le_one hs, smul_eq_mul, mul_one]
  change μ (Set.Ici s ∩ Set.Iic 1) + μ (Set.Ioi 1) = μ (Set.Ici s)
  have hinter : Set.Ici s ∩ Set.Iic 1 = Set.Icc s 1 := by ext x; simp
  rw [hinter, ← measure_union]
  · congr 1
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · rintro (⟨hxs, _⟩ | hx1)
      · exact hxs
      · exact hs.trans hx1.le
    · intro hxs
      exact le_or_gt x 1 |>.elim (fun hx1 => Or.inl ⟨hxs, hx1⟩) Or.inr
  · exact Set.disjoint_left.2 fun _ hx => not_lt_of_ge hx.2
  · exact measurableSet_Ioi

/-- The reference law reproduces the paper survival throughout `[0,1]`. -/
lemma referenceDeathLaw_real_Ici {P : SubjectLaw} (hDeath : DeathHazard P)
    (a : Arm) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (referenceDeathLaw P a).real (Set.Ici s) = survival P a s := by
  rw [measureReal_def, referenceDeathLaw_apply_Ici_eq_original P a hs.2,
    armDeathEventLaw, Measure.map_apply
      (measurable_latentSubject_death a) measurableSet_Ici]
  change P.latent.real {z | s ≤ z.death a} = survival P a s
  exact hDeath.2.2.2.1 a s hs

/-- Beyond time one, the reference survival is the horizon survival times unit exponential decay. -/
lemma referenceDeathLaw_real_Ici_of_one_lt {P : SubjectLaw}
    (hDeath : DeathHazard P) (a : Arm) {s : ℝ} (hs : 1 < s) :
    (referenceDeathLaw P a).real (Set.Ici s) =
      survival P a 1 * Real.exp (-(s - 1)) := by
  rw [measureReal_def, referenceDeathLaw, Measure.add_apply,
    Measure.restrict_apply measurableSet_Ici, Measure.smul_apply]
  have hinter : Set.Ici s ∩ Set.Iic 1 = ∅ :=
    (Set.Ici_disjoint_Iic.mpr (not_le_of_gt hs)).inter_eq
  rw [hinter, measure_empty, zero_add, smul_eq_mul, ENNReal.toReal_mul]
  change (armDeathEventLaw P a).real (Set.Ioi 1) *
    shiftedUnitExpLaw.real (Set.Ici s) = _
  rw [shiftedUnitExpLaw_real_Ici s hs.le,
    armDeathEventLaw_real_Ioi_one hDeath a]

/-- The reference death law is a nonnegative-time probability law. -/
lemma referenceDeathLaw_nonnegativeTimeLaw {P : SubjectLaw}
    (hDeath : DeathHazard P) (a : Arm) :
    Causalean.Stat.RecurrentEvent.CountingProcess.NonnegativeTimeLaw
      (referenceDeathLaw P a) := by
  constructor
  · exact referenceDeathLaw_apply_univ P a
  · rw [referenceDeathLaw_apply_Ici_eq_original P a (by norm_num)]
    exact (armDeathEventLaw_nonnegativeTimeLaw P hDeath a).2

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

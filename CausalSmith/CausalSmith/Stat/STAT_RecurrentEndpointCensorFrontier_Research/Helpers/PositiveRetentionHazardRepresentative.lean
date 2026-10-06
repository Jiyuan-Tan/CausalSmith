module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathEnergyTransport

/-!
# Measurable death hazard for the positive-retention benchmark

Replace the locally integrable hazard by a nonnegative measurable representative
on the study window, with the same reference extension outside it. Compensated
integrals and predictable energies at horizon one are unchanged. These are the
representative and transport steps needed for roadmap (6) and (9); the global
hazard-density equation and the benchmark isometry remain separate obligations.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- A measurable nonnegative representative of the benchmark death hazard,
continued by zero before the study window and one after it. -/
-- @node: positiveRetention_referenceHazard
noncomputable def positiveRetention_referenceHazard (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 then
    max 0 (((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (hDeath.1 a)).aestronglyMeasurable.mk
        (P.hazard a) t)
  else if 1 < t then 1 else 0

/-- The benchmark reference representative is measurable everywhere. -/
-- @node: positiveRetention_referenceHazard_measurable
@[fun_prop] lemma positiveRetention_referenceHazard_measurable (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    Measurable (positiveRetention_referenceHazard P hDeath a) := by
  unfold positiveRetention_referenceHazard
  exact (measurable_const.max
    ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (hDeath.1 a)).aestronglyMeasurable.measurable_mk).ite
    measurableSet_Icc (measurable_const.ite measurableSet_Ioi measurable_const)

/-- The measurable representative is nonnegative at every time. -/
-- @node: positiveRetention_referenceHazard_nonneg
lemma positiveRetention_referenceHazard_nonneg (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) (t : ℝ) :
    0 ≤ positiveRetention_referenceHazard P hDeath a t := by
  unfold positiveRetention_referenceHazard
  split_ifs
  · exact le_max_left _ _
  · norm_num
  · norm_num

/-- Taking a measurable representative preserves the paper hazard almost
 everywhere on the study window. -/
-- @node: positiveRetention_referenceHazard_ae_eq
lemma positiveRetention_referenceHazard_ae_eq (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    positiveRetention_referenceHazard P hDeath a =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      referenceDeathHazard P a := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp (hDeath.1 a)
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hi.aestronglyMeasurable.ae_eq_mk] with t ht heq
  rw [referenceDeathHazard_eq P a ht]
  simp only [positiveRetention_referenceHazard, if_pos ht]
  rw [← heq, max_eq_right (hDeath.2.1 a t ht)]

/-- The representative is integrable on every compact nonnegative horizon;
no continuity of the paper hazard is required. -/
-- @node: positiveRetention_referenceHazard_integrableOn
lemma positiveRetention_referenceHazard_integrableOn (c : ClassConstants)
    (P : SubjectLaw) (hDeath : DeathHazard P) (hDeathBounds : DeathBounds c P)
    (a : Arm) (u : ℝ) :
    IntegrableOn (positiveRetention_referenceHazard P hDeath a) (Icc 0 u) := by
  let hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp (hDeath.1 a)
  let d := hi.aestronglyMeasurable.mk (P.hazard a)
  have hm : Measurable d := hi.aestronglyMeasurable.measurable_mk
  have hbound : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 1 → d t = P.hazard a t := by
    exact (ae_restrict_iff' measurableSet_Icc).mp hi.aestronglyMeasurable.ae_eq_mk.symm
  apply IntegrableOn.of_bound (C := max c.dMax 1) measure_Icc_lt_top
    (positiveRetention_referenceHazard_measurable P hDeath a).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae hbound] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (positiveRetention_referenceHazard_nonneg P hDeath a t)]
  by_cases ht01 : t ∈ Icc (0 : ℝ) 1
  · change (if t ∈ Icc (0 : ℝ) 1 then max 0 (d t) else _) ≤ _
    rw [if_pos ht01, ht ht01, max_eq_right (hDeath.2.1 a t ht01)]
    exact (hDeathBounds a t ht01).2.trans (le_max_left _ _)
  · simp only [positiveRetention_referenceHazard, if_neg ht01]
    split_ifs
    · exact le_max_right _ _
    · exact (by positivity)

/-- Compensated death integrals at horizon one do not depend on the choice
of hazard representative on a Lebesgue null set. -/
-- @node: positiveRetention_referenceHazard_aggregateIntegral_eq
lemma positiveRetention_referenceHazard_aggregateIntegral_eq (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {n : ℕ}
    (H : ℝ → Sample n → ℝ) (x : Sample n) :
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (positiveRetention_referenceHazard P hDeath a) H 1 x =
    Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
      (referenceDeathHazard P a) H 1 x := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
  apply Finset.sum_congr rfl
  intro i _
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.subjectIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [positiveRetention_referenceHazard_ae_eq P hDeath a] with t ht
  rw [ht]

/-- Predictable energy at horizon one is unchanged by the measurable
representative of the death hazard. -/
-- @node: positiveRetention_referenceHazard_predictableEnergy_eq
lemma positiveRetention_referenceHazard_predictableEnergy_eq (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {n : ℕ}
    (H : ℝ → Sample n → ℝ) (x : Sample n) :
    Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (positiveRetention_referenceHazard P hDeath a) H 1 x =
    Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
      (referenceDeathHazard P a) H 1 x := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.predictableEnergy
  apply integral_congr_ae
  filter_upwards [positiveRetention_referenceHazard_ae_eq P hDeath a] with t ht
  rw [ht]

/-- The reference extension is preserved almost everywhere on the whole line. -/
-- @node: positiveRetention_referenceHazard_ae_eq_global
lemma positiveRetention_referenceHazard_ae_eq_global (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    positiveRetention_referenceHazard P hDeath a =ᵐ[volume] referenceDeathHazard P a := by
  have heq := (ae_restrict_iff' measurableSet_Icc).mp
    (positiveRetention_referenceHazard_ae_eq P hDeath a)
  filter_upwards [heq] with t ht
  by_cases hmem : t ∈ Icc (0 : ℝ) 1
  · exact ht hmem
  · simp only [positiveRetention_referenceHazard, if_neg hmem,
      referenceDeathHazard, Set.piecewise, if_neg hmem, Pi.zero_apply, zero_add]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

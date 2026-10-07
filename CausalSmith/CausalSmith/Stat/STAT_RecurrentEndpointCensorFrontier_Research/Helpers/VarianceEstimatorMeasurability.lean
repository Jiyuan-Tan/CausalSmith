module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# Measurability and monotonicity of the subcritical variance estimator

This file supplies the finite-configuration measurability facts used by the
subcritical variance analysis.  It also records that the estimated remaining
mean decreases as its lower time threshold increases.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A two-sided filtered event-multiset sum is the corresponding finite indexed sum. -/
lemma recurrence_times_Icc_sum (s : RecurConfig) (u T : ℝ) (f : ℝ → ℝ) :
    ((s.times.filter (fun t => u ≤ t ∧ t ≤ T)).map f).sum =
      ∑ k : Fin s.1, if u ≤ (s.2 k).1 ∧ (s.2 k).1 ≤ T then f (s.2 k).1 else 0 := by
  classical
  have hlist (l : List ℝ) :
      ((l.filter (fun t => decide (u ≤ t) && decide (t ≤ T))).map f).sum =
        (l.map (fun t => if u ≤ t ∧ t ≤ T then f t else 0)).sum := by
    induction l with
    | nil => simp
    | cons t l ih =>
      by_cases hu : u ≤ t <;> by_cases ht : t ≤ T <;> simp [hu, ht, ih]
  simp only [RecurConfig.times, FiniteSample.count, FiniteSample.points, Multiset.filter_coe,
    Multiset.map_coe, Multiset.sum_coe]
  have hdec : (fun t : ℝ => decide (u ≤ t ∧ t ≤ T)) =
      fun t => decide (u ≤ t) && decide (t ≤ T) := by
    funext t
    simp
  rw [hdec]
  rw [hlist]
  simp [List.map_ofFn, List.sum_ofFn]

/-- The raw recurrence tail sum is jointly measurable in the sample and lower threshold. -/
lemma measurable_remainingRecurrenceSum_joint (a : Arm) {n : ℕ} :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      ∑ i : Fin n, if (p.1 i).treatment = a then
        Multiset.sum (((p.1 i).recur.times.filter (fun t => p.2 ≤ t ∧ t ≤ 1)).map
          (fun t => deathKMLeft a p.1 t * invRisk a p.1 t)) else 0) := by
  classical
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · have hm : Measurable (fun q : (((Fin n → ObsHistory) × ℝ) × RecurConfig) =>
        ∑ k : Fin q.2.1, if q.1.2 ≤ (q.2.2 k).1 ∧ (q.2.2 k).1 ≤ 1 then
          deathKMLeft a q.1.1 (q.2.2 k).1 * invRisk a q.1.1 (q.2.2 k).1 else 0) := by
      apply measurable_recurrence_param_point_sum
        (fun (p : (Fin n → ObsHistory) × ℝ) (x : ℝ × ℝ) =>
          if p.2 ≤ x.1 ∧ x.1 ≤ 1 then
          deathKMLeft a p.1 x.1 * invRisk a p.1 x.1 else 0)
      have hcond : MeasurableSet
          {q : ((Fin n → ObsHistory) × ℝ) × (ℝ × ℝ) |
            q.1.2 ≤ q.2.1 ∧ q.2.1 ≤ 1} :=
        (measurableSet_le
          (show Measurable (fun q : ((Fin n → ObsHistory) × ℝ) × (ℝ × ℝ) =>
            q.1.2) by fun_prop)
          (show Measurable (fun q : ((Fin n → ObsHistory) × ℝ) × (ℝ × ℝ) =>
            q.2.1) by fun_prop)).inter
          (measurableSet_le
            (show Measurable (fun q : ((Fin n → ObsHistory) × ℝ) × (ℝ × ℝ) =>
              q.2.1) by fun_prop) measurable_const)
      apply Measurable.ite hcond
      · have hx : Measurable (fun q : ((Fin n → ObsHistory) × ℝ) × (ℝ × ℝ) =>
            (q.1.1, q.2.1)) := by fun_prop
        exact ((measurable_recurrenceDeathKMLeft_joint a).comp hx).mul
          ((measurable_recurrenceInvRisk_joint a).comp hx)
      · exact measurable_const
    have heq : (fun p : (Fin n → ObsHistory) × ℝ =>
        Multiset.sum (((p.1 i).recur.times.filter (fun t => p.2 ≤ t ∧ t ≤ 1)).map
          (fun t => deathKMLeft a p.1 t * invRisk a p.1 t))) =
        fun p => ∑ k : Fin (p.1 i).recur.1,
          if p.2 ≤ ((p.1 i).recur.2 k).1 ∧ ((p.1 i).recur.2 k).1 ≤ 1 then
            deathKMLeft a p.1 ((p.1 i).recur.2 k).1 *
              invRisk a p.1 ((p.1 i).recur.2 k).1 else 0 := by
      funext p
      exact recurrence_times_Icc_sum _ _ _ _
    rw [heq]
    exact hm.comp (measurable_id.prodMk (by fun_prop))
  · exact measurable_const

/-- The estimated remaining mean is jointly measurable in sample and threshold. -/
@[fun_prop]
lemma measurable_remainingMeanHat_joint (c : ClassConstants) (a : Arm) {n : ℕ} :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      remainingMeanHat c a p.1 p.2) := by
  unfold remainingMeanHat
  exact measurable_const.max
    ((measurable_const.mul (measurable_const.sub measurable_snd)).min
      (measurable_remainingRecurrenceSum_joint a))

/-- The estimated remaining mean decreases as its lower time threshold increases. -/
lemma antitone_remainingMeanHat (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) : Antitone (remainingMeanHat c a s) := by
  classical
  intro u v huv
  unfold remainingMeanHat
  apply max_le_max_left
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_left huv 1)
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  · apply Finset.sum_le_sum
    intro i _
    by_cases hi : (s i).treatment = a
    · simp only [hi, if_true]
      rw [recurrence_times_Icc_sum, recurrence_times_Icc_sum]
      apply Finset.sum_le_sum
      intro k _
      by_cases hv : v ≤ ((s i).recur.2 k).1 ∧ ((s i).recur.2 k).1 ≤ 1
      · have hu : u ≤ ((s i).recur.2 k).1 ∧ ((s i).recur.2 k).1 ≤ 1 :=
          ⟨huv.trans hv.1, hv.2⟩
        simp [hv, hu]
      · simp only [hv, if_false]
        split_ifs
        · exact mul_nonneg (deathKMLeft_mem_Icc a s _).1 (by
            unfold invRisk
            split_ifs <;> positivity)
        · exact le_rfl
    · simp [hi]

/-- The recurrence-jump component of the subcritical variance estimator is measurable. -/
lemma measurable_sigmaHatSq_recurrenceTerm (a : Arm) {n : ℕ} :
    Measurable (fun s : Fin n → ObsHistory =>
      ∑ i : Fin n, if (s i).treatment = a then
        Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
          (fun t => (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2)) else 0) := by
  classical
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · have hm : Measurable (fun p : (Fin n → ObsHistory) × RecurConfig =>
        ∑ k : Fin p.2.1, if (p.2.2 k).1 ≤ 1 then
          (deathKMLeft a p.1 (p.2.2 k).1) ^ 2 *
            (invRisk a p.1 (p.2.2 k).1) ^ 2 else 0) := by
      apply measurable_recurrence_param_point_sum
        (fun s x => if x.1 ≤ 1 then
          (deathKMLeft a s x.1) ^ 2 * (invRisk a s x.1) ^ 2 else 0)
      apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      · have hx : Measurable (fun p : (Fin n → ObsHistory) × (ℝ × ℝ) =>
            (p.1, p.2.1)) := by fun_prop
        exact (((measurable_recurrenceDeathKMLeft_joint a).comp hx).pow_const 2).mul
          (((measurable_recurrenceInvRisk_joint a).comp hx).pow_const 2)
      · exact measurable_const
    have heq : (fun s : Fin n → ObsHistory =>
        Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
          (fun t => (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2))) =
        fun s => ∑ k : Fin (s i).recur.1, if ((s i).recur.2 k).1 ≤ 1 then
          (deathKMLeft a s ((s i).recur.2 k).1) ^ 2 *
            (invRisk a s ((s i).recur.2 k).1) ^ 2 else 0 := by
      funext s
      exact recurrence_times_filtered_sum _ _ _
    rw [heq]
    exact hm.comp (measurable_id.prodMk (by fun_prop))
  · exact measurable_const

/-- The observable subcritical variance estimator is measurable in the sample. -/
@[fun_prop]
lemma measurable_sigmaHatSq (c : ClassConstants) {n : ℕ} :
    Measurable (sigmaHatSq c (n := n)) := by
  classical
  unfold sigmaHatSq
  apply Finset.measurable_sum
  intro a _
  apply (measurable_const.mul (measurable_sigmaHatSq_recurrenceTerm a)).add
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
    ((measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const))
  · have hx : Measurable (fun s : Fin n → ObsHistory => (s, (s i).exit)) := by
      fun_prop
    exact (((measurable_remainingMeanHat_joint c a).comp hx).pow_const 2).mul
      (((measurable_recurrenceInvRisk_joint a).comp hx).pow_const 2)
  · exact measurable_const

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

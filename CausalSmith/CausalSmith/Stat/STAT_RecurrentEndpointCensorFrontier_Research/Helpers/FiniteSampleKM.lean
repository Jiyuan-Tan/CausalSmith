module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators

/-!
# Finite-sample Kaplan--Meier helpers

Bounds, measurability, integrability, and event-sum normalization for the death KM product.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma deathJump_le_riskSet {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (u : ℝ) :
    deathJump a s u ≤ riskSet a s u := by
  have hcard : deathJump a s u =
      (Finset.univ.filter (fun i : Fin n =>
        (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = u)).card := by
    simp [deathJump]
  rw [hcard]
  unfold riskSet
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hi.2.2.ge⟩

lemma deathFactor_mem_Icc {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (u : ℝ) :
    1 - invRisk a s u * deathJump a s u ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hr : riskSet a s u = 0
  · simp [invRisk, hr]
  · have hrp : (0 : ℝ) < riskSet a s u := by exact_mod_cast Nat.pos_of_ne_zero hr
    have hj : (deathJump a s u : ℝ) ≤ riskSet a s u := by
      exact_mod_cast deathJump_le_riskSet a s u
    simp only [invRisk, hr, ↓reduceIte]
    constructor
    · rw [sub_nonneg, ← div_eq_inv_mul]
      exact (div_le_one hrp).2 hj
    · exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hrp.le) (Nat.cast_nonneg _))

lemma deathKMLeft_mem_Icc {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) :
    deathKMLeft a s t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold deathKMLeft
  constructor
  · exact Finset.prod_nonneg fun u _ => (deathFactor_mem_Icc a s u).1
  · exact Finset.prod_le_one (fun _ _ => (deathFactor_mem_Icc a s _).1)
      (fun u _ => (deathFactor_mem_Icc a s u).2)

lemma measurable_deathKMLeft {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    Measurable (deathKMLeft a s) := by
  classical
  unfold deathKMLeft
  generalize exitTimes s = E
  induction E using Finset.induction_on with
  | empty => simp
  | insert u E hu ih =>
      have heq : (fun t => ∏ v ∈ (insert u E).filter (fun v => v < t),
          (1 - invRisk a s v * deathJump a s v)) =
          fun t => if u < t then
            (1 - invRisk a s u * deathJump a s u) *
              ∏ v ∈ E.filter (fun v => v < t),
                (1 - invRisk a s v * deathJump a s v)
          else ∏ v ∈ E.filter (fun v => v < t),
            (1 - invRisk a s v * deathJump a s v) := by
        funext t
        rw [Finset.filter_insert]
        by_cases hut : u < t <;> simp [hut, hu]
      rw [heq]
      exact (ih.const_mul (1 - invRisk a s u * deathJump a s u)).ite
        (measurableSet_lt measurable_const measurable_id) ih

lemma deathKMLeft_mul_intervalIntegrable {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun t => deathKMLeft a s t * f t) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hf ⊢
  apply hf.bdd_mul (measurable_deathKMLeft a s).aestronglyMeasurable.restrict
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (deathKMLeft_mem_Icc a s t).1]
  exact (deathKMLeft_mem_Icc a s t).2

lemma exitTimes_sum_deathJump {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (K : ℝ → ℝ) (T : ℝ) :
    (∑ u ∈ (exitTimes s).filter (fun u => u ≤ T), K u * deathJump a s u) =
      ∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
        (s i).exit ≤ T then K (s i).exit else 0 := by
  classical
  simp only [deathJump, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · simp only [ha, hd, and_self, true_and, mul_ite, mul_one, mul_zero]
      by_cases hT : (s i).exit ≤ T
      · rw [if_pos hT]
        have hmem : (s i).exit ∈
            (exitTimes s).filter (fun u => u ≤ T) := by
          simp [exitTimes, hT]
        rw [Finset.sum_eq_single (s i).exit]
        · simp
        · intro u hu hne
          simp [hne.symm]
        · exact fun hnot => (hnot hmem).elim
      · rw [if_neg hT]
        apply Finset.sum_eq_zero
        intro u hu
        have huT := (Finset.mem_filter.mp hu).2
        by_cases he : (s i).exit = u
        · exact (hT (he ▸ huT)).elim
        · simp [he]
    · simp [hd]
  · simp [ha]


end CausalSmith.Stat.RecurrentEndpointCensorFrontier

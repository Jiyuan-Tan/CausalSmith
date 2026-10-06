module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators

/-!
# Risk sets around extinction

Finite risk sets are positive before the last at-risk time and vanish after it.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: riskSet_pos_iff_assigned_exit
lemma riskSet_pos_iff_assigned_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) :
    0 < riskSet a s t ↔ ∃ i : Fin n, (s i).treatment = a ∧ t ≤ (s i).exit := by
  simp [riskSet, Finset.card_pos, Finset.filter_nonempty_iff]

-- @node: riskSet_le_armSize
lemma riskSet_le_armSize {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) : riskSet a s t ≤ armSize a s := by
  unfold riskSet armSize
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact And.left

-- @node: riskSet_pos_armSize_pos
lemma riskSet_pos_armSize_pos {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ)
    (hRisk : 0 < riskSet a s t) : 0 < armSize a s :=
  lt_of_lt_of_le hRisk (riskSet_le_armSize a s t)

-- @node: riskSet_zero_after_extinction
lemma riskSet_zero_after_extinction {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htExt : extinction a s < t) : riskSet a s t = 0 := by
  by_contra hzero
  have hRisk : 0 < riskSet a s t := Nat.pos_of_ne_zero hzero
  have hArm : armSize a s ≠ 0 :=
    Nat.ne_of_gt (riskSet_pos_armSize_pos a s t hRisk)
  let E : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < riskSet a s u}
  have hmem : t ∈ E := ⟨⟨ht0, ht1⟩, hRisk⟩
  have hBdd : BddAbove E := ⟨1, fun u hu => hu.1.2⟩
  have hle : t ≤ sSup E := le_csSup hBdd hmem
  have hext : extinction a s = sSup E := by
    simp [extinction, hArm, E]
  exact (not_lt_of_ge (hext ▸ hle)) htExt

-- @node: riskSet_pos_before_extinction
lemma riskSet_pos_before_extinction {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ)
    (hInit : 0 < riskSet a s 0)
    (htExt : t < extinction a s) : 0 < riskSet a s t := by
  by_contra hnot
  have hArm : armSize a s ≠ 0 :=
    Nat.ne_of_gt (riskSet_pos_armSize_pos a s 0 hInit)
  let E : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < riskSet a s u}
  have hE : E.Nonempty := ⟨0, ⟨by norm_num, hInit⟩⟩
  have hUpper : ∀ u ∈ E, u ≤ t := by
    intro u hu
    by_contra hle
    have htu : t < u := lt_of_not_ge hle
    obtain ⟨i, hai, hui⟩ := (riskSet_pos_iff_assigned_exit a s u).mp hu.2
    have htRisk : 0 < riskSet a s t :=
      (riskSet_pos_iff_assigned_exit a s t).mpr ⟨i, hai, htu.le.trans hui⟩
    exact hnot htRisk
  have hsup : sSup E ≤ t := csSup_le hE hUpper
  have hext : extinction a s = sSup E := by
    simp [extinction, hArm, E]
  exact (not_lt_of_ge (hext ▸ hsup)) htExt

-- @node: extinction_eq_max_assigned_exit
lemma extinction_eq_max_assigned_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (hArm : 0 < armSize a s)
    (hExit : ∀ i : Fin n, (s i).treatment = a →
      0 ≤ (s i).exit ∧ (s i).exit ≤ 1) :
    ∃ i : Fin n, (s i).treatment = a ∧
      extinction a s = (s i).exit ∧
      ∀ j : Fin n, (s j).treatment = a → (s j).exit ≤ (s i).exit := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (s i).treatment = a)
  have hA : A.Nonempty := by
    rw [← Finset.card_pos]
    exact hArm
  let E : Finset ℝ := A.image (fun i => (s i).exit)
  have hE : E.Nonempty := hA.image _
  obtain ⟨i, hiA, hiMax⟩ : ∃ i ∈ A, (s i).exit = E.max' hE := by
    simpa only [E, Finset.mem_image] using (E.max'_mem hE)
  have hi : (s i).treatment = a := (Finset.mem_filter.mp hiA).2
  have hUpper : ∀ j : Fin n, (s j).treatment = a →
      (s j).exit ≤ (s i).exit := by
    intro j hj
    rw [hiMax]
    exact Finset.le_max' E _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
  let R : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < riskSet a s t}
  have hmem : (s i).exit ∈ R := by
    exact ⟨hExit i hi, (riskSet_pos_iff_assigned_exit a s _).mpr
      ⟨i, hi, le_refl _⟩⟩
  have hbound : BddAbove R := ⟨1, fun t ht => ht.1.2⟩
  have hsup : sSup R = (s i).exit := by
    apply le_antisymm
    · apply csSup_le ⟨(s i).exit, hmem⟩
      intro t ht
      obtain ⟨j, hj, htj⟩ := (riskSet_pos_iff_assigned_exit a s t).mp ht.2
      exact htj.trans (hUpper j hj)
    · exact le_csSup hbound hmem
  refine ⟨i, hi, ?_, hUpper⟩
  simpa [extinction, Nat.ne_of_gt hArm, R] using hsup

-- @node: riskSet_pos_iff_le_extinction
lemma riskSet_pos_iff_le_extinction {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (hArm : 0 < armSize a s)
    (hExit : ∀ i : Fin n, (s i).treatment = a →
      0 ≤ (s i).exit ∧ (s i).exit ≤ 1) (t : ℝ) :
    0 < riskSet a s t ↔ t ≤ extinction a s := by
  obtain ⟨i, hi, hext, hmax⟩ :=
    extinction_eq_max_assigned_exit a s hArm hExit
  rw [hext]
  constructor
  · intro hr
    obtain ⟨j, hj, htj⟩ := (riskSet_pos_iff_assigned_exit a s t).mp hr
    exact htj.trans (hmax j hj)
  · intro ht
    exact (riskSet_pos_iff_assigned_exit a s t).mpr ⟨i, hi, ht⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

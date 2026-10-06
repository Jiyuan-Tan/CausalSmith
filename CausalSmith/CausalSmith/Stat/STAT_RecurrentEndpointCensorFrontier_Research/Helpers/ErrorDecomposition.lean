module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecompositionAnalytic
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FiniteJumpProductRule
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FiniteSampleKM
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationObservables

/-!
# Exact counting-process error identity

The recurrence and death martingale actions are finite event sums minus
ordinary compensator integrals. The extinction remainder is retained.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

noncomputable def recurrenceError (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h : ℝ) : ℝ :=
  muTildeAt c h a s -
    ∫ t in (0 : ℝ)..(1 - h),
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else P.lam a t)

noncomputable def deathError (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h : ℝ) : ℝ :=
  (∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
      (s i).exit ≤ 1 - h then
        remainingTarget c P a h (s i).exit * deathKMLeft a s (s i).exit /
          (survival P a (s i).exit) * invRisk a s (s i).exit else 0) -
    ∫ t in (0 : ℝ)..(1 - h),
      remainingTarget c P a h t * deathKMLeft a s t /
        (survival P a t) * (if riskSet a s t = 0 then 0 else P.hazard a t)

noncomputable def extinctionError (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h : ℝ) : ℝ :=
  if extinction a s < 1 - h then
    deathKM a s (extinction a s) / survival P a (extinction a s) *
      remainingTarget c P a h (extinction a s)
  else 0

lemma riskSet_mul_invRisk {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (t : ℝ) :
    (riskSet a s t : ℝ) * invRisk a s t =
      if riskSet a s t = 0 then 0 else 1 := by
  by_cases h : riskSet a s t = 0
  · simp [invRisk, h]
  · have hcast : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
    simp [invRisk, h, hcast]

-- @node: recurrenceCompensator_integrand
lemma recurrenceCompensator_integrand (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h t : ℝ) :
    continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        invRisk a s t * ((riskSet a s t : ℝ) * P.lam a t) =
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else P.lam a t) := by
  rw [show continuationWeight (holderOrder c) h t * deathKMLeft a s t *
      invRisk a s t * ((riskSet a s t : ℝ) * P.lam a t) =
      (continuationWeight (holderOrder c) h t * deathKMLeft a s t) *
        ((riskSet a s t : ℝ) * invRisk a s t) * P.lam a t by ring]
  rw [riskSet_mul_invRisk]
  split_ifs <;> ring

-- @node: deathCompensator_integrand
lemma deathCompensator_integrand (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h t : ℝ) :
    remainingTarget c P a h t * deathKMLeft a s t /
        survival P a t * invRisk a s t *
        ((riskSet a s t : ℝ) * P.hazard a t) =
      remainingTarget c P a h t * deathKMLeft a s t /
        survival P a t *
        (if riskSet a s t = 0 then 0 else P.hazard a t) := by
  rw [show remainingTarget c P a h t * deathKMLeft a s t /
      survival P a t * invRisk a s t *
      ((riskSet a s t : ℝ) * P.hazard a t) =
      (remainingTarget c P a h t * deathKMLeft a s t /
        survival P a t) *
        ((riskSet a s t : ℝ) * invRisk a s t) * P.hazard a t by ring]
  rw [riskSet_mul_invRisk]
  split_ifs <;> ring

-- @node: armSize_zero_treatment
lemma armSize_zero_treatment {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (hEmpty : armSize a s = 0) (i : Fin n) : (s i).treatment ≠ a := by
  intro hi
  have : i ∈ Finset.univ.filter (fun j => (s j).treatment = a) := by
    simp [hi]
  have hSet : (Finset.univ.filter (fun j => (s j).treatment = a)).card = 0 := hEmpty
  simp only [Finset.card_eq_zero] at hSet
  simp [hSet] at this

-- @node: armSize_zero_riskSet
lemma armSize_zero_riskSet {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (hEmpty : armSize a s = 0) (t : ℝ) : riskSet a s t = 0 := by
  simp [riskSet, armSize_zero_treatment a s hEmpty]

-- @node: armSize_zero_muTildeAt
lemma armSize_zero_muTildeAt (c : ClassConstants) {n : ℕ}
    (a : Arm) (s : Fin n → ObsHistory) (h : ℝ)
    (hEmpty : armSize a s = 0) : muTildeAt c h a s = 0 := by
  simp [muTildeAt, armSize_zero_treatment a s hEmpty]

-- @node: armSize_zero_deathJump
lemma armSize_zero_deathJump {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (hEmpty : armSize a s = 0) (t : ℝ) : deathJump a s t = 0 := by
  simp [deathJump, armSize_zero_treatment a s hEmpty]

-- @node: armSize_zero_deathKM
lemma armSize_zero_deathKM {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (hEmpty : armSize a s = 0) (t : ℝ) : deathKM a s t = 1 := by
  simp [deathKM, armSize_zero_deathJump a s hEmpty]

-- @node: armSize_zero_deathKMLeft
lemma armSize_zero_deathKMLeft {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (hEmpty : armSize a s = 0) (t : ℝ) : deathKMLeft a s t = 1 := by
  simp [deathKMLeft, armSize_zero_deathJump a s hEmpty]

-- @node: riskSet_add_priorExits_eq_armSize
lemma riskSet_add_priorExits_eq_armSize {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) :
    riskSet a s t +
      (Finset.univ.filter (fun i : Fin n =>
        (s i).treatment = a ∧ (s i).exit < t)).card = armSize a s := by
  classical
  let assigned : Finset (Fin n) := Finset.univ.filter (fun i => (s i).treatment = a)
  have h := Finset.card_filter_add_card_filter_not
    (fun i : Fin n => t ≤ (s i).exit) (s := assigned)
  convert h using 1 <;> simp [riskSet, armSize, assigned, Finset.filter_filter, not_le]

-- @node: deathJump_add_censorJump_eq_exitCount
lemma deathJump_add_censorJump_eq_exitCount {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u : ℝ) (hu : u < 1) :
    deathJump a s u + censorJump a s u =
      ∑ i : Fin n, if (s i).treatment = a ∧ (s i).exit = u then 1 else 0 := by
  classical
  simp only [deathJump, censorJump, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (s i).treatment = a
  · by_cases he : (s i).exit = u
    · by_cases hd : (s i).deathInd <;> simp [ha, he, hd, hu]
    · simp [he]
  · simp [ha]

-- @node: exitCount_le_riskSet
lemma exitCount_le_riskSet {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u : ℝ) (hu : u < 1) :
    deathJump a s u + censorJump a s u ≤ riskSet a s u := by
  rw [deathJump_add_censorJump_eq_exitCount a s u hu]
  have hcard :
      (∑ i : Fin n, if (s i).treatment = a ∧ (s i).exit = u then 1 else 0) =
      (Finset.univ.filter (fun i : Fin n =>
        (s i).treatment = a ∧ (s i).exit = u)).card := by
    simp
  rw [hcard]
  unfold riskSet
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hi.2.ge⟩

-- @node: riskSet_at_next_exit
lemma riskSet_at_next_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u t : ℝ) (hu : u < 1) (hut : u < t)
    (hNext : ∀ i : Fin n, (s i).treatment = a →
      u < (s i).exit → t ≤ (s i).exit) :
    riskSet a s u = riskSet a s t + deathJump a s u + censorJump a s u := by
  rw [add_assoc, deathJump_add_censorJump_eq_exitCount a s u hu]
  let atRisk : Finset (Fin n) := Finset.univ.filter
    (fun i => (s i).treatment = a ∧ u ≤ (s i).exit)
  have hsplit := Finset.card_filter_add_card_filter_not
    (fun i : Fin n => t ≤ (s i).exit) (s := atRisk)
  have hBefore : atRisk.filter (fun i => t ≤ (s i).exit) =
      Finset.univ.filter (fun i => (s i).treatment = a ∧ t ≤ (s i).exit) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, atRisk]
    constructor
    · rintro ⟨⟨ha, _⟩, ht⟩
      exact ⟨ha, ht⟩
    · rintro ⟨ha, ht⟩
      exact ⟨⟨ha, le_trans hut.le ht⟩, ht⟩
  have hAt : atRisk.filter (fun i => ¬ t ≤ (s i).exit) =
      Finset.univ.filter (fun i => (s i).treatment = a ∧ (s i).exit = u) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, atRisk, not_le]
    constructor
    · rintro ⟨⟨ha, hu'⟩, ht⟩
      have he : (s i).exit = u := by
        rcases hu'.eq_or_lt with he | hlt
        · exact he.symm
        · exact False.elim ((not_lt.mpr (hNext i ha hlt)) ht)
      exact ⟨ha, he⟩
    · rintro ⟨ha, he⟩
      exact ⟨⟨ha, he.ge⟩, he ▸ hut⟩
  rw [hBefore, hAt] at hsplit
  simp only [riskSet, atRisk] at hsplit ⊢
  have hcard :
      (∑ i : Fin n, if (s i).treatment = a ∧ (s i).exit = u then 1 else 0) =
      (Finset.univ.filter (fun i : Fin n =>
        (s i).treatment = a ∧ (s i).exit = u)).card := by
    simp
  rw [hcard]
  exact hsplit.symm

-- @node: exitFactor_eq_nextRisk_ratio
lemma exitFactor_eq_nextRisk_ratio {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u t : ℝ) (hu : u < 1) (hut : u < t)
    (hNext : ∀ i : Fin n, (s i).treatment = a →
      u < (s i).exit → t ≤ (s i).exit)
    (hRisk : 0 < riskSet a s u) :
    1 - invRisk a s u * (deathJump a s u + censorJump a s u) =
      (riskSet a s t : ℝ) / riskSet a s u := by
  have hcount := riskSet_at_next_exit a s u t hu hut hNext
  have hcountR : (riskSet a s u : ℝ) =
      riskSet a s t + (deathJump a s u + censorJump a s u) := by
    rw [add_assoc] at hcount
    exact_mod_cast hcount
  have hne : (riskSet a s u : ℝ) ≠ 0 := by exact_mod_cast hRisk.ne'
  simp only [invRisk, Nat.ne_of_gt hRisk, ↓reduceIte]
  field_simp
  linear_combination hcountR

-- @node: exitFactor_nonneg
lemma exitFactor_nonneg {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u : ℝ) (hu : u < 1) :
    0 ≤ 1 - invRisk a s u *
      (deathJump a s u + censorJump a s u) := by
  by_cases hr : riskSet a s u = 0
  · simp [invRisk, hr]
  · have hpos : (0 : ℝ) < riskSet a s u := by exact_mod_cast Nat.pos_of_ne_zero hr
    have hle : (deathJump a s u + censorJump a s u : ℝ) ≤ riskSet a s u := by
      exact_mod_cast exitCount_le_riskSet a s u hu
    simp only [invRisk, hr, ↓reduceIte]
    have := (div_le_one hpos).2 hle
    simpa [div_eq_mul_inv, mul_comm] using sub_nonneg.mpr this

-- @node: deathCensorFactors_eq_exitFactor
lemma deathCensorFactors_eq_exitFactor {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u : ℝ)
    (hNoMixedExit : deathJump a s u = 0 ∨ censorJump a s u = 0) :
    (1 - invRisk a s u * deathJump a s u) *
      (1 - invRisk a s u * censorJump a s u) =
      1 - invRisk a s u * (deathJump a s u + censorJump a s u) := by
  rcases hNoMixedExit with h | h
  · simp [h]
  · simp [h]

-- @node: deathKMLeft_mul_reverseKMLeft_eq_exitProduct
lemma deathKMLeft_mul_reverseKMLeft_eq_exitProduct {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ)
    (hNoMixedExit : ∀ u ∈ (exitTimes s).filter (fun u => u < t),
      deathJump a s u = 0 ∨ censorJump a s u = 0) :
    deathKMLeft a s t * reverseKMLeft a s t =
      ∏ u ∈ (exitTimes s).filter (fun u => u < t),
        (1 - invRisk a s u * (deathJump a s u + censorJump a s u)) := by
  simp only [deathKMLeft, reverseKMLeft, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  exact deathCensorFactors_eq_exitFactor a s u (hNoMixedExit u hu)

-- @node: noMixedExit_of_noDeathCensorTie
lemma noMixedExit_of_noDeathCensorTie {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hNoTie : ∀ i j : Fin n, (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → ¬(s j).deathInd → (s i).exit ≠ (s j).exit)
    (u : ℝ) : deathJump a s u = 0 ∨ censorJump a s u = 0 := by
  by_contra h
  push Not at h
  have hd : 0 < deathJump a s u := Nat.pos_of_ne_zero h.1
  have hc : 0 < censorJump a s u := Nat.pos_of_ne_zero h.2
  simp only [deathJump, Finset.sum_pos_iff, Finset.mem_univ, true_and] at hd
  simp only [censorJump, Finset.sum_pos_iff, Finset.mem_univ, true_and] at hc
  obtain ⟨i, hi⟩ := hd
  obtain ⟨j, hj⟩ := hc
  have hdi : (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = u := by
    by_contra hn
    simp [hn] at hi
  have hcj : (s j).treatment = a ∧ ¬(s j).deathInd ∧
      (s j).exit = u ∧ u < 1 := by
    split_ifs at hj with hcj
    · exact hcj
    · simp at hj
  exact (hNoTie i j hdi.1 hdi.2.1 hcj.1 hcj.2.1)
    (hdi.2.2.trans hcj.2.2.1.symm)

-- @node: riskSet_eq_armSize_of_noPriorExit
lemma riskSet_eq_armSize_of_noPriorExit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ)
    (hNone : ((exitTimes s).filter (fun u => u < t)).card = 0) :
    riskSet a s t = armSize a s := by
  have hprior : (Finset.univ.filter (fun i : Fin n =>
      (s i).treatment = a ∧ (s i).exit < t)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have he : (s i).exit ∈ (exitTimes s).filter (fun u => u < t) := by
        simp [exitTimes, hi.2]
      have hempty := Finset.card_eq_zero.mp hNone
      simp [hempty] at he
    · intro hi
      simp at hi
  have hcount := riskSet_add_priorExits_eq_armSize a s t
  simpa [hprior] using hcount

-- @node: riskSet_eq_exitProduct
lemma riskSet_eq_exitProduct {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (ht : t ≤ 1)
    (hRisk : 0 < riskSet a s t) :
    (riskSet a s t : ℝ) / armSize a s =
      ∏ u ∈ (exitTimes s).filter (fun u => u < t),
        (1 - invRisk a s u * (deathJump a s u + censorJump a s u)) := by
  classical
  let E (v : ℝ) := (exitTimes s).filter (fun u => u < v)
  have hmain : ∀ k : ℕ, ∀ v : ℝ, (E v).card = k → v ≤ 1 →
      0 < riskSet a s v →
      (riskSet a s v : ℝ) / armSize a s =
        ∏ u ∈ E v, (1 - invRisk a s u *
          (deathJump a s u + censorJump a s u)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hk hv hr
      by_cases hE : (E v).Nonempty
      · let u := (E v).max' hE
        have huE : u ∈ E v := (E v).max'_mem hE
        have huv : u < v := (Finset.mem_filter.mp huE).2
        have hu1 : u < 1 := lt_of_lt_of_le huv hv
        have hnext : ∀ i : Fin n, (s i).treatment = a →
            u < (s i).exit → v ≤ (s i).exit := by
          intro i _ hui
          by_contra hnot
          have hiE : (s i).exit ∈ E v := by
            simp [E, exitTimes, lt_of_not_ge hnot]
          exact (not_lt_of_ge (Finset.le_max' (E v) _ hiE)) hui
        have hEr : E u = (E v).erase u := by
          ext x
          constructor
          · intro hx
            have hxu : x < u := (Finset.mem_filter.mp hx).2
            apply Finset.mem_erase.mpr
            exact ⟨ne_of_lt hxu, Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hx).1, lt_trans hxu huv⟩⟩
          · intro hx
            have hxE := (Finset.mem_erase.mp hx).2
            have hxu : x ≤ u := Finset.le_max' (E v) x hxE
            have hne : x ≠ u := (Finset.mem_erase.mp hx).1
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxE).1,
              lt_of_le_of_ne hxu hne⟩
        have hcard : (E u).card < k := by
          rw [hEr, ← hk]
          exact Finset.card_erase_lt_of_mem huE
        have hru : 0 < riskSet a s u := by
          obtain ⟨i, hai, hvi⟩ := (riskSet_pos_iff_assigned_exit a s v).mp hr
          exact (riskSet_pos_iff_assigned_exit a s u).mpr
            ⟨i, hai, le_trans huv.le hvi⟩
        have hprod := ih (E u).card hcard u rfl hu1.le hru
        have hfactor := exitFactor_eq_nextRisk_ratio a s u v hu1 huv hnext hru
        have harm : (armSize a s : ℝ) ≠ 0 := by
          exact_mod_cast (riskSet_pos_armSize_pos a s v hr).ne'
        have hru' : (riskSet a s u : ℝ) ≠ 0 := by exact_mod_cast hru.ne'
        rw [hEr, ← Finset.prod_erase_mul (E v)
          (fun x => 1 - invRisk a s x *
            (deathJump a s x + censorJump a s x)) huE] at *
        rw [← hEr] at hprod
        rw [← hEr, ← hprod, hfactor]
        field_simp
      · have hzero : (E v).card = 0 := Finset.card_eq_zero.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hE)
        have heq := riskSet_eq_armSize_of_noPriorExit a s v hzero
        simp [E, Finset.card_eq_zero.mp hzero, heq,
          (riskSet_pos_armSize_pos a s v hr).ne']
  exact hmain (E t).card t rfl ht hRisk

-- @node: reverseKM_product_of_noMixed
lemma reverseKM_product_of_noMixed {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (ht : t ≤ 1)
    (hRisk : 0 < riskSet a s t)
    (hNoMixedExit : ∀ u ∈ (exitTimes s).filter (fun u => u < t),
      deathJump a s u = 0 ∨ censorJump a s u = 0) :
    (riskSet a s t : ℝ) / armSize a s =
      deathKMLeft a s t * reverseKMLeft a s t := by
  rw [riskSet_eq_exitProduct a s t ht hRisk]
  exact (deathKMLeft_mul_reverseKMLeft_eq_exitProduct a s t hNoMixedExit).symm

-- @node: reverseKM_product_of_noDeathCensorTie
lemma reverseKM_product_of_noDeathCensorTie {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (ht : t ≤ 1)
    (hRisk : 0 < riskSet a s t)
    (hNoTie : ∀ i j : Fin n, (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → ¬(s j).deathInd → (s i).exit ≠ (s j).exit) :
    (riskSet a s t : ℝ) / armSize a s =
      deathKMLeft a s t * reverseKMLeft a s t := by
  exact reverseKM_product_of_noMixed a s t ht hRisk
    (fun u _ => noMixedExit_of_noDeathCensorTie a s hNoTie u)

-- @node: exact_error_decomposition_empty_arm
lemma exact_error_decomposition_empty_arm (c : ClassConstants) (P : SubjectLaw)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (h : ℝ)
    (hEmpty : armSize a s = 0) (hOne : h < 1) :
    muTildeAt c h a s - truncatedMean c P a h =
      recurrenceError c P a s h - deathError c P a s h -
        extinctionError c P a s h := by
  have hRec : recurrenceError c P a s h = 0 := by
    simp [recurrenceError, armSize_zero_muTildeAt c a s h hEmpty,
      armSize_zero_riskSet a s hEmpty]
  have hDeath : deathError c P a s h = 0 := by
    simp [deathError, armSize_zero_treatment a s hEmpty,
      armSize_zero_riskSet a s hEmpty]
  have hExt : extinctionError c P a s h = truncatedMean c P a h := by
    have hPos : 0 < 1 - h := by linarith
    simp [extinctionError, extinction, hEmpty, hPos,
      armSize_zero_deathKM a s hEmpty, remainingTarget_at_zero, survival]
  rw [hRec, hDeath, hExt, armSize_zero_muTildeAt c a s h hEmpty]
  ring

-- @node: observed_death_exit_fixed_null
lemma observed_death_exit_fixed_null (P : SubjectLaw) (hDeath : DeathHazard P)
    (a : Arm) (t : ℝ) :
    observedLaw P {o | o.treatment = a ∧ o.deathInd ∧ o.exit = t} = 0 := by
  have hMeas : MeasurableSet {o : ObsHistory | o.treatment = a ∧ o.deathInd ∧
      o.exit = t} :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      ((measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const).inter
        (measurableSet_eq_fun measurable_obsHistory_exit measurable_const))
  rw [observedLaw, Measure.map_apply measurable_observe hMeas]
  have hsub : observe ⁻¹' {o | o.treatment = a ∧ o.deathInd ∧ o.exit = t} ⊆
      (fun z : LatentSubject => z.death a) ⁻¹' {t} := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
    rcases hz with ⟨ha, hd, he⟩
    simp only [observe] at ha hd he
    have hle : z.death z.treatment ≤ censorHorizon z z.treatment := of_decide_eq_true hd
    simpa [← ha, min_eq_left hle] using he
  have hnull : P.latent ((fun z : LatentSubject => z.death a) ⁻¹' {t}) = 0 := by
    have hmap := (hDeath.2.2.1 a) (measure_singleton t)
    rwa [Measure.map_apply (measurable_latentSubject_death a)
      (MeasurableSet.singleton t)] at hmap
  exact measure_mono_null hsub hnull

-- @node: observed_pair_death_exit_no_tie
lemma observed_pair_death_exit_no_tie (P : SubjectLaw) (hDeath : DeathHazard P)
    (a : Arm) :
    (observedLaw P).prod (observedLaw P)
      {o : ObsHistory × ObsHistory |
        o.2.treatment = a ∧ o.2.deathInd ∧ o.2.exit = o.1.exit} = 0 := by
  have hMeas : MeasurableSet
      {o : ObsHistory × ObsHistory |
        o.2.treatment = a ∧ o.2.deathInd ∧ o.2.exit = o.1.exit} := by
    exact (measurableSet_eq_fun
      (measurable_obsHistory_treatment.comp measurable_snd) measurable_const).inter
      ((measurableSet_eq_fun
        (measurable_obsHistory_deathInd.comp measurable_snd) measurable_const).inter
        (measurableSet_eq_fun
          (measurable_obsHistory_exit.comp measurable_snd)
          (measurable_obsHistory_exit.comp measurable_fst)))
  apply Measure.measure_prod_null_of_ae_null hMeas
  apply Filter.Eventually.of_forall
  intro o
  exact observed_death_exit_fixed_null P hDeath a o.exit

-- @node: sample_death_exit_no_tie
lemma sample_death_exit_no_tie (P : SubjectLaw) (hDeath : DeathHazard P)
    (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ (i j : Fin n), i ≠ j →
      ∀ (a : Arm), (s i).treatment = a → (s i).deathInd →
        (s i).exit ≠ (s j).exit := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by
    dsimp [sampleLaw]
    infer_instance
  have hInd : ProbabilityTheory.iIndepFun (fun i (s : Fin n → ObsHistory) => s i)
      (sampleLaw P n) := by
    change ProbabilityTheory.iIndepFun (fun i (s : Fin n → ObsHistory) => s i)
      (Measure.pi fun _ : Fin n => observedLaw P)
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hEval (i : Fin n) :
      (sampleLaw P n).map (fun s => s i) = observedLaw P := by
    simpa [sampleLaw] using
      (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).map_eq
  have hPair (i j : Fin n) (hij : i ≠ j) :
      (sampleLaw P n).map (fun s => (s j, s i)) =
        (observedLaw P).prod (observedLaw P) := by
    have hIndij := hInd.indepFun hij.symm
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply j).aemeasurable
      (measurable_pi_apply i).aemeasurable).mp hIndij
    simpa [hEval] using hmap
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun s h => (h hij).elim)
  have hArm (a : Arm) : ∀ᵐ s ∂sampleLaw P n,
      (s i).treatment = a → (s i).deathInd →
        (s i).exit ≠ (s j).exit := by
    have hnull : (sampleLaw P n)
      {s | (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = (s j).exit} = 0 := by
      have h := observed_pair_death_exit_no_tie P hDeath a
      rw [← hPair i j hij,
        Measure.map_apply ((measurable_pi_apply j).prodMk (measurable_pi_apply i))
          (by
            exact (measurableSet_eq_fun
              (measurable_obsHistory_treatment.comp measurable_snd) measurable_const).inter
              ((measurableSet_eq_fun
                (measurable_obsHistory_deathInd.comp measurable_snd) measurable_const).inter
                (measurableSet_eq_fun
                  (measurable_obsHistory_exit.comp measurable_snd)
                  (measurable_obsHistory_exit.comp measurable_fst))))] at h
      exact h
    exact ae_iff.mpr (by simpa only [Classical.not_imp, not_not] using hnull)
  filter_upwards [hArm false, hArm true] with s h0 h1 _ a ha hd
  cases a
  · exact h0 ha hd
  · exact h1 ha hd

-- @node: sample_exit_le_one
lemma sample_exit_le_one (P : SubjectLaw) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ i : Fin n, (s i).exit ≤ 1 := by
  have hObs : ∀ᵐ o ∂observedLaw P, o.exit ≤ 1 := by
    rw [observedLaw]
    apply (ae_map_iff measurable_observe.aemeasurable
      (measurableSet_le measurable_obsHistory_exit measurable_const)).mpr
    apply Filter.Eventually.of_forall
    intro z
    have hc : censorHorizon z z.treatment ≤ 1 := by
      unfold censorHorizon
      split_ifs <;> simp
    simpa only [observe] using (le_trans (min_le_right (z.death z.treatment)
      (censorHorizon z z.treatment)) hc)
  rw [Filter.eventually_all]
  intro i
  have hmap : (sampleLaw P n).map (fun s => s i) = observedLaw P := by
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    letI : IsProbabilityMeasure (observedLaw P) :=
      Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
    simpa [sampleLaw] using
      (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).map_eq
  rw [← hmap] at hObs
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_le measurable_obsHistory_exit measurable_const)).mp hObs

-- @node: sample_exit_nonneg
lemma sample_exit_nonneg (P : SubjectLaw) (hDeath : DeathHazard P) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ i : Fin n, 0 ≤ (s i).exit := by
  have hDeathNonneg (a : Arm) :
      ∀ᵐ z ∂P.latent, 0 ≤ z.death a := by
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    have htail : P.latent.real {z | (0 : ℝ) ≤ z.death a} = 1 := by
      simpa [survival] using hDeath.2.2.2.1 a 0 (by norm_num)
    have hmeas : MeasurableSet {z : LatentSubject | (0 : ℝ) ≤ z.death a} :=
      measurableSet_le measurable_const (measurable_latentSubject_death a)
    have hcomp := measureReal_compl (μ := P.latent) hmeas
    have huniv : P.latent.real Set.univ = 1 := by
      simp [Measure.real, P.prob]
    rw [htail, huniv] at hcomp
    have hzero : P.latent {z | ¬(0 : ℝ) ≤ z.death a} = 0 := by
      rw [← compl_setOf]
      exact (measureReal_eq_zero_iff).mp (by linarith [hcomp])
    exact ae_iff.mpr (by simpa only [not_not] using hzero)
  have hObs : ∀ᵐ o ∂observedLaw P, 0 ≤ o.exit := by
    rw [observedLaw]
    apply (ae_map_iff measurable_observe.aemeasurable
      (measurableSet_le measurable_const measurable_obsHistory_exit)).mpr
    filter_upwards [hDeathNonneg false, hDeathNonneg true] with z h0 h1
    have hd : 0 ≤ z.death z.treatment := by cases z.treatment <;> assumption
    have hc : 0 ≤ censorHorizon z z.treatment := by
      unfold censorHorizon
      split_ifs <;> positivity
    simpa only [observe] using (le_min hd hc)
  rw [Filter.eventually_all]
  intro i
  have hmap : (sampleLaw P n).map (fun s => s i) = observedLaw P := by
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    letI : IsProbabilityMeasure (observedLaw P) :=
      Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
    simpa [sampleLaw] using
      (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).map_eq
  rw [← hmap] at hObs
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_le measurable_const measurable_obsHistory_exit)).mp hObs

-- @node: lem:exact-error-decomposition
lemma exact_error_decomposition (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hBounds : DeathBounds c P)
    (hAssignment : AssignmentLaw P) :
    (∀ (n : ℕ), 3 ≤ n → ∀ᵐ s ∂sampleLaw P n, ∀ (a : Arm) (h : ℝ),
      0 ≤ h → h ≤ c.x0 / 2 →
      muTildeAt c h a s - truncatedMean c P a h =
        recurrenceError c P a s h - deathError c P a s h -
          extinctionError c P a s h) ∧
    (∀ n : ℕ, 3 ≤ n → ∀ᵐ s ∂sampleLaw P n,
      ∀ (a : Arm) (t : ℝ), 0 < riskSet a s t →
        (riskSet a s t : ℝ) / armSize a s =
          deathKMLeft a s t * reverseKMLeft a s t) := by
  constructor
  · intro n hn
    filter_upwards [sample_exit_nonneg P hDeath n,
      sample_exit_le_one P n] with s hExit0 hExit1
    intro a h hh hcap
    by_cases hEmpty : armSize a s = 0
    · apply exact_error_decomposition_empty_arm c P a s h hEmpty
      have hx := c.x0_le
      linarith
    · have hArm : 0 < armSize a s := Nat.pos_of_ne_zero hEmpty
      have hOne : h < 1 := by
        have hx := c.x0_le
        linarith
      let U : ℝ := 1 - h
      have hU0 : 0 ≤ U := by dsimp [U]; linarith
      have hExit (i : Fin n) (hi : (s i).treatment = a) :
          0 ≤ (s i).exit ∧ (s i).exit ≤ 1 := ⟨hExit0 i, hExit1 i⟩
      obtain ⟨imax, himax, hext, hmax⟩ :=
        extinction_eq_max_assigned_exit a s hArm hExit
      have hext0 : 0 ≤ extinction a s := hext.symm ▸ hExit0 imax
      let T : ℝ := min (extinction a s) U
      have hT0 : 0 ≤ T := le_min hext0 hU0
      have hTU : T ≤ U := min_le_right _ _
      let F : ℝ → ℝ := fun t => remainingTarget c P a h t / survival P a t
      let f : ℝ → ℝ := fun t =>
        -(continuationWeight (holderOrder c) h t * P.lam a t) +
          remainingTarget c P a h t / survival P a t * P.hazard a t
      have hparts := remainingTarget_ratio_field_intervalIntegrable
        c P hPoisson hDeath hBounds a hh hT0 (by simpa [U] using hTU)
      have hf : IntervalIntegrable f volume 0 T := by
        exact hparts.1.neg.add hparts.2
      have hstep : IntervalIntegrable
          (fun t => deathKMLeft a s t * f t) volume 0 T :=
        deathKMLeft_mul_intervalIntegrable a s f hT0 hf
      have hFTC : ∀ x y, (0 : ℝ) ≤ x → x ≤ y → y ≤ T →
          (∫ t in x..y, f t) = F y - F x := by
        intro x y hx hxy hy
        exact remainingTarget_ratio_integral_eq_sub c P hPoisson hDeath
          hBounds a hh (by simp [U]) hU0 hx hxy (hy.trans hTU)
      have hprod := deathKM_finiteJumpProductRule_of_integral_eq_sub
        a s F f hT0 hExit0 hFTC hstep
      have hsum :
          (∑ u ∈ (exitTimes s).filter (fun u => u ≤ T),
            deathKMLeft a s u *
              ((1 - invRisk a s u * deathJump a s u) - 1) * F u) =
          -(∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
              (s i).exit ≤ T then
                remainingTarget c P a h (s i).exit *
                  deathKMLeft a s (s i).exit / survival P a (s i).exit *
                    invRisk a s (s i).exit else 0) := by
        calc
          _ = -(∑ u ∈ (exitTimes s).filter (fun u => u ≤ T),
              (remainingTarget c P a h u * deathKMLeft a s u /
                survival P a u * invRisk a s u) * deathJump a s u) := by
            simp only [F]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro u hu
            ring
          _ = _ := by
            rw [exitTimes_sum_deathJump a s
              (fun u => remainingTarget c P a h u * deathKMLeft a s u /
                survival P a u * invRisk a s u) T]
      have hint :
          (∫ t in (0 : ℝ)..T, deathKMLeft a s t * f t) =
            -(∫ t in (0 : ℝ)..T,
              continuationWeight (holderOrder c) h t * deathKMLeft a s t *
                P.lam a t) +
            ∫ t in (0 : ℝ)..T,
              remainingTarget c P a h t * deathKMLeft a s t /
                survival P a t * P.hazard a t := by
        rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_add]
        · apply intervalIntegral.integral_congr
          intro t ht
          simp only [f]
          ring
        · apply (deathKMLeft_mul_intervalIntegrable a s
              (fun t => continuationWeight (holderOrder c) h t * P.lam a t)
              hT0 hparts.1).neg.congr
          intro t ht
          change -(deathKMLeft a s t *
            (continuationWeight (holderOrder c) h t * P.lam a t)) = _
          ring
        · apply (deathKMLeft_mul_intervalIntegrable a s
              (fun t => remainingTarget c P a h t / survival P a t *
                P.hazard a t) hT0 hparts.2).congr
          intro t ht
          ring
      rw [hsum, hint] at hprod
      have hU1 : U ≤ 1 := by dsimp [U]; linarith
      have hRiskClosed (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) T) :
          riskSet a s t ≠ 0 := by
        rw [Set.uIcc_of_le hT0] at ht
        apply Nat.ne_of_gt
        apply (riskSet_pos_iff_le_extinction a s hArm hExit t).2
        exact ht.2.trans (min_le_left _ _)
      have hRiskLeft (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) T) :
          riskSet a s t ≠ 0 :=
        hRiskClosed t (Set.uIoc_subset_uIcc ht)
      have hRiskRight (t : ℝ) (ht : t ∈ Set.uIoc T U) :
          riskSet a s t = 0 := by
        rw [Set.uIoc_of_le hTU] at ht
        apply riskSet_zero_after_extinction a s t
        · exact hT0.trans ht.1.le
        · exact ht.2.trans hU1
        · by_contra hnot
          have hte : t ≤ extinction a s := le_of_not_gt hnot
          exact (not_lt_of_ge (le_min hte ht.2)) ht.1
      let r : ℝ → ℝ := fun t =>
        continuationWeight (holderOrder c) h t * deathKMLeft a s t *
          (if riskSet a s t = 0 then 0 else P.lam a t)
      let d : ℝ → ℝ := fun t =>
        remainingTarget c P a h t * deathKMLeft a s t / survival P a t *
          (if riskSet a s t = 0 then 0 else P.hazard a t)
      have hrLeft : IntervalIntegrable r volume 0 T := by
        apply (deathKMLeft_mul_intervalIntegrable a s
          (fun t => continuationWeight (holderOrder c) h t * P.lam a t)
          hT0 hparts.1).congr
        intro t ht
        simp only [r, hRiskLeft t ht, if_false]
        ring
      have hdLeft : IntervalIntegrable d volume 0 T := by
        apply (deathKMLeft_mul_intervalIntegrable a s
          (fun t => remainingTarget c P a h t / survival P a t * P.hazard a t)
          hT0 hparts.2).congr
        intro t ht
        simp only [d, hRiskLeft t ht, if_false]
        ring
      have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume T U :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hTU).2 integrableOn_zero
      have hrRight : IntervalIntegrable r volume T U := by
        apply hzero.congr
        intro t ht
        simp [r, hRiskRight t ht]
      have hdRight : IntervalIntegrable d volume T U := by
        apply hzero.congr
        intro t ht
        simp [d, hRiskRight t ht]
      have hrTail : (∫ t in T..U, r t) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        simp [r, hRiskRight t ht]
      have hdTail : (∫ t in T..U, d t) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        simp [d, hRiskRight t ht]
      have hrIntegral :
          (∫ t in (0 : ℝ)..T,
            continuationWeight (holderOrder c) h t * deathKMLeft a s t *
              P.lam a t) = ∫ t in (0 : ℝ)..U, r t := by
        have hs := intervalIntegral.integral_add_adjacent_intervals hrLeft hrRight
        rw [hrTail, add_zero] at hs
        rw [← hs]
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [r, hRiskClosed t ht, if_false]
      have hdIntegral :
          (∫ t in (0 : ℝ)..T,
            remainingTarget c P a h t * deathKMLeft a s t /
              survival P a t * P.hazard a t) =
            ∫ t in (0 : ℝ)..U, d t := by
        have hs := intervalIntegral.integral_add_adjacent_intervals hdLeft hdRight
        rw [hdTail, add_zero] at hs
        rw [← hs]
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [d, hRiskClosed t ht, if_false]
      have hCut (i : Fin n) (hai : (s i).treatment = a) :
          (s i).exit ≤ T ↔ (s i).exit ≤ U := by
        simp only [T, le_min_iff]
        exact and_iff_right (by rw [hext]; exact hmax i hai)
      have hdeathSum :
          (∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
              (s i).exit ≤ T then
                remainingTarget c P a h (s i).exit *
                  deathKMLeft a s (s i).exit / survival P a (s i).exit *
                    invRisk a s (s i).exit else 0) =
          ∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
              (s i).exit ≤ U then
                remainingTarget c P a h (s i).exit *
                  deathKMLeft a s (s i).exit / survival P a (s i).exit *
                    invRisk a s (s i).exit else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hai : (s i).treatment = a
        · by_cases hd : (s i).deathInd
          · by_cases ht : (s i).exit ≤ T
            · have hu := (hCut i hai).1 ht
              simp [hai, hd, ht, hu]
            · have hu : ¬(s i).exit ≤ U := fun hu => ht ((hCut i hai).2 hu)
              simp [hai, hd, ht, hu]
          · simp [hai, hd]
        · simp [hai]
      have hF0 : F 0 = truncatedMean c P a h := by
        simp [F, remainingTarget_at_zero, survival]
      have hboundary :
          deathKM a s T * F T = extinctionError c P a s h := by
        by_cases he : extinction a s < U
        · have hTe : T = extinction a s := by simp [T, min_eq_left he.le]
          rw [hTe]
          simp only [F, extinctionError, U, he, if_true]
          ring
        · have hUe : U ≤ extinction a s := le_of_not_gt he
          have hTe : T = U := by simp [T, min_eq_right hUe]
          rw [hTe]
          simp [F, extinctionError, U, he, remainingTarget_at_horizon]
      rw [hF0, hboundary, hrIntegral, hdIntegral, hdeathSum] at hprod
      unfold recurrenceError deathError
      dsimp [U, r, d] at hprod ⊢
      linarith
  · intro n hn
    filter_upwards [sample_death_exit_no_tie P hDeath n,
      sample_exit_le_one P n] with s hNoTie hExit
    intro a t hRisk
    have ht : t ≤ 1 := by
      obtain ⟨i, _, hti⟩ := (riskSet_pos_iff_assigned_exit a s t).mp hRisk
      exact hti.trans (hExit i)
    apply reverseKM_product_of_noDeathCensorTie a s t ht hRisk
    intro i j hai hdi haj hdc
    by_cases hij : i = j
    · subst j
      exact (hdc hdi).elim
    · exact hNoTie i j hij a hai hdi

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

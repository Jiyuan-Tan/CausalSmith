module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalIntervalLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FiniteSampleKM
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreTransport

/-!
# Early recurrence witnesses for critical nonfallback

Roadmap (31)--(32): a subject still observed at a recurrence time prevents
any earlier death product factor from vanishing. An early recurrence thus
contributes strictly positive optional variation. These are deterministic
sample facts; the uniform probability of such witnesses is a separate step.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A subject remaining at risk strictly beyond a death time prevents the
entire risk set from dying at that time, including samples with tied exits. -/
-- @node: deathJump_lt_riskSet_of_later_exit
lemma deathJump_lt_riskSet_of_later_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (i : Fin n) (hi : (s i).treatment = a)
    {u : ℝ} (hu : u < (s i).exit) : deathJump a s u < riskSet a s u := by
  classical
  have hj : deathJump a s u =
      (Finset.univ.filter (fun j : Fin n =>
        (s j).treatment = a ∧ (s j).deathInd ∧ (s j).exit = u)).card := by
    simp [deathJump]
  rw [hj, riskSet]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hj.2.2.ge⟩
  · intro heq
    have hm : i ∈ Finset.univ.filter (fun j : Fin n =>
        (s j).treatment = a ∧ u ≤ (s j).exit) := by simp [hi, hu.le]
    rw [← heq] at hm
    have he : (s i).exit = u := (Finset.mem_filter.mp hm).2.2.2
    exact (ne_of_gt hu) he

/-- Every death factor before a witnessed observed time is strictly positive. -/
-- @node: deathFactor_pos_of_later_exit
lemma deathFactor_pos_of_later_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (i : Fin n) (hi : (s i).treatment = a)
    {u : ℝ} (hu : u < (s i).exit) :
    0 < 1 - invRisk a s u * deathJump a s u := by
  have hj := deathJump_lt_riskSet_of_later_exit a s i hi hu
  have hr : 0 < riskSet a s u := (Nat.zero_le _).trans_lt hj
  have hrR : (0 : ℝ) < riskSet a s u := by exact_mod_cast hr
  have hjR : (deathJump a s u : ℝ) < riskSet a s u := by exact_mod_cast hj
  rw [invRisk, if_neg (Nat.ne_of_gt hr), ← div_eq_inv_mul]
  exact sub_pos.mpr ((div_lt_one hrR).mpr hjR)

/-- The left Kaplan--Meier survival is positive at every time with a
same-arm observed subject still at risk. -/
-- @node: deathKMLeft_pos_of_assigned_exit
lemma deathKMLeft_pos_of_assigned_exit {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (i : Fin n) (hi : (s i).treatment = a)
    {t : ℝ} (ht : t ≤ (s i).exit) : 0 < deathKMLeft a s t := by
  classical
  unfold deathKMLeft
  apply Finset.prod_pos
  intro u hu
  exact deathFactor_pos_of_later_exit a s i hi
    ((Finset.mem_filter.mp hu).2.trans_le ht)

/-- The ordinary part of the continuation weight equals one strictly before
its terminal band. -/
-- @node: continuationWeight_eq_one_before_band
lemma continuationWeight_eq_one_before_band (ell : ℕ) {h t : ℝ}
    (hh : 0 ≤ h) (ht : t < 1 - 2 * h) : continuationWeight ell h t = 1 := by
  have htT : t ≤ 1 - h := by linarith
  simp [continuationWeight, htT, not_le.mpr ht]

/-- A recurrence observed before the continuation band gives a strictly
positive contribution to the actual armwise optional variation. -/
-- @node: armCriticalVariance_pos_of_early_recurrence
lemma armCriticalVariance_pos_of_early_recurrence (c : ClassConstants)
    {n : ℕ} (hn : 0 < n) (a : Arm) (s : Fin n → ObsHistory)
    (i : Fin n) (hi : (s i).treatment = a) (k : Fin (s i).recur.1)
    (htExit : (((s i).recur).2 k).1 ≤ (s i).exit)
    (htBand : (((s i).recur).2 k).1 < 1 - 2 * bandwidth c n) :
    0 < armCriticalVariance c a s := by
  classical
  have hh := (bandwidth_pos_and_le_cap c hn).1
  have htT : (((s i).recur).2 k).1 ≤ 1 - bandwidth c n := by linarith
  have hr := (riskSet_pos_iff_assigned_exit a s _).mpr ⟨i, hi, htExit⟩
  have hrR : (0 : ℝ) < riskSet a s (((s i).recur).2 k).1 := by exact_mod_cast hr
  have hinv : 0 < invRisk a s (((s i).recur).2 k).1 := by
    rw [invRisk, if_neg (Nat.ne_of_gt hr)]
    exact inv_pos.mpr hrR
  have hkm := deathKMLeft_pos_of_assigned_exit a s i hi htExit
  unfold armCriticalVariance
  apply Finset.sum_pos'
  · intro j _
    split_ifs
    · apply Multiset.sum_nonneg
      intro x hx
      obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp hx
      positivity
    · rfl
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [if_pos hi, recurrence_times_filtered_sum]
    apply Finset.sum_pos'
    · intro j _
      split_ifs <;> positivity
    · refine ⟨k, Finset.mem_univ _, ?_⟩
      rw [if_pos htT, continuationWeight_eq_one_before_band (holderOrder c) hh.le htBand]
      exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hkm)) (sq_pos_of_pos hinv)

/-- The sum over both arms retains any positive armwise recurrence contribution. -/
-- @node: criticalVarianceEstimator_pos_of_early_recurrence
lemma criticalVarianceEstimator_pos_of_early_recurrence (c : ClassConstants)
    {n : ℕ} (hn : 0 < n) (a : Arm) (s : Fin n → ObsHistory)
    (i : Fin n) (hi : (s i).treatment = a) (k : Fin (s i).recur.1)
    (htExit : (((s i).recur).2 k).1 ≤ (s i).exit)
    (htBand : (((s i).recur).2 k).1 < 1 - 2 * bandwidth c n) :
    0 < criticalVarianceEstimator c s := by
  have hp := armCriticalVariance_pos_of_early_recurrence c hn a s i hi k htExit htBand
  cases a
  · exact add_pos_of_pos_of_nonneg hp (armCriticalVariance_nonneg c true s)
  · exact add_pos_of_nonneg_of_pos (armCriticalVariance_nonneg c false s) hp

/-- Roadmap (32)'s deterministic implication: one early observed recurrence
in each arm ensures both arms are present and the studentizer is positive. -/
-- @node: nonFallback_of_early_recurrence_witnesses
lemma nonFallback_of_early_recurrence_witnesses (c : ClassConstants)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory)
    (hw : ∀ a : Arm, ∃ i : Fin n, (s i).treatment = a ∧
      ∃ k : Fin (s i).recur.1,
        (((s i).recur).2 k).1 ≤ (s i).exit ∧
        (((s i).recur).2 k).1 < 1 - 2 * bandwidth c n) :
    nonFallback c s := by
  have ha (a : Arm) : 0 < armSize a s := by
    obtain ⟨i, hi, k, ht, _⟩ := hw a
    exact riskSet_pos_armSize_pos a s _
      ((riskSet_pos_iff_assigned_exit a s _).mpr ⟨i, hi, ht⟩)
  obtain ⟨i, hi, k, ht, hb⟩ := hw false
  exact ⟨ha false, ha true,
    criticalVarianceEstimator_pos_of_early_recurrence c hn false s i hi k ht hb⟩

/-- Iid sampling gives the exact geometric probability of seeing no member
of any measurable subject event. -/
-- @node: sampleLaw_no_event_probability
lemma sampleLaw_no_event_probability (P : SubjectLaw) (n : ℕ)
    (B : Set ObsHistory) (hB : MeasurableSet B) :
    (sampleLaw P n).real {s | ∀ i, s i ∉ B} =
      (1 - (observedLaw P).real B) ^ n := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have he : {s : Fin n → ObsHistory | ∀ i, s i ∉ B} =
      Set.pi Set.univ (fun _ => Bᶜ) := by
    ext s
    simp [Set.mem_pi]
  rw [he, sampleLaw, measureReal_def, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [← measureReal_def, probReal_compl_eq_one_sub hB]

/-- Fallback requires the absence of a subject witness in at least one arm.
The events may be any concrete early-recurrence events satisfying the stated
pointwise implication; no probability or rate is assumed here. -/
-- @node: nonFallback_compl_subset_no_early_witness
lemma nonFallback_compl_subset_no_early_witness (c : ClassConstants)
    {n : ℕ} (hn : 0 < n) (B : Arm → Set ObsHistory)
    (hB : ∀ a o, o ∈ B a → o.treatment = a ∧
      ∃ k : Fin o.recur.1, (o.recur.2 k).1 ≤ o.exit ∧
        (o.recur.2 k).1 < 1 - 2 * bandwidth c n) :
    {s : Fin n → ObsHistory | ¬ nonFallback c s} ⊆
      {s | ∀ i, s i ∉ B false} ∪ {s | ∀ i, s i ∉ B true} := by
  intro s hs
  by_contra h
  have hf : ∃ i, s i ∈ B false := by
    simpa only [not_forall, not_not] using
      (show ¬ (∀ i, s i ∉ B false) from fun hh => h (Or.inl hh))
  have ht : ∃ i, s i ∈ B true := by
    simpa only [not_forall, not_not] using
      (show ¬ (∀ i, s i ∉ B true) from fun hh => h (Or.inr hh))
  apply hs
  apply nonFallback_of_early_recurrence_witnesses c hn s
  intro a
  have ha : ∃ i, s i ∈ B a := by cases a <;> assumption
  obtain ⟨i, hi⟩ := ha
  exact ⟨i, hB a (s i) hi⟩

/-- The genuine probability bridge in roadmap (32): a union bound and iid
sampling turn concrete subject recurrence witnesses into geometric fallback
control. Establishing the uniform positive subject probability in (31)
remains independent of this bridge. -/
-- @node: nonFallback_compl_probability_le_no_early_witness
lemma nonFallback_compl_probability_le_no_early_witness (c : ClassConstants)
    (P : SubjectLaw) {n : ℕ} (hn : 0 < n) (B : Arm → Set ObsHistory)
    (hm : ∀ a, MeasurableSet (B a))
    (hB : ∀ a o, o ∈ B a → o.treatment = a ∧
      ∃ k : Fin o.recur.1, (o.recur.2 k).1 ≤ o.exit ∧
        (o.recur.2 k).1 < 1 - 2 * bandwidth c n) :
    (sampleLaw P n).real {s | ¬ nonFallback c s} ≤
      (1 - (observedLaw P).real (B false)) ^ n +
        (1 - (observedLaw P).real (B true)) ^ n := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  calc
    _ ≤ (sampleLaw P n).real ({s | ∀ i, s i ∉ B false} ∪
        {s | ∀ i, s i ∉ B true}) :=
      measureReal_mono (nonFallback_compl_subset_no_early_witness c hn B hB) (by finiteness)
    _ ≤ (sampleLaw P n).real {s | ∀ i, s i ∉ B false} +
        (sampleLaw P n).real {s | ∀ i, s i ∉ B true} := measureReal_union_le _ _
    _ = _ := by rw [sampleLaw_no_event_probability P n _ (hm false),
      sampleLaw_no_event_probability P n _ (hm true)]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

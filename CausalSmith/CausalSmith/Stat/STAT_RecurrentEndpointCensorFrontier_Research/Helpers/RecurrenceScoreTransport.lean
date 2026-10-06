module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreEnergy
/-!
# Concrete recurrence score transport

Stable stopping preserves weighted point sums. The observable recurrence error
is exactly the sum of latent compensated scores, and those scores depend only
on treatment and same-arm death/censor exposure. Non-arm exit times contribute
unit factors to the death Kaplan–Meier product and cannot change these scores.
-/
@[expose] public section
open MeasureTheory Set
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier
/-- A filtered event-multiset integral is the corresponding finite indexed point sum. -/
-- @node: recurrence_times_filtered_sum
lemma recurrence_times_filtered_sum (s : RecurConfig) (T : ℝ) (f : ℝ → ℝ) :
    ((s.times.filter (fun t => t ≤ T)).map f).sum =
      ∑ i : Fin s.1, if (s.2 i).1 ≤ T then f (s.2 i).1 else 0 := by
  classical
  have hlist (l : List ℝ) :
      ((l.filter (fun t => decide (t ≤ T))).map f).sum =
        (l.map (fun t => if t ≤ T then f t else 0)).sum := by
    induction l with
    | nil => simp
    | cons t l ih =>
      by_cases ht : t ≤ T <;> simp [ht, ih]
  simp only [RecurConfig.times, FiniteSample.count, FiniteSample.points, Multiset.filter_coe,
    Multiset.map_coe, Multiset.sum_coe]
  rw [hlist]
  simp [List.map_ofFn, List.sum_ofFn]
/-- Stable stopping retains exactly the weighted points before both exit and the estimation
horizon. -/
-- @node: recurrence_stopped_weighted_sum
lemma recurrence_stopped_weighted_sum (s : RecurConfig) (x T : ℝ) (f : ℝ → ℝ) :
    (((s.stopAt x).times.filter (fun t => t ≤ T)).map f).sum =
      ∑ i : Fin s.1, if (s.2 i).1 ≤ x ∧ (s.2 i).1 ≤ T
        then f (s.2 i).1 else 0 := by
  classical
  rw [recurrence_times_filtered_sum, RecurConfig.stopAt_eq_restrictAt]
  unfold RecurConfig.restrictAt
  simp only [FiniteMeasurablePartition.restrictCell, FiniteSample.count,
    FiniteSample.points]
  let u := (timeCutPartition x).cellIndices true s
  change (∑ k : Fin u.card, if (s.2 ((u.orderIsoOfFin rfl k).1)).1 ≤ T
      then f (s.2 ((u.orderIsoOfFin rfl k).1)).1 else 0) = _
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => (u.orderIsoOfFin rfl k).1)
  · intro k hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hk).2⟩
    have hu := (u.orderIsoOfFin rfl k).2
    simpa [u, FiniteMeasurablePartition.cellIndices, timeCutPartition,
      FiniteSample.points] using hu
  · intro k₁ _ k₂ _ heq
    exact (u.orderIsoOfFin rfl).injective (Subtype.ext heq)
  · intro i hi
    have hip := (Finset.mem_filter.mp hi).2
    have hiu : i ∈ u := by
      simpa [u, FiniteMeasurablePartition.cellIndices, timeCutPartition,
        FiniteSample.points] using hip.1
    let k : Fin u.card := (u.orderIsoOfFin rfl).symm ⟨i, hiu⟩
    refine ⟨k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa [k] using hip.2⟩
    · simp [k]
  · intro k hk
    rfl
/-- The unprojected observed estimator is the sum of the same-arm latent point scores, with
stopping encoded in each subject weight. -/
-- @node: recurrence_muTilde_eq_latent_point_scores
lemma recurrence_muTilde_eq_latent_point_scores (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (z : Fin n → LatentSubject) :
    muTildeAt c h a (fun i => observe (z i)) =
      ∑ i : Fin n, ∑ k : Fin ((z i).recur a).1,
        if (((z i).recur a).2 k).1 ≤ 1 - h then
          recurrenceSubjectWeight c h a (fun j => observe (z j)) i
            (((z i).recur a).2 k).1 else 0 := by
  classical
  unfold muTildeAt
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (z i).treatment = a
  · simp only [observe, hi, ↓reduceIte]
    rw [recurrence_stopped_weighted_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [recurrenceSubjectWeight, hi, true_and]
    by_cases hx : (((z i).recur a).2 k).1 ≤ min ((z i).death a) (censorHorizon (z i) a)
    <;> by_cases ht : (((z i).recur a).2 k).1 ≤ 1 - h
    <;> simp [hx, ht]
  · simp only [observe, hi, ↓reduceIte]
    simp [recurrenceSubjectWeight, hi]

/-- The actual recurrence error is the sum of latent subject point scores minus their intensity
compensators. -/
-- @node: recurrenceError_eq_latent_compensated_scores
lemma recurrenceError_eq_latent_compensated_scores (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      ∑ i : Fin n,
        ((∑ k : Fin ((z i).recur a).1,
          if (((z i).recur a).2 k).1 ≤ 1 - h then
            recurrenceSubjectWeight c h a (fun j => observe (z j)) i
              (((z i).recur a).2 k).1 else 0) -
        ∫ t in (0 : ℝ)..(1 - h),
          recurrenceSubjectWeight c h a (fun j => observe (z j)) i t * P.lam a t) := by
  rw [recurrenceError_eq_subject_compensators c P hP a _ hh hh1,
    recurrence_muTilde_eq_latent_point_scores, Finset.sum_sub_distrib]
/-- There is no death jump at a time outside the observed exit-time set. -/
-- @node: recurrence_deathJump_zero_off_exitTimes
lemma recurrence_deathJump_zero_off_exitTimes {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) {t : ℝ} (ht : t ∉ exitTimes s) :
    deathJump a s t = 0 := by
  classical
  unfold deathJump
  apply Finset.sum_eq_zero
  intro i _
  have hi : (s i).exit ≠ t := by
    intro heq
    apply ht
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  simp [hi]

/-- Adding unused exit times to the death Kaplan–Meier product contributes only unit factors. -/
-- @node: recurrence_deathKMLeft_eq_prod_superset
lemma recurrence_deathKMLeft_eq_prod_superset {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (E : Finset ℝ)
    (hE : exitTimes s ⊆ E) :
    deathKMLeft a s t = ∏ u ∈ E.filter (fun u => u < t),
      (1 - invRisk a s u * deathJump a s u) := by
  classical
  unfold deathKMLeft
  apply Finset.prod_subset
  · intro u hu
    exact Finset.mem_filter.mpr ⟨hE (Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2⟩
  · intro u hu hnot
    have hux : u ∉ exitTimes s := by
      intro hx
      exact hnot (Finset.mem_filter.mpr ⟨hx, (Finset.mem_filter.mp hu).2⟩)
    rw [recurrence_deathJump_zero_off_exitTimes a s hux]
    simp

/-- Point scores depend only on assignment and the exit and death status of subjects assigned to
the selected arm. -/
-- @node: recurrenceSubjectWeight_arm_exposure_congr
lemma recurrenceSubjectWeight_arm_exposure_congr (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s r : Fin n → ObsHistory)
    (hA : ∀ i, (s i).treatment = (r i).treatment)
    (hX : ∀ i, (s i).treatment = a → (s i).exit = (r i).exit)
    (hD : ∀ i, (s i).treatment = a → (s i).deathInd = (r i).deathInd)
    (i : Fin n) (t : ℝ) :
    recurrenceSubjectWeight c h a s i t = recurrenceSubjectWeight c h a r i t := by
  classical
  have hrisk (u : ℝ) : riskSet a s u = riskSet a r u := by
    unfold riskSet
    congr 1
    ext j
    by_cases hj : (s j).treatment = a
    · simp [← hA, hj, hX j hj]
    · simp [← hA, hj]
  have hinv (u : ℝ) : invRisk a s u = invRisk a r u := by
    simp only [invRisk, hrisk]
  have hjump (u : ℝ) : deathJump a s u = deathJump a r u := by
    unfold deathJump
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : (s j).treatment = a
    · simp [← hA, hj, hX j hj, hD j hj]
    · simp [← hA, hj]
  have hkm : deathKMLeft a s t = deathKMLeft a r t := by
    rw [recurrence_deathKMLeft_eq_prod_superset a s t
      (exitTimes s ∪ exitTimes r) Finset.subset_union_left,
      recurrence_deathKMLeft_eq_prod_superset a r t
      (exitTimes s ∪ exitTimes r) Finset.subset_union_right]
    simp only [hinv, hjump]
  by_cases hi : (s i).treatment = a
  · simp [recurrenceSubjectWeight, ← hA, hi, hX i hi, hkm, hinv]
  · simp [recurrenceSubjectWeight, ← hA, hi]
/-- A synthetic observed record carries treatment and same-arm death/censor exposure, with an
empty recurrence configuration. -/
-- @node: recurrenceExposureHistory
noncomputable def recurrenceExposureHistory (e : Arm × (ℝ × ENNReal)) : ObsHistory :=
  let C := if e.2.2 = ⊤ then 1 else min e.2.2.toReal 1
  { treatment := e.1
    exit := min e.2.1 C
    deathInd := decide (e.2.1 ≤ C)
    recur := RecurConfig.empty }

/-- Replacing observations by their exposure-only synthetic records preserves every point score.
-/
-- @node: recurrenceSubjectWeight_eq_exposureHistory
lemma recurrenceSubjectWeight_eq_exposureHistory (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (z : Fin n → LatentSubject) (i : Fin n) (t : ℝ) :
    recurrenceSubjectWeight c h a (fun j => observe (z j)) i t =
      recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory
        ((z j).treatment, ((z j).death a, (z j).censor a))) i t := by
  apply recurrenceSubjectWeight_arm_exposure_congr
  · intro j
    rfl
  · intro j hj
    change (z j).treatment = a at hj
    simp [observe, recurrenceExposureHistory, censorHorizon, hj]
  · intro j hj
    change (z j).treatment = a at hj
    simp [observe, recurrenceExposureHistory, censorHorizon, hj]

/-- The concrete compensated recurrence score as a function of the exposure array and
independent latent recurrence configurations. -/
-- @node: recurrenceConcreteExposureScore
noncomputable def recurrenceConcreteExposureScore (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) (n : ℕ) (h : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) : ℝ :=
  ∑ i : Fin n,
    ((∑ k : Fin (r i).1, if ((r i).2 k).1 ≤ 1 - h then
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i
          ((r i).2 k).1 else 0) -
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a
        (fun j => recurrenceExposureHistory (e j)) i t * P.lam a t)

/-- The observed recurrence error is exactly the concrete exposure score, ready for transport
through the canonical exposure/Poisson product law. -/
-- @node: recurrenceError_eq_concreteExposureScore
lemma recurrenceError_eq_concreteExposureScore (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      recurrenceConcreteExposureScore c P a n h
        (fun i => ((z i).treatment, ((z i).death a, (z i).censor a)))
        (fun i => (z i).recur a) := by
  rw [recurrenceError_eq_latent_compensated_scores c P hP a z hh hh1]
  unfold recurrenceConcreteExposureScore
  simp_rw [recurrenceSubjectWeight_eq_exposureHistory]
end CausalSmith.Stat.RecurrentEndpointCensorFrontier

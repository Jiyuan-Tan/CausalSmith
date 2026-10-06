module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RiskEnvelopes

/-!
# Concrete recurrence point-score energy

The subject scores keep their time-dependent inverse risk. Summing their
squares cancels one inverse-risk factor, rather than replacing it by an
endpoint bound. The score sum also identifies the recurrence compensator.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The time score for one subject, before restriction to the integration horizon. -/
-- @node: recurrenceSubjectWeight
noncomputable def recurrenceSubjectWeight (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) : ℝ :=
  if (s i).treatment = a ∧ t ≤ (s i).exit then
    continuationWeight (holderOrder c) h t * deathKMLeft a s t * invRisk a s t
  else 0

/-- The observed zero-safe inverse risk is between zero and one. -/
-- @node: recurrence_invRisk_mem_Icc
lemma recurrence_invRisk_mem_Icc {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) : invRisk a s t ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hz : riskSet a s t = 0
  · simp [invRisk, hz]
  · have hp : (1 : ℝ) ≤ riskSet a s t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    simp only [invRisk, hz, ↓reduceIte, Set.mem_Icc]
    exact ⟨by positivity, inv_le_one_of_one_le₀ hp⟩

/-- Recurrence point scores are uniformly bounded by the continuation envelope. -/
-- @node: recurrenceSubjectWeight_abs_le
lemma recurrenceSubjectWeight_abs_le (c : ClassConstants) {h : ℝ}
    (hh : 0 < h) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) :
    |recurrenceSubjectWeight c h a s i t| ≤ weightEnvelope c := by
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  unfold recurrenceSubjectWeight
  split_ifs
  · rw [abs_mul, abs_mul, abs_of_nonneg (deathKMLeft_mem_Icc a s t).1,
      abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
    calc
      _ ≤ weightEnvelope c * 1 * 1 := by
        gcongr
        · exact (recurrence_invRisk_mem_Icc a s t).1
        · exact (deathKMLeft_mem_Icc a s t).1
        · exact continuationWeight_abs_le_coeffSum (holderOrder c) hh
        · exact (deathKMLeft_mem_Icc a s t).2
        · exact (recurrence_invRisk_mem_Icc a s t).2
      _ = _ := by ring
  · simpa using hW

/-- For fixed data, the risk count is measurable in time. -/
-- @node: measurable_recurrenceRiskSet
@[fun_prop]
lemma measurable_recurrenceRiskSet {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    Measurable (riskSet a s) := by
  classical
  have heq : riskSet a s = fun t => ∑ i : Fin n,
      if (s i).treatment = a ∧ t ≤ (s i).exit then (1 : ℕ) else 0 := by
    funext t
    simp [riskSet]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (s i).treatment = a
  · simp only [hi, true_and]
    exact measurable_const.ite (measurableSet_le measurable_id measurable_const)
      measurable_const
  · simp only [hi, false_and, ↓reduceIte]
    exact measurable_const

/-- The zero-safe inverse risk is measurable in time. -/
-- @node: measurable_recurrenceInvRisk
@[fun_prop]
lemma measurable_recurrenceInvRisk {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    Measurable (invRisk a s) := by
  unfold invRisk
  apply Measurable.ite
    (measurableSet_eq_fun (measurable_recurrenceRiskSet a s) measurable_const)
  · exact measurable_const
  · fun_prop

/-- The continuation multiplier is measurable at every bandwidth. -/
-- @node: measurable_recurrenceContinuationWeight
@[fun_prop]
lemma measurable_recurrenceContinuationWeight (c : ClassConstants) (h : ℝ) :
    Measurable (continuationWeight (holderOrder c) h) := by
  unfold continuationWeight
  by_cases hz : h = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    apply Measurable.add
    · exact measurable_const.ite
        (measurableSet_le measurable_id measurable_const) measurable_const
    · apply ((continuationPoly_continuous _).measurable.comp (by fun_prop)).ite
      · exact (measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const)
      · exact measurable_const

/-- Each concrete subject score is measurable in time. -/
-- @node: measurable_recurrenceSubjectWeight
@[fun_prop]
lemma measurable_recurrenceSubjectWeight (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) :
    Measurable (recurrenceSubjectWeight c h a s i) := by
  unfold recurrenceSubjectWeight
  by_cases hi : (s i).treatment = a
  · simp only [hi, true_and]
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · exact ((measurable_recurrenceContinuationWeight c h).mul
        (measurable_deathKMLeft a s)).mul (measurable_recurrenceInvRisk a s)
    · exact measurable_const
  · simp only [hi, false_and, ↓reduceIte]
    exact measurable_const

/-- Every finite power of the point score can multiply the integrable intensity
on the estimation interval. The needed regularity follows from the model. -/
-- @node: recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable
lemma recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (i : Fin n) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (k : ℕ) :
    IntervalIntegrable (fun t => recurrenceSubjectWeight c h a s i t ^ k *
      P.lam a t) volume 0 (1 - h) := by
  have hT : 0 ≤ 1 - h := by linarith
  have hlam : IntervalIntegrable (P.lam a) volume 0 (1 - h) :=
    (poissonRecurrence_intervalIntegrable P hP.poissonRecurrence a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hlam ⊢
  apply hlam.bdd_mul (c := weightEnvelope c ^ k)
    ((measurable_recurrenceSubjectWeight c h a s i).pow_const k
      |>.aestronglyMeasurable.restrict)
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (recurrenceSubjectWeight_abs_le c hh a s i t) k

/-- Summation over the at-risk subjects is multiplication by the risk count. -/
-- @node: recurrence_atRisk_sum
lemma recurrence_atRisk_sum {n : ℕ} (a : Arm) (s : Fin n → ObsHistory)
    (t v : ℝ) :
    (∑ i : Fin n, if (s i).treatment = a ∧ t ≤ (s i).exit then v else 0) =
      (riskSet a s t : ℝ) * v := by
  classical
  rw [← Finset.sum_filter]
  simp [riskSet, nsmul_eq_mul]

/-- Zero-safe inverse risk cancels one of its two factors against the risk count. -/
-- @node: recurrence_risk_mul_invRisk_sq
lemma recurrence_risk_mul_invRisk_sq {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) :
    (riskSet a s t : ℝ) * invRisk a s t ^ 2 = invRisk a s t := by
  by_cases hz : riskSet a s t = 0
  · simp [invRisk, hz]
  · have hc : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
    simp only [invRisk, hz, ↓reduceIte]
    field_simp

/-- Summed point scores are exactly the zero-safe compensator multiplier. -/
-- @node: recurrenceSubjectWeight_sum
lemma recurrenceSubjectWeight_sum (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t) =
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else 1) := by
  unfold recurrenceSubjectWeight
  rw [recurrence_atRisk_sum]
  rw [show (riskSet a s t : ℝ) *
      (continuationWeight (holderOrder c) h t * deathKMLeft a s t * invRisk a s t) =
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        ((riskSet a s t : ℝ) * invRisk a s t) by ring]
  rw [riskSet_mul_invRisk]

/-- The exact diagonal energy retains inverse risk at each time. -/
-- @node: recurrenceSubjectWeight_sum_sq
lemma recurrenceSubjectWeight_sum_sq (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) =
      continuationWeight (holderOrder c) h t ^ 2 * deathKMLeft a s t ^ 2 *
        invRisk a s t := by
  classical
  simp only [recurrenceSubjectWeight, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [recurrence_atRisk_sum]
  rw [show (riskSet a s t : ℝ) *
      (continuationWeight (holderOrder c) h t * deathKMLeft a s t * invRisk a s t) ^ 2 =
      continuationWeight (holderOrder c) h t ^ 2 * deathKMLeft a s t ^ 2 *
        ((riskSet a s t : ℝ) * invRisk a s t ^ 2) by ring]
  rw [recurrence_risk_mul_invRisk_sq]

/-- The concrete energy density is bounded without replacing inverse risk by
its endpoint value. -/
-- @node: recurrenceSubjectWeight_energy_density_le
lemma recurrenceSubjectWeight_energy_density_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) * P.lam a t ≤
      weightEnvelope c ^ 2 * c.lambdaMax * invRisk a s t := by
  have hw : |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c :=
    continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hw2 : continuationWeight (holderOrder c) h t ^ 2 ≤ weightEnvelope c ^ 2 :=
    by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hW).2 hw
  have hk := deathKMLeft_mem_Icc a s t
  have hk2 : deathKMLeft a s t ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
  have hi : 0 ≤ invRisk a s t := by
    unfold invRisk
    split_ifs <;> positivity
  have hl := hP.recurrenceBounds a t ht
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hl.1
  rw [recurrenceSubjectWeight_sum_sq]
  calc
    _ ≤ weightEnvelope c ^ 2 * 1 * invRisk a s t * P.lam a t := by
      gcongr
    _ ≤ weightEnvelope c ^ 2 * c.lambdaMax * invRisk a s t := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (weightEnvelope c)) hi)
        (sub_nonneg.mpr hl.2)]

/-- Summing the individual intensity integrals recovers precisely the
compensator subtracted in the observable recurrence error. -/
-- @node: recurrenceSubjectWeight_compensator_eq
lemma recurrenceSubjectWeight_compensator_eq (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t * P.lam a t) =
    ∫ t in (0 : ℝ)..(1 - h),
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else P.lam a t) := by
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← Finset.sum_mul, recurrenceSubjectWeight_sum]
    split_ifs <;> ring
  · intro i _
    simpa only [pow_one] using
      recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 1

/-- The recurrence error uses the sum of the individual point-score compensators. -/
-- @node: recurrenceError_eq_subject_compensators
lemma recurrenceError_eq_subject_compensators (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    recurrenceError c P a s h = muTildeAt c h a s -
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t * P.lam a t := by
  rw [recurrenceSubjectWeight_compensator_eq c P hP a s hh hh1]
  rfl

/-- The integrated subject diagonal energy equals the concrete inverse-risk
energy, with the time-dependent risk factor retained inside the integral. -/
-- @node: recurrenceSubjectWeight_integrated_energy_eq
lemma recurrenceSubjectWeight_integrated_energy_eq (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) =
    ∫ t in (0 : ℝ)..(1 - h),
      continuationWeight (holderOrder c) h t ^ 2 * deathKMLeft a s t ^ 2 *
        invRisk a s t * P.lam a t := by
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← Finset.sum_mul, recurrenceSubjectWeight_sum_sq]
  · intro i _
    exact recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 2

/-- Changing recurrence marks while preserving treatment, exit, and death
status leaves every point score unchanged. Thus the integrand depends only on
exposure, as required by the canonical exposure/Poisson product law. -/
-- @node: recurrenceSubjectWeight_exposure_congr
lemma recurrenceSubjectWeight_exposure_congr (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s r : Fin n → ObsHistory)
    (hA : ∀ i, (s i).treatment = (r i).treatment)
    (hX : ∀ i, (s i).exit = (r i).exit)
    (hD : ∀ i, (s i).deathInd = (r i).deathInd) (i : Fin n) (t : ℝ) :
    recurrenceSubjectWeight c h a s i t = recurrenceSubjectWeight c h a r i t := by
  have hrisk (u : ℝ) : riskSet a s u = riskSet a r u := by
    unfold riskSet
    simp_rw [hA, hX]
  have hinv (u : ℝ) : invRisk a s u = invRisk a r u := by
    simp only [invRisk, hrisk]
  have hexit : exitTimes s = exitTimes r := by
    unfold exitTimes
    simp_rw [hX]
  have hjump (u : ℝ) : deathJump a s u = deathJump a r u := by
    unfold deathJump
    simp_rw [hA, hD, hX]
  have hkm : deathKMLeft a s t = deathKMLeft a r t := by
    unfold deathKMLeft
    simp only [hexit, hinv, hjump]
  simp only [recurrenceSubjectWeight, hA, hX, hkm, hinv]

/-- Inverse risk is integrable on every finite nonnegative time interval. -/
-- @node: recurrenceInvRisk_intervalIntegrable
lemma recurrenceInvRisk_intervalIntegrable {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (invRisk a s) volume 0 T := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T :=
    intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hone ⊢
  have hi := hone.bdd_mul (c := 1)
    (measurable_recurrenceInvRisk a s).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
      exact (recurrence_invRisk_mem_Icc a s t).2))
  simpa only [IntegrableOn, mul_one] using hi

/-- The integrated diagonal energy is bounded by the integral of inverse risk.
No endpoint supremum of the risk factor is taken. -/
-- @node: recurrenceSubjectWeight_integrated_energy_le
lemma recurrenceSubjectWeight_integrated_energy_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ≤
    weightEnvelope c ^ 2 * c.lambdaMax *
      ∫ t in (0 : ℝ)..(1 - h), invRisk a s t := by
  have hT : 0 ≤ 1 - h := by linarith
  have hi (i : Fin n) :=
    recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 2
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i),
    ← intervalIntegral.integral_const_mul]
  have hsum : IntervalIntegrable (fun t => ∑ i : Fin n,
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) volume 0 (1 - h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact integrable_finsetSum Finset.univ (fun i _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hi i))
  apply intervalIntegral.integral_mono_on hT hsum
    ((recurrenceInvRisk_intervalIntegrable a s hT).const_mul
      (weightEnvelope c ^ 2 * c.lambdaMax))
  intro t ht
  rw [← Finset.sum_mul]
  exact recurrenceSubjectWeight_energy_density_le c P hP a s hh
    ⟨ht.1, ht.2.trans (by linarith)⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

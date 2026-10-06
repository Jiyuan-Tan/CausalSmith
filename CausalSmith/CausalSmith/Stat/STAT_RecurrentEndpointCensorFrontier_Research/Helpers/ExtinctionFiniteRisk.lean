module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition

/-! # Finite-sample extinction remainder

The final positive-risk time identifies the empty-risk event, and the
Kaplan--Meier product and survival bounds control its remainder.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: deathKM_mem_Icc
lemma deathKM_mem_Icc {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) :
    deathKM a s t ∈ Icc (0 : ℝ) 1 := by
  unfold deathKM
  constructor
  · exact Finset.prod_nonneg fun u _ => (deathFactor_mem_Icc a s u).1
  · exact Finset.prod_le_one (fun _ _ => (deathFactor_mem_Icc a s _).1)
      (fun u _ => (deathFactor_mem_Icc a s u).2)

-- @node: extinction_nonneg_of_exit_bounds
lemma extinction_nonneg_of_exit_bounds {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).treatment = a → 0 ≤ (s i).exit ∧ (s i).exit ≤ 1) :
    0 ≤ extinction a s := by
  by_cases hArm : armSize a s = 0
  · simp [extinction, hArm]
  · obtain ⟨i, hi, he, _⟩ :=
      extinction_eq_max_assigned_exit a s (Nat.pos_of_ne_zero hArm) hExit
    rw [he]
    exact (hExit i hi).1

-- @node: extinction_lt_iff_riskSet_zero
lemma extinction_lt_iff_riskSet_zero {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).treatment = a → 0 ≤ (s i).exit ∧ (s i).exit ≤ 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    extinction a s < t ↔ riskSet a s t = 0 := by
  constructor
  · exact riskSet_zero_after_extinction a s t ht.le ht1
  · intro hz
    by_cases hArm : armSize a s = 0
    · simpa [extinction, hArm] using ht
    · have hiff := riskSet_pos_iff_le_extinction a s (Nat.pos_of_ne_zero hArm) hExit t
      exact lt_of_not_ge (fun hle => by
        have hp := hiff.mpr hle
        rw [hz] at hp
        exact (lt_irrefl 0) hp)

-- @node: extinctionError_abs_le_indicator
lemma extinctionError_abs_le_indicator (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).treatment = a → 0 ≤ (s i).exit ∧ (s i).exit ≤ 1)
    {h : ℝ} (hh : 0 < h) :
    |extinctionError c P a s h| ≤
      if riskSet a s (1 - h) = 0 then
        weightEnvelope c * c.lambdaMax * Real.exp c.dMax else 0 := by
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hB : 0 ≤ weightEnvelope c * c.lambdaMax * Real.exp c.dMax := by positivity
  by_cases he : extinction a s < 1 - h
  · have he0 := extinction_nonneg_of_exit_bounds a s hExit
    have ht : extinction a s ∈ Icc (0 : ℝ) (1 - h) := ⟨he0, he.le⟩
    have hs0 : 0 < survival P a (extinction a s) := Real.exp_pos _
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨he0, by linarith⟩).1
    have hinv : (survival P a (extinction a s))⁻¹ ≤ Real.exp c.dMax := by
      calc
        _ ≤ (Real.exp (-c.dMax))⁻¹ :=
          (inv_le_inv₀ hs0 (Real.exp_pos _)).2 hs
        _ = _ := by rw [Real.exp_neg]; simp
    have hkm := deathKM_mem_Icc a s (extinction a s)
    have hrem := remainingTarget_abs_le_weightEnvelope c P hP a hh ht
    rw [if_pos (riskSet_zero_after_extinction a s (1 - h) (by linarith) (by linarith) he),
      extinctionError, if_pos he, abs_mul, abs_div, abs_of_nonneg hkm.1,
      abs_of_pos hs0, div_eq_mul_inv]
    calc
      _ ≤ (1 * Real.exp c.dMax) * (weightEnvelope c * c.lambdaMax) := by
        exact mul_le_mul (mul_le_mul hkm.2 hinv (inv_nonneg.mpr hs0.le)
          (by norm_num)) hrem (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [extinctionError, if_neg he, abs_zero]
    split_ifs <;> positivity

-- @node: observed_arm_risk_probability
lemma observed_arm_risk_probability (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (observedLaw P).real {o | o.treatment = a ∧ t ≤ o.exit} =
      P.p a * survival P a t * retention P a t := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hind : IndepFun LatentSubject.treatment
      (fun z : LatentSubject => min (z.death a) (censorHorizon z a)) P.latent := by
    have hi := hP.randomAssignment.comp measurable_id
      (show Measurable (fun r : (Arm → RecurConfig) ×
        ((Arm → ℝ) × (Arm → ENNReal)) =>
          min (r.2.1 a) (censorHorizonValue (r.2.2 a))) by fun_prop)
    simpa only [Function.comp_def, id_eq, censorHorizon_eq_value] using hi
  have hm : MeasurableSet {o : ObsHistory | o.treatment = a ∧ t ≤ o.exit} :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurable_obsHistory_exit measurableSet_Ici)
  have he : observe ⁻¹' {o : ObsHistory | o.treatment = a ∧ t ≤ o.exit} =
      LatentSubject.treatment ⁻¹' ({a} : Set Arm) ∩
      (fun z : LatentSubject => min (z.death a) (censorHorizon z a)) ⁻¹' Ici t := by
    ext z
    change (z.treatment = a ∧ t ≤ min (z.death z.treatment)
      (censorHorizon z z.treatment)) ↔ _
    by_cases ha : z.treatment = a <;> simp [ha]
  rw [observedLaw, measureReal_def, Measure.map_apply measurable_observe hm, he,
    hind.measure_inter_preimage_eq_mul ({a} : Set Arm) (Ici t)
      (MeasurableSet.singleton a) measurableSet_Ici, ENNReal.toReal_mul]
  change P.latent.real {z | z.treatment = a} *
    P.latent.real {z | t ≤ min (z.death a) (censorHorizon z a)} = _
  rw [hP.assignmentLaw a,
    exitTail_eq_survival_mul_retention P hP.deathHazard hP.independentCensoring a t ht]
  ring

-- @node: riskSet_zero_probability
lemma riskSet_zero_probability (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (sampleLaw P n).real {s | riskSet a s t = 0} =
      (1 - P.p a * survival P a t * retention P a t) ^ n := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let E : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hm : MeasurableSet E :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurable_obsHistory_exit measurableSet_Ici)
  have he : {s : Fin n → ObsHistory | riskSet a s t = 0} =
      Set.pi Set.univ (fun _ => Eᶜ) := by
    ext s
    simp [riskSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff, E, Set.mem_pi]
  rw [he, sampleLaw, measureReal_def, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [← measureReal_def, probReal_compl_eq_one_sub hm]
  rw [observed_arm_risk_probability P hP a ht]

-- @node: riskSet_zero_probability_le_exp
lemma riskSet_zero_probability_le_exp (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (sampleLaw P n).real {s | riskSet a s t = 0} ≤
      Real.exp (-(n * (P.p a * survival P a t * retention P a t))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hq : P.p a * survival P a t * retention P a t ≤ 1 := by
    rw [← observed_arm_risk_probability P hP a ht]
    exact measureReal_le_one
  rw [riskSet_zero_probability P hP a n ht]
  calc
    _ ≤ (Real.exp (-(P.p a * survival P a t * retention P a t))) ^ n :=
      pow_le_pow_left₀ (by linarith)
        (by linarith [Real.add_one_le_exp (-(P.p a * survival P a t * retention P a t))]) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorIntegrability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance

/-!
# Subcritical ordinary death risk

Roadmap (5), (6), (8), and (19): retain inverse risk in the death
quadratic energy and integrate its binomial bound through the full horizon.
Subcritical retention gives a finite C/n second moment and consistency of
the actual ordinary death error, with no independence factorization.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open Causalean.Stat.RecurrentEvent.CountingProcess (Sample inverseRisk inverseRisk_jointMeasurable)

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Time-averaged reference death inverse risk has a subcritical full-horizon bound. -/
-- @node: subcritical_integral_expected_deathInverseRisk_le
lemma subcritical_integral_expected_deathInverseRisk_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ t in Ioo (0 : ℝ) 1, ∫ s : Sample n,
      inverseRisk t s ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      (2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)) *
        ∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹ := by
  let : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  let : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  let : IsProbabilityMeasure (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  let ν := volume.restrict (Ioo (0 : ℝ) 1)
  let r := fun t => ∫ s : Sample n, inverseRisk t s ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let C := 2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrMeas : Measurable r :=
    (inverseRisk_jointMeasurable.comp measurable_swap).stronglyMeasurable.integral_prod_left'.measurable
  have hrBound (t : ℝ) : |r t| ≤ 1 := by
    have hi : Integrable (fun s : Sample n => inverseRisk t s) (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
      apply Integrable.of_bound
        ((inverseRisk_jointMeasurable.comp measurable_swap).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
      filter_upwards [] with s
      change |inverseRisk t s| ≤ 1
      rw [abs_of_nonneg (pairInverseRisk_mem_Icc t s).1]
      exact (pairInverseRisk_mem_Icc t s).2
    rw [abs_of_nonneg (integral_nonneg (fun s => (pairInverseRisk_mem_Icc t s).1))]
    simpa using integral_mono hi (integrable_const 1)
      (fun s => (pairInverseRisk_mem_Icc t s).2)
  have hrInt : Integrable r ν := Integrable.of_bound hrMeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hrBound t))
  have hretInt : Integrable (fun t => (retention P a t)⁻¹) ν := by
    have hi := inv_retention_intervalIntegrable_subcritical c P hP hk a
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
    exact hi.mono_set Ioo_subset_Icc_self
  have hpoint : ∀ᵐ t ∂ν, r t ≤ C * (retention P a t)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht1 : t < 1 := ht.2
    have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
    have hr : 0 < retention P a t :=
      retention_pos_of_modelClass c P hP a t ht.1.le ht1
    have hs : 0 < survival P a t := Real.exp_pos _
    have hsurv := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨ht.1.le, ht1.le⟩).1
    calc
      r t ≤ 2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t)) :=
        DeathCP.integral_inverseRisk_le_arm_tail c P hP a hn ht.1 ht1
      _ ≤ 2 / ((n : ℝ) * (c.pMin * retention P a t * Real.exp (-c.dMax))) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hnR (mul_pos (mul_pos c.pMin_pos hr) (Real.exp_pos _)))
        gcongr
        exact hP.treatmentOverlap a
      _ = C * (retention P a t)⁻¹ := by
        dsimp [C]
        rw [Real.exp_neg]
        field_simp
  calc
    _ ≤ ∫ t, C * (retention P a t)⁻¹ ∂ν :=
      integral_mono_ae hrInt (hretInt.const_mul C) hpoint
    _ = _ := by rw [integral_const_mul]

/-- Compact target-weight bounds and subcritical inverse retention give a
single finite full-horizon second-moment constant for every sample size. -/
-- @node: subcritical_deathError_zero_secondMoment_le
lemma subcritical_deathError_zero_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (∫ s : Fin n → ObsHistory, deathError c P a s 0 ^ 2 ∂sampleLaw P n) ≤ C / n := by
  obtain ⟨K, hK, hbound⟩ := DeathCP.exists_deathTargetWeight_bound c P hP a
    (h := 0) (by norm_num) (by norm_num)
  let B := K ^ 2 * c.dMax
  let R := ∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹
  refine ⟨B * (2 * Real.exp c.dMax / c.pMin) * R, ?_, ?_⟩
  · have hd : 0 ≤ c.dMax := c.dMin_pos.le.trans c.dMin_lt.le
    have hR : 0 ≤ R := integral_nonneg (fun t => inv_nonneg.mpr measureReal_nonneg)
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg K) hd)
      (div_nonneg (by positivity) c.pMin_pos.le)) hR
  · intro n hn
    let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)
    let ν := volume.restrict (Ioo (0 : ℝ) 1)
    let r := fun t => ∫ x : Sample n, inverseRisk t x ∂μ
    let : IsProbabilityMeasure (armDeathFailureLaw P a) :=
      ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
    let : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
    let : IsProbabilityMeasure μ := by
      unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
      infer_instance
    have hrM : Measurable r :=
      (inverseRisk_jointMeasurable.comp measurable_swap).stronglyMeasurable.integral_prod_left'.measurable
    have hr0 (t : ℝ) : 0 ≤ r t :=
      integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1)
    have hr1 (t : ℝ) : r t ≤ 1 := by
      have hi : Integrable (fun x : Sample n => inverseRisk t x) μ := by
        apply Integrable.of_bound
          (inverseRisk_jointMeasurable.comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
        filter_upwards [] with x
        change |inverseRisk t x| ≤ 1
        rw [ abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
        exact (pairInverseRisk_mem_Icc t x).2
      simpa using integral_mono hi (integrable_const 1)
        (fun x => (pairInverseRisk_mem_Icc t x).2)
    have hrI : Integrable r ν := Integrable.of_bound hrM.aestronglyMeasurable 1 (by
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 t)]
      exact hr1 t)
    have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans c.dMin_lt.le)
    have he := DeathCP.deathError_secondMoment_le_expectedInverseRiskEnergy
      c P hP a n (h := 0) (by norm_num) (by norm_num)
    simp only [sub_zero, integral_Icc_eq_integral_Ioo] at he
    calc
      _ ≤ ∫ t, deathTargetWeight c P a 0 t ^ 2 * P.hazard a t * r t ∂ν := he
      _ ≤ ∫ t, B * r t ∂ν := by
        apply integral_mono_of_nonneg
          (show ∀ᵐ t ∂ν, 0 ≤ deathTargetWeight c P a 0 t ^ 2 * P.hazard a t * r t from by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (mul_nonneg (sq_nonneg _)
              (c.dMin_pos.le.trans (hP.deathBounds a t ⟨ht.1.le, ht.2.le⟩).1)) (hr0 t))
          (hrI.const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        apply mul_le_mul_of_nonneg_right _ (hr0 t)
        have hw : deathTargetWeight c P a 0 t ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) hK).2 (hbound t ⟨ht.1.le, by simpa using ht.2.le⟩)
        exact mul_le_mul hw (hP.deathBounds a t ⟨ht.1.le, ht.2.le⟩).2
          (c.dMin_pos.le.trans (hP.deathBounds a t ⟨ht.1.le, ht.2.le⟩).1) (sq_nonneg _)
      _ = B * ∫ t, r t ∂ν := integral_const_mul _ _
      _ ≤ B * ((2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)) * R) :=
        mul_le_mul_of_nonneg_left
          (subcritical_integral_expected_deathInverseRisk_le c P hP hk a hn) hB
      _ = _ := by ring

/-- Chebyshev converts the full-horizon death energy into a C/(n ε²)
probability bound with one constant for the fixed model law. -/
-- @node: subcritical_deathError_zero_probability_le
lemma subcritical_deathError_zero_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε →
      (sampleLaw P n).real {s | ε < |deathError c P a s 0|} ≤
        C / ((n : ℝ) * ε ^ 2) := by
  obtain ⟨C, hC, hb⟩ := subcritical_deathError_zero_secondMoment_le c P hP hk a
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := deathError_sq_integrable c P hP a n (h := 0) (by norm_num) (by norm_num)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (deathError c P a s 0))) hi (ε ^ 2)
  have hsub : {s : Fin n → ObsHistory | ε < |deathError c P a s 0|} ⊆
      {s | ε ^ 2 ≤ deathError c P a s 0 ^ 2} := by
    intro s hs
    change ε < |deathError c P a s 0| at hs
    change ε ^ 2 ≤ deathError c P a s 0 ^ 2
    nlinarith [sq_abs (deathError c P a s 0)]
  have h := ((mul_le_mul_of_nonneg_left
    (measureReal_mono hsub (by finiteness)) (sq_nonneg ε)).trans hm).trans (hb n hn)
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm] using h

/-- The actual ordinary death error converges to zero in probability. -/
-- @node: subcritical_deathError_zero_probability_tendsto_zero
lemma subcritical_deathError_zero_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |deathError c P a s 0|}) atTop (nhds 0) := by
  obtain ⟨C, _, hb⟩ := subcritical_deathError_zero_probability_le c P hP hk a
  have hlim : Tendsto (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) atTop (nhds 0) := by
    simp only [div_mul_eq_div_div]
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C).div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hb n (by omega) ε hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceFullHorizonEnergy

/-!
# Subcritical ordinary recurrence risk

Roadmap (5), (6), (8), and (19): the full-horizon recurrence error has an
inverse-sample-size second moment under integrable endpoint retention.
The inverse retention integral is derived from the model class. Markov's
inequality gives actual recurrence-error consistency, without any fitted-risk
or independence premise.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Time-averaged observed inverse risk has a subcritical full-horizon bound. -/
-- @node: subcritical_integral_expected_invRisk_le
lemma subcritical_integral_expected_invRisk_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ t in Ioo (0 : ℝ) 1, ∫ s : Fin n → ObsHistory,
      invRisk a s t ∂sampleLaw P n) ≤
      (2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)) *
        ∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹ := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let ν := volume.restrict (Ioo (0 : ℝ) 1)
  let r := fun t => ∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n
  let C := 2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrMeas : Measurable r :=
    (measurable_recurrenceInvRisk_joint a).stronglyMeasurable.integral_prod_left'.measurable
  have hrBound (t : ℝ) : |r t| ≤ 1 := by
    have hi : Integrable (fun s : Fin n → ObsHistory => invRisk a s t) (sampleLaw P n) := by
      apply Integrable.of_bound
        ((measurable_recurrenceInvRisk_joint a).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
      filter_upwards [] with s
      change |invRisk a s t| ≤ 1
      rw [abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
      exact (recurrence_invRisk_mem_Icc a s t).2
    rw [abs_of_nonneg (integral_nonneg (fun s => (recurrence_invRisk_mem_Icc a s t).1))]
    simpa using integral_mono hi (integrable_const 1)
      (fun s => (recurrence_invRisk_mem_Icc a s t).2)
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
        recurrence_integral_invRisk_le_arm_tail c P hP a hn ht.1 ht1
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

/-- The ordinary recurrence martingale has an explicit full-horizon C/n
second-moment bound. All random coefficient dependence stays inside energy. -/
-- @node: subcritical_recurrenceError_zero_secondMoment_le
lemma subcritical_recurrenceError_zero_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      (2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
        (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)) / n := by
  have he := recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg
    c P hP a n (h := 0) (by norm_num) (by norm_num)
  rw [sub_zero, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at he
  have hK : 0 ≤ weightEnvelope c ^ 2 * c.lambdaMax :=
    mul_nonneg (sq_nonneg _) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  have hb := mul_le_mul_of_nonneg_left
    (subcritical_integral_expected_invRisk_le c P hP hk a hn) hK
  exact he.trans (hb.trans_eq (by ring))

/-- Chebyshev's inequality applied to the actual ordinary recurrence score. -/
-- @node: subcritical_recurrenceError_zero_probability_le
lemma subcritical_recurrenceError_zero_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    (sampleLaw P n).real {s : Fin n → ObsHistory |
      ε < |recurrenceError c P a s 0|} ≤
      (2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
        (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)) / ((n : ℝ) * ε ^ 2) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := (recurrenceError_secondMoment_eq_exposure_energy_of_nonneg
    c P hP a n (h := 0) (by norm_num) (by norm_num)).1
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (recurrenceError c P a s 0))) hi (ε ^ 2)
  have hsub : {s : Fin n → ObsHistory | ε < |recurrenceError c P a s 0|} ⊆
      {s | ε ^ 2 ≤ recurrenceError c P a s 0 ^ 2} := by
    intro s hs
    change ε < |recurrenceError c P a s 0| at hs
    change ε ^ 2 ≤ recurrenceError c P a s 0 ^ 2
    nlinarith [sq_abs (recurrenceError c P a s 0)]
  have hb := ((mul_le_mul_of_nonneg_left
    (measureReal_mono hsub (by finiteness)) (sq_nonneg ε)).trans hm).trans
      (subcritical_recurrenceError_zero_secondMoment_le c P hP hk a hn)
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm] using hb

/-- The ordinary empirical recurrence error vanishes in probability. -/
-- @node: subcritical_recurrenceError_zero_probability_tendsto_zero
lemma subcritical_recurrenceError_zero_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |recurrenceError c P a s 0|}) atTop (nhds 0) := by
  let C := 2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
    (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)
  have hlim : Tendsto (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) atTop (nhds 0) := by
    simp only [div_mul_eq_div_div]
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul C).div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact subcritical_recurrenceError_zero_probability_le c P hP hk a (by omega) hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

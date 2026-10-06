module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonKMConsistency

/-!
# Remaining-mean compensator consistency

Roadmap (35)--(36): the recurrence compensator converges on every remaining
study window. Integrated KM consistency and vanishing empty-risk probabilities
control the drift without independence or a positive endpoint retention bound.
The stochastic recurrence remainder is a separate proof obligation.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Vanishing second moments imply vanishing first absolute moments under
probability laws, by the elementary Young inequality. -/
-- @node: absolute_moment_tendsto_zero_of_secondMoment
lemma absolute_moment_tendsto_zero_of_secondMoment
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ)
    (hX : ∀ n, Integrable (X n) (μ n))
    (hX2 : ∀ n, Integrable (fun x => X n x ^ 2) (μ n))
    (hlim : Tendsto (fun n => ∫ x, X n x ^ 2 ∂μ n) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, |X n x| ∂μ n) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le (integral_nonneg (fun _ => abs_nonneg _)))
  · intro ε hε
    have hδ : 0 < ε / 2 := half_pos hε
    have hsmall := (hlim.div_const (ε / 2)).eventually
      (gt_mem_nhds (show (0 : ℝ) / (ε / 2) < ε / 2 by simpa using hδ))
    filter_upwards [hsmall] with n hn
    have hpoint (x : Ω n) : |X n x| ≤ ε / 2 + X n x ^ 2 / (ε / 2) := by
      apply (mul_le_mul_iff_of_pos_left hδ).mp
      rw [mul_add, mul_div_cancel₀ _ hδ.ne']
      nlinarith [sq_nonneg (|X n x| - ε / 2), sq_abs (X n x)]
    have hb := integral_mono (hX n).abs ((integrable_const (ε / 2)).add
      ((hX2 n).div_const (ε / 2))) hpoint
    simp only [Pi.add_apply] at hb
    rw [integral_add (integrable_const _) ((hX2 n).div_const _), integral_const,
      integral_div] at hb
    simp at hb
    linarith

/-- The actual KM left-limit error vanishes in first mean at strict horizons. -/
-- @node: observed_KM_error_absoluteMoment_tendsto_zero
lemma observed_KM_error_absoluteMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |deathKMLeft a s t - survival P a t| ∂sampleLaw P n) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hm (n : ℕ) : Measurable (fun s : Fin n → ObsHistory =>
      deathKMLeft a s t - survival P a t) := by fun_prop
  have hb (n : ℕ) (s : Fin n → ObsHistory) :
      |deathKMLeft a s t - survival P a t| ≤ 1 := by
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    rw [abs_le]
    constructor <;> linarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  apply absolute_moment_tendsto_zero_of_secondMoment (fun n => sampleLaw P n)
    (fun _ s => deathKMLeft a s t - survival P a t)
    (fun n => Integrable.of_bound (hm n).aestronglyMeasurable 1
      (Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hb n s)))
    (fun n => Integrable.of_bound ((hm n).pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        nlinarith [hb n s, abs_nonneg (deathKMLeft a s t - survival P a t),
          sq_abs (deathKMLeft a s t - survival P a t)])))
    (observed_KM_error_secondMoment_tendsto_zero c P hP a ht0 ht1)

/-- Multiplying the KM drift by the totalized risk cancellation adds only
an empty-risk indicator to its absolute error. -/
-- @node: recurrence_drift_error_abs_le_KM_add_emptyRisk
lemma recurrence_drift_error_abs_le_KM_add_emptyRisk
    (P : SubjectLaw) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ)
    (hS : survival P a t ≤ 1) :
    |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t| ≤
      |deathKMLeft a s t - survival P a t| +
        (if riskSet a s t = 0 then 1 else 0) := by
  by_cases hr : riskSet a s t = 0
  · simp only [invRisk, hr, if_pos, mul_zero, zero_sub, abs_neg]
    rw [abs_of_pos (show 0 < survival P a t from Real.exp_pos _)]
    linarith [abs_nonneg (deathKMLeft a s t - survival P a t)]
  · have hrR : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
    simp [invRisk, hr, hrR]

/-- The drift error is bounded by one throughout the study window. -/
-- @node: recurrence_drift_error_abs_le_one
lemma recurrence_drift_error_abs_le_one
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t| ≤ 1 := by
  have hk := deathKMLeft_mem_Icc a s t
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht
  by_cases hr : riskSet a s t = 0
  · simp only [invRisk, hr, if_pos, mul_zero, zero_sub, abs_neg]
    rw [abs_of_pos (show 0 < survival P a t from Real.exp_pos _)]
    exact hs.2
  · have hrR : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
    simp only [invRisk, if_neg hr, mul_inv_cancel₀ hrR, mul_one]
    rw [abs_le]
    constructor <;> linarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]

/-- The empirical recurrence drift converges in first mean at every strict
time. The empty-risk contribution is controlled under the actual sample law. -/
-- @node: observed_recurrence_drift_error_absoluteMoment_tendsto_zero
lemma observed_recurrence_drift_error_absoluteMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t|
      ∂sampleLaw P n) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (observed_KM_error_absoluteMoment_tendsto_zero c P hP a ht0 ht1).add
    (observed_strictHorizon_emptyRisk_probability_tendsto_zero c P hP a ht0 ht1)
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _
    (by simpa only [add_zero] using hlim)
  intro n
  let Z : Set (Fin n → ObsHistory) := {s | riskSet a s t = 0}
  have hZ : MeasurableSet Z := by
    exact measurableSet_eq_fun ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const
  have hi : Integrable (fun s : Fin n → ObsHistory => |deathKMLeft a s t - survival P a t|)
      (sampleLaw P n) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    constructor <;> linarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  have hZi := (integrable_const (1 : ℝ) (μ := sampleLaw P n)).indicator hZ
  calc
    _ ≤ ∫ s, |deathKMLeft a s t - survival P a t| + Z.indicator (fun _ => (1 : ℝ)) s
        ∂sampleLaw P n := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hi.add hZi)
      (Eventually.of_forall (fun s => by
        simpa [Z, Set.indicator] using recurrence_drift_error_abs_le_KM_add_emptyRisk
          P a s t (survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩).2))
    _ = _ := by
      rw [integral_add hi hZi, integral_indicator hZ]
      simp [Z, integral_const, measureReal_def]

/-- Bounded drift errors are integrable on the sample-by-time space, even
when the endpoint risk probability is zero. -/
-- @node: observed_recurrence_drift_error_integrable_prod
lemma observed_recurrence_drift_error_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      |deathKMLeft a p.1 p.2 * ((riskSet a p.1 p.2 : ℝ) * invRisk a p.1 p.2) -
        survival P a p.2|)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      |deathKMLeft a p.1 p.2 * ((riskSet a p.1 p.2 : ℝ) * invRisk a p.1 p.2) - g p.2|) := by
    fun_prop
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1)), p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      |deathKMLeft a p.1 p.2 * ((riskSet a p.1 p.2 : ℝ) * invRisk a p.1 p.2) - g p.2|)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [htprod] with p hp
    simp only [g, Set.piecewise, if_pos hp, Real.norm_eq_abs, abs_abs]
    exact recurrence_drift_error_abs_le_one c P hP a p.1 hp
  apply hi.congr
  filter_upwards [htprod] with p hp
  simp only [g, Set.piecewise, if_pos hp]

/-- The expected full-window absolute drift error vanishes. Fubini and
dominated convergence retain all dependence between KM and risk. -/
-- @node: observed_recurrence_drift_integrated_absoluteMoment_tendsto_zero
lemma observed_recurrence_drift_integrated_absoluteMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1,
        |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t|)
      ∂sampleLaw P n) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hi (n : ℕ) := observed_recurrence_drift_error_integrable_prod c P hP a n
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := fun n t => ∫ s : Fin n → ObsHistory,
      |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t|
      ∂sampleLaw P n)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => (hi n).integral_prod_right.aestronglyMeasurable) (integrable_const 1)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Icc, (hi n).prod_left_ae] with t ht hit
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
      calc
        _ ≤ ∫ _s : Fin n → ObsHistory, (1 : ℝ) ∂sampleLaw P n :=
          integral_mono hit (integrable_const 1)
            (fun s => recurrence_drift_error_abs_le_one c P hP a s ht)
        _ = 1 := by simp)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc (0 : ℝ) 1)).ae_ne (1 : ℝ)] with t ht htne
      exact observed_recurrence_drift_error_absoluteMoment_tendsto_zero c P hP a ht.1
        (lt_of_le_of_ne ht.2 htne))
  simp only [integral_zero] at h
  convert h using 1
  funext n
  exact integral_integral_swap (hi n)

/-- The integrated absolute drift error is itself integrable under the
observed iid sample law. -/
-- @node: observed_recurrence_drift_integrated_error_integrable
lemma observed_recurrence_drift_integrated_error_integrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    Integrable (fun s : Fin n → ObsHistory => ∫ t in Icc (0 : ℝ) 1,
      |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t|)
      (sampleLaw P n) :=
  (observed_recurrence_drift_error_integrable_prod c P hP a n).integral_prod_left

/-- The drift limit holds uniformly for integration over any subwindow:
the full-window absolute error bounds every recurrence compensator error. -/
-- @node: remainingMean_compensator_error_le_integrated_drift
lemma remainingMean_compensator_error_le_integrated_drift
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |(∫ t in u..1, deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) *
        P.lam a t) - remainingTarget c P a 0 u| ≤
      c.lambdaMax * ∫ t in Icc (0 : ℝ) 1,
        |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t| := by
  let D := fun t => deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t)
  have hmD : Measurable D := by
    dsimp [D]
    fun_prop
  have hD (t : ℝ) : D t ∈ Icc (0 : ℝ) 1 := by
    by_cases hr : riskSet a s t = 0
    · simp [D, invRisk, hr]
    · have hrR : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
      simpa [D, invRisk, hr, hrR] using deathKMLeft_mem_Icc a s t
  have hiD : IntervalIntegrable (fun t => D t * P.lam a t) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
    apply Integrable.of_bound (hmD.aestronglyMeasurable.mul
      ((hP.recurrenceHolder a).1.continuousOn.aestronglyMeasurable measurableSet_Icc)) c.lambdaMax
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD t).1,
      abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
    exact (mul_le_mul_of_nonneg_right (hD t).2
      (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)).trans
      (by simpa using (hP.recurrenceBounds a t ht).2)
  have hiS := modelClass_target_intervalIntegrable c P hP a
  have hiE : IntegrableOn (fun t => |D t - survival P a t|) (Icc (0 : ℝ) 1) := by
    have hmE : AEStronglyMeasurable (fun t => |D t - survival P a t|)
        (volume.restrict (Icc (0 : ℝ) 1)) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (hmD.aestronglyMeasurable.sub
          ((modelClass_survival_continuousOn c P hP a).aestronglyMeasurable
            measurableSet_Icc)).norm
    apply Integrable.of_bound hmE 1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs, abs_abs, D] using recurrence_drift_error_abs_le_one c P hP a s ht
  have hsub : uIcc u 1 ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hu.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hu.1 le_rfl
  simp only [remainingTarget, continuationWeight, if_true, sub_zero, one_mul]
  rw [← intervalIntegral.integral_sub (hiD.mono_set hsub) (hiS.mono_set hsub),
    intervalIntegral.integral_of_le hu.2, ← integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Icc u 1, |D t * P.lam a t - survival P a t * P.lam a t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Icc u 1, c.lambdaMax * |D t - survival P a t| := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
        ((hiE.mono_set (Icc_subset_Icc hu.1 le_rfl)).const_mul _) 
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [← sub_mul, abs_mul,
        abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ⟨hu.1.trans ht.1, ht.2⟩).1)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (hP.recurrenceBounds a t ⟨hu.1.trans ht.1, ht.2⟩).2 (abs_nonneg (D t - survival P a t))
    _ ≤ ∫ t in Icc (0 : ℝ) 1, c.lambdaMax * |D t - survival P a t| :=
      setIntegral_mono_set ((hiE.const_mul _))
        (Eventually.of_forall (fun _ => mul_nonneg
          (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) (abs_nonneg _)))
        (Filter.Eventually.of_forall (Icc_subset_Icc hu.1 le_rfl))
    _ = _ := by rw [integral_const_mul]

/-- Remaining-mean compensators converge uniformly in their lower endpoint
in probability, by Markov applied to the full-window absolute drift error. -/
-- @node: remainingMean_compensator_uniform_probability_tendsto_zero
lemma remainingMean_compensator_uniform_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ∃ u ∈ Icc (0 : ℝ) 1,
        ε < |(∫ t in u..1, deathKMLeft a s t *
          ((riskSet a s t : ℝ) * invRisk a s t) * P.lam a t) -
          remainingTarget c P a 0 u|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let E := fun (n : ℕ) (s : Fin n → ObsHistory) => ∫ t in Icc (0 : ℝ) 1,
    |deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) - survival P a t|
  have hL : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hδ : 0 < ε / c.lambdaMax := div_pos hε hL
  have hlim := (observed_recurrence_drift_integrated_absoluteMoment_tendsto_zero
    c P hP a).div_const (ε / c.lambdaMax)
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using hlim)
  intro n
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      integral_nonneg (fun _ => abs_nonneg _)))
    (observed_recurrence_drift_integrated_error_integrable c P hP a n)
    (ε / c.lambdaMax)
  apply (le_div_iff₀ hδ).2
  rw [mul_comm]
  apply (mul_le_mul_of_nonneg_left (measureReal_mono (show
      {s : Fin n → ObsHistory | ∃ u ∈ Icc (0 : ℝ) 1,
        ε < |(∫ t in u..1, deathKMLeft a s t *
          ((riskSet a s t : ℝ) * invRisk a s t) * P.lam a t) -
          remainingTarget c P a 0 u|} ⊆ {s | ε / c.lambdaMax ≤ E n s} from ?_)
      (by finiteness)) hδ.le).trans hmarkov
  intro s hs
  obtain ⟨u, hu, herr⟩ := hs
  have hb := remainingMean_compensator_error_le_integrated_drift c P hP a s hu
  exact ((div_le_iff₀ hL).2 (by simpa only [E, mul_comm] using (herr.trans_le hb).le))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

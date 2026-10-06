module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonDeathVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.InverseRiskCompensatorIntegral
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonDeathPlugin

public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalAsymptoticLinearity

/-! # Death optional-variation consistency

Roadmap (39)--(41): deterministic strict-horizon compensation, followed by
terminal localization using the remaining-horizon envelope. No future marks
are treated as predictable.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Restricting the time integral preserves the full-horizon inverse-risk
mean error bound. -/
-- @node: subcritical_partial_inverseRisk_compensator_mean_abs_tendsto_zero
lemma subcritical_partial_inverseRisk_compensator_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {T : ℝ} (hT : T ≤ 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(∫ t in Ioo (0 : ℝ) T, f t * ((n : ℝ) * invRisk a s t)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) T,
          (f t / survival P a t) / retention P a t| ∂sampleLaw P n)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hsub : Ioo (0 : ℝ) T ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨ht.1, ht.2.trans_le hT⟩
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _
    (subcritical_inverseRisk_integrated_density_mean_tendsto_zero c P hP hk a f hf hc)
  intro n
  have he := subcritical_inverseRisk_compensator_integrable_prod c P hP a n f hf hc
  have hd := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => f t / survival P a t)
    (hc.div (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne'))).const_mul (P.p a)⁻¹
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hd
  have hi := (subcritical_inverseRisk_centered_density_integrable_prod
    c P hP hk a n f hf hc).norm.integral_prod_left
  simp only [Real.norm_eq_abs] at hi
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) hi
  filter_upwards [he.prod_right_ae,
    (subcritical_inverseRisk_centered_density_integrable_prod c P hP hk a n f hf hc).prod_right_ae]
    with s hs hs'
  rw [← integral_const_mul, ← integral_sub (hs.mono_measure (Measure.restrict_mono hsub le_rfl)) (hd.mono_set hsub)]
  calc
    _ = |∫ t in Ioo (0 : ℝ) T, f t * ((n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t))| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ∫ t in Ioo (0 : ℝ) T, |f t * ((n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t))| := abs_integral_le_integral_abs
    _ ≤ _ := setIntegral_mono_set hs'.abs
      (Eventually.of_forall (fun _ => abs_nonneg _)) (Eventually.of_forall hsub)

/-- Markov's inequality applies to the restricted compensator as well. -/
-- @node: subcritical_partial_inverseRisk_compensator_probability_tendsto_zero
lemma subcritical_partial_inverseRisk_compensator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) {T ε : ℝ} (hT : T ≤ 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(∫ t in Ioo (0 : ℝ) T, f t * ((n : ℝ) * invRisk a s t)) -
        (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) T,
          (f t / survival P a t) / retention P a t|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    |(∫ t in Ioo (0 : ℝ) T, f t * ((n : ℝ) * invRisk a s t)) -
      (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) T, (f t / survival P a t) / retention P a t|
  have ht := (subcritical_partial_inverseRisk_compensator_mean_abs_tendsto_zero
    c P hP hk a f hf hc hT).div_const ε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa only [zero_div] using ht)
  intro n
  have he := (subcritical_inverseRisk_compensator_integrable_prod c P hP a n f hf hc).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono
      (show Ioo (0 : ℝ) T ⊆ Ioo (0 : ℝ) 1 from fun t ht => ⟨ht.1, ht.2.trans_le hT⟩) le_rfl))
  have hFi : Integrable (F n) (sampleLaw P n) :=
    (he.integral_prod_left.sub (integrable_const _)).abs
  have hb := mul_meas_ge_le_integral_of_nonneg
    (f := F n) (Eventually.of_forall (fun _ => abs_nonneg _)) hFi ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => hs.le) (by finiteness)
  change (sampleLaw P n).real {s | ε < F n s} ≤ (∫ s, F n s ∂sampleLaw P n) / ε
  apply (le_div_iff₀ hε).2
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans (by rw [mul_comm]; exact hb)

/-- On every strict horizon, the actual deterministic death variation
converges to its stated oracle integral (39). -/
-- @node: subcritical_localizedDeathVariation_probability_tendsto_limit
lemma subcritical_localizedDeathVariation_probability_tendsto_limit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {T ε : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingTarget c P a 0) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..T,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)|}) atTop (nhds 0) := by
  classical
  let f := fun t => remainingTarget c P a 0 t ^ 2 * P.hazard a t
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    ((continuousOn_remainingTarget_zero c P hP a).pow 2).mul
      (hP.deathHolder a).1.continuousOn
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hA (n : ℕ) (s : Fin n → ObsHistory) :
      (∫ t in Ioo (0 : ℝ) T, g t * ((n : ℝ) * invRisk a s t)) =
        (n : ℝ) * ∫ t in Ioc (0 : ℝ) T,
          remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t := by
    rw [integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le.trans hT1.le⟩]
    dsimp [f]
    ring
  have hV : (∫ t in Ioo (0 : ℝ) T, (g t / survival P a t) / retention P a t) =
      ∫ t in (0 : ℝ)..T, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
        (survival P a t * retention P a t) := by
    rw [intervalIntegral.integral_of_le hT0, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [he t ⟨ht.1.le, ht.2.le.trans hT1.le⟩]
    simp only [f, div_div]
  let C := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    (n : ℝ) * ∫ t in Ioc (0 : ℝ) T,
      remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t
  let V := (P.p a)⁻¹ * ∫ t in (0 : ℝ)..T,
    remainingTarget c P a 0 t ^ 2 * P.hazard a t / (survival P a t * retention P a t)
  have hconv (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n : ℕ => (sampleLaw P n).real {s | δ < |V - C n s|})
        atTop (nhds 0) := by
    simpa only [hA, hV, abs_sub_comm] using
      subcritical_partial_inverseRisk_compensator_probability_tendsto_zero
        c P hP hk a g hg (hc.congr he) hT1.le hδ
  have ht := sampleLaw_negligible_sub P
    (fun n s => localizedDeathVariation a s T (remainingTarget c P a 0) - C n s)
    (fun n s => V - C n s)
    (fun δ hδ => ordinaryFixedDeathVariationRemainder_probability_tendsto_zero
      c P hP a hT0 hT1 hδ) hconv hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [mem_setOf_eq]
  have heq : localizedDeathVariation a s T (remainingTarget c P a 0) - C n s -
      (V - C n s) = localizedDeathVariation a s T (remainingTarget c P a 0) - V := by ring
  rw [heq]

/-- The remaining target is bounded by the same deterministic terminal
coefficient as the plug-in marks. -/
-- @node: tailDeathVariation_remainingTarget_le_envelope
lemma tailDeathVariation_remainingTarget_le_envelope
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) {T : ℝ} (hT : 0 ≤ T) :
    tailDeathVariation a s T 1 (remainingTarget c P a 0) ≤
      tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)) := by
  classical
  unfold tailDeathVariation
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have hh := remainingTarget_zero_mem_Icc c P hP a
      (show (s i).exit ∈ Icc (0 : ℝ) 1 from ⟨hT.trans hi.2.2.1.le, hi.2.2.2⟩)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh.1 hh.2 2) (sq_nonneg _)
  · exact le_rfl

/-- Terminal localization closes the deterministic full-horizon death
optional-variation limit without a bounded endpoint oracle weight. -/
-- @node: subcritical_deathVariation_probability_tendsto_limit
lemma subcritical_deathVariation_probability_tendsto_limit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s 1 (remainingTarget c P a 0) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          remainingTarget c P a 0 t ^ 2 * P.hazard a t /
            (survival P a t * retention P a t)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let f := fun t => remainingTarget c P a 0 t ^ 2 * P.hazard a t /
    (survival P a t * retention P a t)
  have hε3 : 0 < ε / 3 := by positivity
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun _ => hl.trans_le measureReal_nonneg)
  · intro η hη
    have horacle := ((subcritical_death_oracle_tail_tendsto_zero c P hP hk a).abs).eventually
      (gt_mem_nhds (by simpa only [abs_zero] using hε3))
    have hterminal := tailDeathVariation_envelope_probability_uniform_small
      c P hP hk a hε3 (half_pos hη)
    obtain ⟨T, hT0, hT1, hsmall, htail⟩ := exists_strict_study_horizon_of_eventually
      (horacle.and hterminal)
    have hlocal := (subcritical_localizedDeathVariation_probability_tendsto_limit
      c P hP hk a hT0 hT1 hε3).eventually (gt_mem_nhds (half_pos hη))
    have hi := subcritical_death_energy_intervalIntegrable c P hP hk a
    have hleft : IntervalIntegrable f volume 0 T := hi.mono_set (by
      rw [uIcc_of_le hT0, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl hT1.le)
    have hright : IntervalIntegrable f volume T 1 := hi.mono_set (by
      rw [uIcc_of_le hT1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hT0 le_rfl)
    have hsplit : (P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, f t) =
        (P.p a)⁻¹ * (∫ t in (0 : ℝ)..T, f t) +
        (P.p a)⁻¹ * (∫ t in T..1, f t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, mul_add]
    filter_upwards [hlocal, eventually_ge_atTop 1] with n hn hn1
    have hs : {s : Fin n → ObsHistory |
        ε < |localizedDeathVariation a s 1 (remainingTarget c P a 0) -
          (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1, f t|} ⊆
        {s | ε / 3 < |localizedDeathVariation a s T (remainingTarget c P a 0) -
          (P.p a)⁻¹ * ∫ t in (0 : ℝ)..T, f t|} ∪
        {s | ε / 3 < tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))} := by
      intro s hs
      by_contra h
      simp only [mem_union, mem_setOf_eq, not_or, not_lt] at h
      rw [mem_setOf_eq, localizedDeathVariation_split a s hT1.le, hsplit] at hs
      have heq : localizedDeathVariation a s T (remainingTarget c P a 0) +
          tailDeathVariation a s T 1 (remainingTarget c P a 0) -
          ((P.p a)⁻¹ * (∫ t in (0 : ℝ)..T, f t) + (P.p a)⁻¹ * (∫ t in T..1, f t)) =
          (localizedDeathVariation a s T (remainingTarget c P a 0) -
            (P.p a)⁻¹ * (∫ t in (0 : ℝ)..T, f t)) +
          (tailDeathVariation a s T 1 (remainingTarget c P a 0) -
            (P.p a)⁻¹ * (∫ t in T..1, f t)) := by ring
      rw [heq] at hs
      have hab := abs_add_le
        (localizedDeathVariation a s T (remainingTarget c P a 0) -
          (P.p a)⁻¹ * (∫ t in (0 : ℝ)..T, f t))
        (tailDeathVariation a s T 1 (remainingTarget c P a 0) -
          (P.p a)⁻¹ * (∫ t in T..1, f t))
      have hsub := abs_sub (tailDeathVariation a s T 1 (remainingTarget c P a 0))
        ((P.p a)⁻¹ * (∫ t in T..1, f t))
      rw [abs_of_nonneg (tailDeathVariation_nonneg _ _ _ _ _)] at hsub
      have hb := tailDeathVariation_remainingTarget_le_envelope c P hP a s hT0
      change |(P.p a)⁻¹ * (∫ t in T..1, f t)| < ε / 3 at hsmall
      linarith
    exact ((measureReal_mono hs (by finiteness)).trans (measureReal_union_le _ _)).trans_lt
      (by linarith [htail n (show 0 < n by omega)])

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

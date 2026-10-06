module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanCompensator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanRecurrenceEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalRemainingMeanGrid

/-!
# Observed remaining-mean identification

Roadmap (35)--(37): identify the observed future-mark tail with its actual
latent compensated recurrence score and drift. The exposure-dependent energy
bound then applies without independence of KM coefficients and risk sets.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed remaining recurrence mean before projection. -/
-- @node: remainingMeanRaw
noncomputable def remainingMeanRaw (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (u : ℝ) : ℝ :=
  ∑ i : Fin n, if (s i).treatment = a then
    (((s i).recur.times.filter (fun t => u ≤ t ∧ t ≤ 1)).map
      (fun t => deathKMLeft a s t * invRisk a s t)).sum else 0

/-- The raw future-mark tail is jointly measurable. -/
-- @node: measurable_remainingMeanRaw_joint
@[fun_prop]
lemma measurable_remainingMeanRaw_joint (a : Arm) {n : ℕ} :
    Measurable (fun p : (Fin n → ObsHistory) × ℝ => remainingMeanRaw a p.1 p.2) :=
  measurable_remainingRecurrenceSum_joint a

/-- A lower cutoff in the event filter can instead be inserted in its weight. -/
-- @node: remaining_times_filter_weight
lemma remaining_times_filter_weight (m : Multiset ℝ) (u T : ℝ) (f : ℝ → ℝ) :
    ((m.filter (fun t => u ≤ t ∧ t ≤ T)).map f).sum =
      ((m.filter (fun t => t ≤ T)).map (fun t => if u ≤ t then f t else 0)).sum := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons t m ih =>
    by_cases hu : u ≤ t <;> by_cases ht : t ≤ T <;> simp [hu, ht, ih]

/-- Stable stopping preserves the actual two-sided remaining-interval score. -/
-- @node: remaining_stopped_weighted_sum
lemma remaining_stopped_weighted_sum (r : RecurConfig) (x u T : ℝ) (f : ℝ → ℝ) :
    (((r.stopAt x).times.filter (fun t => u ≤ t ∧ t ≤ T)).map f).sum =
      ∑ k : Fin r.1, if u ≤ (r.2 k).1 ∧ (r.2 k).1 ≤ T ∧ (r.2 k).1 ≤ x
        then f (r.2 k).1 else 0 := by
  classical
  rw [remaining_times_filter_weight, recurrence_stopped_weighted_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hu : u ≤ (r.2 k).1 <;> by_cases ht : (r.2 k).1 ≤ T <;>
    by_cases hx : (r.2 k).1 ≤ x <;> simp [hu, ht, hx]

/-- The raw observed tail is the corresponding latent exposure-weighted point sum. -/
-- @node: remainingMeanRaw_eq_latent_point_sum
lemma remainingMeanRaw_eq_latent_point_sum (c : ClassConstants) (a : Arm)
    {n : ℕ} (z : Fin n → LatentSubject) (u : ℝ) :
    remainingMeanRaw a (fun j => observe (z j)) u =
      ∑ i : Fin n, ∑ k : Fin ((z i).recur a).1,
        remainingRecurrenceWeight c a u
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          (((z i).recur a).2 k).1 := by
  classical
  unfold remainingMeanRaw remainingRecurrenceWeight
  simp_rw [← recurrenceSubjectWeight_eq_exposureHistory]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (z i).treatment = a
  · simp only [observe, hi, ↓reduceIte]
    rw [remaining_stopped_weighted_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [recurrenceSubjectWeight, observe, hi, ↓reduceIte, true_and,
      continuationWeight, if_true, one_mul]
    by_cases hu : u ≤ (((z i).recur a).2 k).1 <;>
      by_cases ht : (((z i).recur a).2 k).1 ≤ 1 <;>
      by_cases hx : (((z i).recur a).2 k).1 ≤ min ((z i).death a) (censorHorizon (z i) a)
      <;> simp [hu, ht, hx]
  · simp [observe, hi, recurrenceSubjectWeight]

/-- An intensity integral with two endpoint cutoffs is its remaining-window
Lebesgue integral; absolute continuity removes the lower-endpoint singleton. -/
-- @node: recurrenceIntensity_integral_remaining
lemma recurrenceIntensity_integral_remaining (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (f : ℝ → ℝ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    (∫ t, (if u ≤ t ∧ t ≤ 1 then f t else 0) ∂recurrenceIntensity P a) =
      ∫ t in u..1, f t * P.lam a t := by
  have heq : (fun t => if u ≤ t ∧ t ≤ 1 then f t else 0) =
      fun t => if t ≤ (1 : ℝ) then (if u ≤ t then f t else 0) else 0 := by
    funext t
    by_cases ht : t ≤ 1 <;> by_cases ht' : u ≤ t <;> simp [ht, ht']
  rw [heq, recurrenceIntensity_integral_truncated P hP a _ (by norm_num) le_rfl,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  have hind : (fun t => (if u ≤ t then f t else 0) * P.lam a t) =
      (Ici u).indicator (fun t => f t * P.lam a t) := by
    funext t
    simp only [indicator_apply, mem_Ici]
    split_ifs <;> simp
  rw [hind, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici u ∩ Icc (0 : ℝ) 1 = Icc u 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hut, _, ht1⟩; exact ⟨hut, ht1⟩
    · rintro ⟨hut, ht1⟩; exact ⟨hut, hu.1.trans hut, ht1⟩
  rw [hset, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.2]

/-- The actual zero-safe recurrence drift on a remaining interval. -/
-- @node: remainingMeanDrift
noncomputable def remainingMeanDrift (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (u : ℝ) : ℝ :=
  ∫ t in u..1, deathKMLeft a s t * ((riskSet a s t : ℝ) * invRisk a s t) * P.lam a t

/-- The remaining-window drift is measurable in the observed sample. -/
-- @node: measurable_remainingMeanDrift
@[fun_prop]
lemma measurable_remainingMeanDrift (P : SubjectLaw) (hP : PoissonRecurrence P)
    (a : Arm) {n : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Measurable (fun s : Fin n → ObsHistory => remainingMeanDrift P a s u) := by
  obtain ⟨g, hg, he⟩ := (hP a).1
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      deathKMLeft a p.1 p.2 * ((riskSet a p.1 p.2 : ℝ) * invRisk a p.1 p.2) *
        g p.2) := by fun_prop
  have hi := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc u 1))).measurable
  have heq : (fun s : Fin n → ObsHistory => remainingMeanDrift P a s u) =
      fun s => ∫ t in Ioc u 1, deathKMLeft a s t *
        ((riskSet a s t : ℝ) * invRisk a s t) * g t := by
    funext s
    unfold remainingMeanDrift
    rw [intervalIntegral.integral_of_le hu.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hu.1 le_rfl) he] with t ht
    rw [ht]
  rw [heq]
  exact hi

/-- Summing subject compensators gives the actual remaining-window drift. -/
-- @node: remainingMeanDrift_eq_subject_integrals
lemma remainingMeanDrift_eq_subject_integrals (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (∑ i : Fin n, ∫ t in u..1, recurrenceSubjectWeight c 0 a s i t * P.lam a t) =
      remainingMeanDrift P a s u := by
  have hsub : uIcc u 1 ⊆ uIcc (0 : ℝ) 1 := by
    simp only [sub_zero, uIcc_of_le hu.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hu.1 le_rfl
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← Finset.sum_mul, recurrenceSubjectWeight_sum, riskSet_mul_invRisk]
    simp only [continuationWeight, if_true, one_mul, remainingMeanDrift]
  · intro i _
    have hi : IntervalIntegrable (fun t => recurrenceSubjectWeight c 0 a s i t *
        P.lam a t) volume 0 1 := by
      simpa only [sub_zero, pow_one] using
        recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg c P hP a s i
          (h := 0) (by norm_num) (by norm_num) 1
    exact hi.mono_set hsub

/-- The observed raw tail minus its drift is exactly the latent compensated
recurrence tail, preserving the full dependence of the empirical coefficient. -/
-- @node: remainingMeanRaw_sub_drift_eq_latent_score
lemma remainingMeanRaw_sub_drift_eq_latent_score (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (z : Fin n → LatentSubject)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    remainingMeanRaw a (fun j => observe (z j)) u -
      remainingMeanDrift P a (fun j => observe (z j)) u =
      remainingRecurrenceExposureScore c P a n u
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) := by
  rw [remainingMeanRaw_eq_latent_point_sum c,
    ← remainingMeanDrift_eq_subject_integrals c P hP a _ hu, ← Finset.sum_sub_distrib]
  unfold remainingRecurrenceExposureScore
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [show (fun t => remainingRecurrenceWeight c a u
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t) =
      (fun t => if u ≤ t ∧ t ≤ 1 then
        recurrenceSubjectWeight c 0 a (fun j => observe (z j)) i t else 0) by
      funext t
      unfold remainingRecurrenceWeight
      rw [recurrenceSubjectWeight_eq_exposureHistory],
    recurrenceIntensity_integral_remaining P hP.poissonRecurrence a _ hu]

/-- The actual observed compensated tail tends to zero in probability by
transport of its derived latent Poisson energy bound. -/
-- @node: remainingMeanRaw_sub_drift_probability_tendsto_zero
lemma remainingMeanRaw_sub_drift_probability_tendsto_zero (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm)
    {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |remainingMeanRaw a s u - remainingMeanDrift P a s u|})
      atTop (nhds 0) := by
  have heq (n : ℕ) : (sampleLaw P n).real {s |
      ε < |remainingMeanRaw a s u - remainingMeanDrift P a s u|} =
      (Measure.pi (fun _ : Fin n => P.latent)).real {z |
        ε < |remainingRecurrenceExposureScore c P a n u
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
          (fun j => (z j).recur a)|} := by
    have hm : Measurable (fun s : Fin n → ObsHistory =>
        remainingMeanRaw a s u - remainingMeanDrift P a s u) := by
      apply Measurable.sub
      · exact (measurable_remainingMeanRaw_joint a).comp
          (measurable_id.prodMk measurable_const)
      · exact measurable_remainingMeanDrift P hP.poissonRecurrence a hu
    rw [recurrence_sampleLaw_eq_latent_map, measureReal_def, Measure.map_apply
      (show Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) by
        fun_prop) (measurableSet_lt measurable_const hm.abs)]
    congr 2
    ext z
    simp only [mem_preimage, mem_setOf_eq,
      remainingMeanRaw_sub_drift_eq_latent_score c P hP a z hu]
  simp_rw [heq]
  exact subcritical_remainingRecurrenceExposureScore_probability_tendsto_zero
    c P hP hk a u hε

/-- Compensator consistency at a fixed lower endpoint follows from the
already proved uniform drift bound. -/
-- @node: remainingMeanDrift_probability_tendsto_target
lemma remainingMeanDrift_probability_tendsto_target (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |remainingMeanDrift P a s u - remainingTarget c P a 0 u|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (remainingMean_compensator_uniform_probability_tendsto_zero c P hP a hε)
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs
  exact ⟨u, hu, hs⟩

/-- The unprojected observed future-mark remaining mean is consistent at
each fixed endpoint, using the genuine score and compensator decomposition. -/
-- @node: remainingMeanRaw_probability_tendsto_target
lemma remainingMeanRaw_probability_tendsto_target (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm)
    {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |remainingMeanRaw a s u - remainingTarget c P a 0 u|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hlim := (remainingMeanRaw_sub_drift_probability_tendsto_zero c P hP hk a hu
    (half_pos hε)).add (remainingMeanDrift_probability_tendsto_target c P hP a hu
      (half_pos hε))
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hlim)
  intro n
  apply (measureReal_mono (show {s : Fin n → ObsHistory |
      ε < |remainingMeanRaw a s u - remainingTarget c P a 0 u|} ⊆
      {s | ε / 2 < |remainingMeanRaw a s u - remainingMeanDrift P a s u|} ∪
      {s | ε / 2 < |remainingMeanDrift P a s u - remainingTarget c P a 0 u|} from ?_)
      (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_contra hn
  have h1 : |remainingMeanRaw a s u - remainingMeanDrift P a s u| ≤ ε / 2 :=
    le_of_not_gt (fun h => hn (Or.inl h))
  have h2 : |remainingMeanDrift P a s u - remainingTarget c P a 0 u| ≤ ε / 2 :=
    le_of_not_gt (fun h => hn (Or.inr h))
  have hb := abs_add_le (remainingMeanRaw a s u - remainingMeanDrift P a s u)
    (remainingMeanDrift P a s u - remainingTarget c P a 0 u)
  simp only [sub_add_sub_cancel] at hb
  exact (not_lt_of_ge (hb.trans (by linarith))) hs

/-- Projection of the raw tail onto the construction's deterministic range
cannot increase its error about the true remaining target. -/
-- @node: remainingMeanHat_error_le_raw
lemma remainingMeanHat_error_le_raw (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤
      |remainingMeanRaw a s u - remainingTarget c P a 0 u| := by
  have ht := remainingTarget_zero_mem_Icc c P hP a hu
  change |max 0 (min (c.lambdaMax * (1 - u)) (remainingMeanRaw a s u)) -
    remainingTarget c P a 0 u| ≤ _
  by_cases hlo : remainingMeanRaw a s u ≤ 0
  · rw [min_eq_right (hlo.trans (ht.1.trans ht.2)), max_eq_left hlo]
    rw [abs_of_nonpos (by linarith [ht.1]), abs_of_nonpos (by linarith [ht.1])]
    linarith
  · by_cases hhi : c.lambdaMax * (1 - u) ≤ remainingMeanRaw a s u
    · rw [min_eq_left hhi, max_eq_right (ht.1.trans ht.2)]
      rw [abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg (by linarith [ht.2])]
      linarith
    · rw [min_eq_right (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]

/-- The actual projected future-mark remaining mean is pointwise consistent,
without a predictability premise for the future recurrence marks. -/
-- @node: remainingMeanHat_probability_tendsto_target
lemma remainingMeanHat_probability_tendsto_target (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm)
    {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (remainingMeanRaw_probability_tendsto_target c P hP hk a hu hε)
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs
  exact hs.trans_le (remainingMeanHat_error_le_raw c P hP a s hu)

/-- Finite-grid bracketing upgrades actual pointwise remaining-mean
consistency to uniform consistency on each bounded study subinterval. -/
-- @node: remainingMeanHat_uniform_probability_tendsto_target
lemma remainingMeanHat_uniform_probability_tendsto_target (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real
      {s | ∃ u ∈ Icc (0 : ℝ) T,
        ε < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
      atTop (nhds 0) := by
  apply remainingMeanHat_uniform_probability_tendsto_of_pointwise c P hP a hT0 hT1
  intro u hu η hη
  exact remainingMeanHat_probability_tendsto_target c P hP hk a
    ⟨hu.1, hu.2.trans hT1⟩ hη

/-- The future-mark plug-in may be replaced by its deterministic remaining
target in localized death optional variation, under the actual model alone. -/
-- @node: localizedDeathVariation_plugin_probability_tendsto_zero
lemma localizedDeathVariation_plugin_probability_tendsto_zero (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|}) atTop (nhds 0) := by
  apply localizedDeathVariation_plugin_probability_tendsto_of_pointwise_modelClass
    c P hP a hT0 hT1
  intro u hu η hη
  exact remainingMeanHat_probability_tendsto_target c P hP hk a
    ⟨hu.1, hu.2.trans hT1.le⟩ hη

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

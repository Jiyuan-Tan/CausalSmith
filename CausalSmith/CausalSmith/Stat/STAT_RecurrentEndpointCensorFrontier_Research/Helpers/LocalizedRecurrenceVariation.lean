module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceOracleApproximation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonLocalization

/-!
# Localized recurrence optional-variation energy

Roadmap (31): the squared KM/inverse-risk event coefficient is of order
one over sample size on a positive-risk localization. Conditional Poisson
energy therefore controls its compensated sum without independence between
KM and the risk sets. This module supplies the localized remainder bound;
full-horizon tail removal and variance assembly remain separate obligations.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A uniformly bounded exposure-dependent coefficient has at most sample
size times its squared bound times the intensity mass as Poisson energy. -/
-- @node: recurrenceJointExposureScore_secondMoment_le_uniform
lemma recurrenceJointExposureScore_secondMoment_le_uniform
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ e i t, |f e i t| ≤ B) :
    Integrable (fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      (n : ℝ) * B ^ 2 * (recurrenceIntensity P a).real univ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  let Q := Measure.pi (fun _ : Fin n => P.latent.map
    (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))
  letI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  letI : SigmaFinite Q := IsFiniteMeasure.toSigmaFinite Q
  have hsq (e) (i) (t) : f e i t ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb e i t) 2
  have hs (e) (t) : (∑ i : Fin n, f e i t ^ 2) ≤ (n : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, B ^ 2 := Finset.sum_le_sum (fun i _ => hsq e i t)
      _ = _ := by simp
  have hm : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2) :=
    Finset.measurable_sum _ (fun i _ => (hf i).pow_const 2)
  have hp : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2) (Q.prod (recurrenceIntensity P a)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable ((n : ℝ) * B ^ 2)
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact hs p.1 p.2
  obtain ⟨hi, he⟩ := recurrenceJointExposureScore_latent_secondMoment c P hP a n f hf hp
  refine ⟨hi, ?_⟩
  rw [he]
  have hslice (e) (i) : Integrable (fun t => f e i t ^ 2) (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      (((hf i).comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
      (B ^ 2)
    filter_upwards [] with t
    simpa only [Function.comp_def, id_eq, Real.norm_of_nonneg (sq_nonneg _)] using hsq e i t
  have heq : (∫ e, (∑ i : Fin n, ∫ t, f e i t ^ 2 ∂recurrenceIntensity P a) ∂Q) =
      ∫ p, (∑ i : Fin n, f p.1 i p.2 ^ 2) ∂Q.prod (recurrenceIntensity P a) := by
    rw [integral_prod _ hp]
    apply integral_congr_ae
    filter_upwards [] with e
    exact (integral_finsetSum _ (fun i _ => hslice e i)).symm
  rw [heq]
  calc
    _ ≤ ∫ _p, (n : ℝ) * B ^ 2 ∂Q.prod (recurrenceIntensity P a) :=
      integral_mono hp (integrable_const _) (fun p => hs p.1 p.2)
    _ = _ := by simp [Measure.prod_apply, measureReal_def, mul_comm]

/-- The localized coefficient of the recurrence optional-variation
remainder. Its risk cutoff depends only on exposure, as does the death KM. -/
-- @node: localizedRecurrenceVariationWeight
noncomputable def localizedRecurrenceVariationWeight (a : Arm) {n : ℕ}
    (T q : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  let s := fun j => recurrenceExposureHistory (e j)
  if t ≤ T ∧ (n : ℝ) * q ≤ riskSet a s t ∧ (s i).treatment = a ∧ t ≤ (s i).exit then
    (n : ℝ) * deathKMLeft a s t ^ 2 * invRisk a s t ^ 2 else 0

/-- Exposure measurability suffices; no independence of empirical weights
and exposure is required. -/
-- @node: measurable_localizedRecurrenceVariationWeight
@[fun_prop] lemma measurable_localizedRecurrenceVariationWeight (a : Arm) {n : ℕ}
    (T q : ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      localizedRecurrenceVariationWeight a T q p.1 i p.2) := by
  dsimp only [localizedRecurrenceVariationWeight]
  apply Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_le measurable_snd measurable_const).inter
    ((measurableSet_le measurable_const
      (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
        (riskSet a (fun j => recurrenceExposureHistory (p.1 j)) p.2 : ℝ)) by fun_prop)).inter
      ((measurableSet_eq_fun
        (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
          (recurrenceExposureHistory (p.1 i)).treatment) by fun_prop) measurable_const).inter
        (measurableSet_le measurable_snd
          (show Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
            (recurrenceExposureHistory (p.1 i)).exit) by fun_prop))))

/-- On the positive-risk cutoff, the actual squared KM/inverse-risk event
coefficient is bounded by the reciprocal of sample size times risk level squared. -/
-- @node: localizedRecurrenceVariationWeight_abs_le
lemma localizedRecurrenceVariationWeight_abs_le (a : Arm) {n : ℕ}
    (hn : 0 < n) (T : ℝ) {q : ℝ} (hq : 0 < q)
    (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    |localizedRecurrenceVariationWeight a T q e i t| ≤ 1 / ((n : ℝ) * q ^ 2) := by
  let s := fun j => recurrenceExposureHistory (e j)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  dsimp only [localizedRecurrenceVariationWeight]
  split_ifs with h
  · have hr : 0 < (riskSet a s t : ℝ) := (mul_pos hnR hq).trans_le h.2.1
    have hr0 : riskSet a s t ≠ 0 := by exact_mod_cast hr.ne'
    have hi : invRisk a s t ≤ 1 / ((n : ℝ) * q) := by
      simp only [invRisk, if_neg hr0, one_div]
      exact inv_anti₀ (mul_pos hnR hq) h.2.1
    have hk := deathKMLeft_mem_Icc a s t
    have hk2 : deathKMLeft a s t ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
    have hi0 := (recurrence_invRisk_mem_Icc a s t).1
    change |(n : ℝ) * deathKMLeft a s t ^ 2 * invRisk a s t ^ 2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (n : ℝ) * 1 * (1 / ((n : ℝ) * q)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hk2 hnR.le)
          (pow_le_pow_left₀ hi0 hi 2) (sq_nonneg _) (by positivity)
      _ = _ := by field_simp
  · simp only [abs_zero]; positivity

/-- The localized optional-variation compensated recurrence sum has second
moment at most intensity mass divided by sample size and risk level to the fourth. -/
-- @node: localizedRecurrenceVariationScore_secondMoment_le
lemma localizedRecurrenceVariationScore_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (T : ℝ) {q : ℝ} (hq : 0 < q) :
    Integrable (fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n
      (localizedRecurrenceVariationWeight a T q)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, recurrenceJointExposureScore P a n
      (localizedRecurrenceVariationWeight a T q)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      (recurrenceIntensity P a).real univ / ((n : ℝ) * q ^ 4) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := recurrenceJointExposureScore_secondMoment_le_uniform c P hP a n
    (localizedRecurrenceVariationWeight a T q)
    (measurable_localizedRecurrenceVariationWeight a T q)
    (1 / ((n : ℝ) * q ^ 2)) (by positivity)
    (localizedRecurrenceVariationWeight_abs_le a hn T hq)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  field_simp
  <;> ring

/-- The localized recurrence optional-variation martingale remainder
vanishes in probability, using its actual conditional Poisson energy. -/
-- @node: localizedRecurrenceVariationScore_probability_tendsto_zero
lemma localizedRecurrenceVariationScore_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (T : ℝ) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (localizedRecurrenceVariationWeight a T q)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have ht : Tendsto (fun n : ℕ =>
      ((recurrenceIntensity P a).real univ / ((n : ℝ) * q ^ 4)) / ε ^ 2)
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      ((recurrenceIntensity P a).real univ / q ^ 4 / ε ^ 2)
    simpa only [Function.comp_def, zero_mul, mul_zero, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using h
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  let F := fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n
    (localizedRecurrenceVariationWeight a T q)
    (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
    (fun j => (z j).recur a)
  obtain ⟨hi, hb⟩ := localizedRecurrenceVariationScore_secondMoment_le c P hP a
    (show 0 < n by omega) T hq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun z => sq_nonneg (F z))) hi (ε ^ 2)
  have hsub : {z | ε < |F z|} ⊆ {z | ε ^ 2 ≤ F z ^ 2} := by
    intro z hz
    change ε < |F z| at hz
    change ε ^ 2 ≤ F z ^ 2
    nlinarith [sq_abs (F z)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  exact ((mul_le_mul_of_nonneg_right (measureReal_mono hsub (by finiteness))
    (sq_nonneg ε)).trans (by simpa only [mul_comm] using hm)).trans hb

/-- The fixed-horizon optional-variation coefficient before risk localization. -/
-- @node: fixedRecurrenceVariationWeight
noncomputable def fixedRecurrenceVariationWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (T : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  if t ≤ T then (n : ℝ) *
    recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 else 0

/-- A positive horizon risk makes the localization inactive at all earlier
recurrence times, by antitonicity of risk sets. -/
-- @node: localizedRecurrenceVariationWeight_eq_fixed
lemma localizedRecurrenceVariationWeight_eq_fixed (c : ClassConstants) (a : Arm)
    {n : ℕ} (T q : ℝ) (e : Fin n → Arm × (ℝ × ENNReal))
    (hr : (n : ℝ) * q ≤ riskSet a (fun j => recurrenceExposureHistory (e j)) T) :
    localizedRecurrenceVariationWeight a T q e = fixedRecurrenceVariationWeight c a T e := by
  funext i t
  have ht (h : t ≤ T) : (n : ℝ) * q ≤
      riskSet a (fun j => recurrenceExposureHistory (e j)) t :=
    hr.trans (by exact_mod_cast riskSet_antitone a _ h)
  unfold localizedRecurrenceVariationWeight fixedRecurrenceVariationWeight recurrenceSubjectWeight
  dsimp only
  by_cases hT : t ≤ T
  · simp only [hT, ht hT, true_and, if_true, continuationWeight, one_mul]
    split_ifs <;> ring
  · simp [hT]

/-- Synthetic same-arm exposure records have exactly the observed arm risk
set; exposures of subjects in the other arm cannot enter that risk count. -/
-- @node: riskSet_observe_eq_recurrenceExposureHistory
lemma riskSet_observe_eq_recurrenceExposureHistory (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) (t : ℝ) :
    riskSet a (fun j => observe (z j)) t = riskSet a (fun j =>
      recurrenceExposureHistory ((z j).treatment, ((z j).death a, (z j).censor a))) t := by
  classical
  unfold riskSet
  congr 1
  ext i
  by_cases hi : (z i).treatment = a
  · simp [observe, recurrenceExposureHistory, censorHorizon, hi]
  · simp [observe, recurrenceExposureHistory, hi]

/-- Removing the risk cutoff on a strict horizon preserves the vanishing
recurrence optional-variation remainder. This is the actual exposure-dependent
Poisson score with coefficient n times the squared ordinary estimator weight. -/
-- @node: fixedRecurrenceVariationScore_probability_tendsto_zero
lemma fixedRecurrenceVariationScore_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  obtain ⟨q, hq, hbad⟩ := exists_observed_horizonRisk_localization c P hP a hT.1 hT.2
  have hbadLatent : Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real
      {z | (riskSet a (fun j => recurrenceExposureHistory
        ((z j).treatment, ((z j).death a, (z j).censor a))) T : ℝ) < (n : ℝ) * q})
      atTop (nhds 0) := by
    apply hbad.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [recurrence_sampleLaw_eq_latent_map, measureReal_def, Measure.map_apply
      (show Measurable (fun z : Fin n → LatentSubject => fun j => observe (z j)) by fun_prop)
      (measurableSet_lt (by fun_prop) measurable_const)]
    simp only [measureReal_def]
    congr 1
    congr 1
    ext z
    simp only [mem_preimage, mem_setOf_eq, riskSet_observe_eq_recurrenceExposureHistory]
  have hloc := localizedRecurrenceVariationScore_probability_tendsto_zero c P hP a T hq hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hbadLatent.add hloc)
  apply Eventually.of_forall
  intro n
  apply (measureReal_mono (show {z : Fin n → LatentSubject |
      ε < |recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} ⊆
      {z | (riskSet a (fun j => recurrenceExposureHistory
        ((z j).treatment, ((z j).death a, (z j).censor a))) T : ℝ) < (n : ℝ) * q} ∪
      {z | ε < |recurrenceJointExposureScore P a n (localizedRecurrenceVariationWeight a T q)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} from ?_) (by finiteness)).trans
    (measureReal_union_le _ _)
  intro z hz
  by_cases hr : (riskSet a (fun j => recurrenceExposureHistory
      ((z j).treatment, ((z j).death a, (z j).censor a))) T : ℝ) < (n : ℝ) * q
  · exact Or.inl hr
  · apply Or.inr
    have he := localizedRecurrenceVariationWeight_eq_fixed c a T q
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) (le_of_not_gt hr)
    change ε < |recurrenceJointExposureScore P a n (localizedRecurrenceVariationWeight a T q)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)|
    simpa only [mem_setOf_eq, recurrenceJointExposureScore, he] using hz

/-- The recurrence optional variation on a strict horizon minus its
conditional intensity integral, under the actual observed sample. -/
-- @node: fixedRecurrenceVariationRemainder
noncomputable def fixedRecurrenceVariationRemainder (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) {n : ℕ} (T : ℝ) (s : Fin n → ObsHistory) : ℝ :=
  (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
    Multiset.sum (((s i).recur.times.filter (fun t => t ≤ T)).map
      (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2)) else 0) -
  ∑ i : Fin n, ∫ t, (if t ≤ T then
    (n : ℝ) * recurrenceSubjectWeight c 0 a s i t ^ 2 else 0) ∂recurrenceIntensity P a

/-- The observed optional-variation remainder is exactly the conditional
Poisson score. This identification preserves the observed recurrence marks
and the dependence of the empirical coefficient on the exposure array. -/
-- @node: fixedRecurrenceVariationRemainder_eq_latent_score
lemma fixedRecurrenceVariationRemainder_eq_latent_score (c : ClassConstants)
    (P : SubjectLaw) (a : Arm) {n : ℕ} (T : ℝ) (z : Fin n → LatentSubject) :
    fixedRecurrenceVariationRemainder c P a T (fun j => observe (z j)) =
    recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) := by
  classical
  unfold fixedRecurrenceVariationRemainder recurrenceJointExposureScore fixedRecurrenceVariationWeight
  simp_rw [← recurrenceSubjectWeight_eq_exposureHistory]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (z i).treatment = a
  · simp only [observe, hi, ↓reduceIte]
    rw [recurrence_stopped_weighted_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [recurrenceSubjectWeight, observe, hi, ↓reduceIte, true_and,
      continuationWeight, one_mul]
    by_cases hx : (((z i).recur a).2 k).1 ≤ min ((z i).death a) (censorHorizon (z i) a)
    <;> by_cases ht : (((z i).recur a).2 k).1 ≤ T
    <;> simp [hx, ht, mul_pow] <;> ring
  · simp [recurrenceSubjectWeight, observe, hi]

/-- The actual observed fixed-horizon recurrence optional-variation
remainder in roadmap (31) tends to zero in probability. -/
-- @node: fixedRecurrenceVariationRemainder_probability_tendsto_zero
lemma fixedRecurrenceVariationRemainder_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |fixedRecurrenceVariationRemainder c P a T s|}) atTop (nhds 0) := by
  have ht := fixedRecurrenceVariationScore_probability_tendsto_zero c P hP a hT hε
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hm : Measurable (fixedRecurrenceVariationRemainder c P a (n := n) T) := by
    letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
    unfold fixedRecurrenceVariationRemainder
    apply Measurable.sub
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · have hpoint : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          if p.2 ≤ T then deathKMLeft a p.1 p.2 ^ 2 * invRisk a p.1 p.2 ^ 2 else 0) :=
          Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
            measurable_const
        have heq : (fun s : Fin n → ObsHistory =>
            Multiset.sum (((s i).recur.times.filter (fun t => t ≤ T)).map
              (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2))) =
            fun s => ∑ k : Fin (s i).recur.1, if (((s i).recur).2 k).1 ≤ T then
              deathKMLeft a s (((s i).recur).2 k).1 ^ 2 *
                invRisk a s (((s i).recur).2 k).1 ^ 2 else 0 := by
          funext s
          exact recurrence_times_filtered_sum _ _ _
        rw [heq]
        have hsum := measurable_recurrence_param_point_sum
          (fun (s : Fin n → ObsHistory) (x : ℝ × ℝ) =>
            if x.1 ≤ T then deathKMLeft a s x.1 ^ 2 * invRisk a s x.1 ^ 2 else 0)
          (hpoint.comp (show Measurable (fun p : (Fin n → ObsHistory) × (ℝ × ℝ) =>
            (p.1, p.2.1)) by fun_prop))
        exact hsum.comp (show Measurable (fun s : Fin n → ObsHistory =>
          (s, (s i).recur)) by fun_prop)
      · exact measurable_const
    · apply Finset.measurable_sum
      intro i _
      have hi : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          if p.2 ≤ T then (n : ℝ) * recurrenceSubjectWeight c 0 a p.1 i p.2 ^ 2 else 0) :=
        Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const
      exact hi.stronglyMeasurable.integral_prod_right'.measurable
  dsimp only
  rw [recurrence_sampleLaw_eq_latent_map]
  simp only [measureReal_def]
  rw [Measure.map_apply
    (show Measurable (fun z : Fin n → LatentSubject => fun j => observe (z j)) by fun_prop)
    (measurableSet_lt measurable_const hm.abs)]
  congr 1
  congr 1
  ext z
  simp only [mem_setOf_eq, mem_preimage, fixedRecurrenceVariationRemainder_eq_latent_score]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

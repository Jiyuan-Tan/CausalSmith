module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonLocalization
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LocalizedDeathVariation

/-!
# Removing reciprocal-risk localization from death variation

Roadmap (39): on a strict horizon, the actual observed lower-risk event
makes the predictable reciprocal-risk cutoff inactive. The localized isometry
therefore proves negligibility of the actual deterministic death remainder.
-/

@[expose] public section

open MeasureTheory Set Filter
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Restrict a deterministic death target to a fixed study horizon. -/
-- @node: fixedDeathVariationTarget
noncomputable def fixedDeathVariationTarget (H : ℝ → ℝ) (T : ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) T).indicator H

/-- The restricted deterministic target is measurable. -/
-- @node: measurable_fixedDeathVariationTarget
@[fun_prop] lemma measurable_fixedDeathVariationTarget (H : ℝ → ℝ)
    (hH : Measurable H) (T : ℝ) : Measurable (fixedDeathVariationTarget H T) := by
  exact hH.indicator measurableSet_Ioc

/-- A lower empirical risk at the horizon makes the cutoff inactive for
all nonzero restricted target coefficients, pathwise. -/
-- @node: fixedDeathVariationIntegrand_eq_localized_of_horizonRisk_lower
lemma fixedDeathVariationIntegrand_eq_localized_of_horizonRisk_lower
    (H : ℝ → ℝ) (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) {T q : ℝ} (hq : 0 < q)
    (hr : (n : ℝ) * q ≤ riskSet a s T) (t : ℝ) :
    (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 *
        inverseRisk t (observedDeathSample a s) ^ 2 =
      localizedDeathVariationIntegrand (fixedDeathVariationTarget H T) q t
        (observedDeathSample a s) := by
  by_cases ht : t ∈ Ioc (0 : ℝ) T
  · have hr' : (n : ℝ) * q ≤ riskSet a s t :=
      hr.trans (by exact_mod_cast riskSet_antitone a s ht.2)
    have hb := scaledInvRisk_le_of_riskFraction_lower hn a s hq hr'
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hi : inverseRisk t (observedDeathSample a s) ≤ 1 / ((n : ℝ) * q) := by
      rw [observedDeathSample_inverseRisk a s ht.1]
      apply (le_div_iff₀ (mul_pos hnR hq)).2
      have hb' := (mul_le_mul_of_nonneg_right hb hq.le)
      simpa only [inv_mul_cancel₀ hq.ne', mul_assoc, mul_left_comm, mul_comm] using hb'
    simp only [localizedDeathVariationIntegrand, if_pos hi]
  · simp [fixedDeathVariationTarget, indicator_of_notMem ht,
      localizedDeathVariationIntegrand]

/-- For a bounded measurable deterministic target, the genuine fixed-horizon
compensated death variation vanishes in probability. Its cutoff is removed
using the actual observed risk event rather than an independence assumption. -/
-- @node: fixedDeathVariationIntegral_probability_tendsto_zero
lemma fixedDeathVariationIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {T B ε : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, |H t| ≤ B) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (fun t x => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2)
        1 (observedDeathSample a s)|}) atTop (nhds 0) := by
  obtain ⟨q, hq, hrisk⟩ := exists_observed_horizonRisk_localization c P hP a hT0 hT1
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, |fixedDeathVariationTarget H T t| ≤ B := by
    intro t _
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · simpa only [fixedDeathVariationTarget, indicator_of_mem ht] using hB t ⟨ht.1.le, ht.2⟩
    · simpa only [fixedDeathVariationTarget, indicator_of_notMem ht, abs_zero] using hB0
  have hlocal := observedLocalizedDeathVariationIntegral_probability_tendsto_zero
    c P hP a _ (measurable_fixedDeathVariationTarget H hH T) hq hb hε
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hrisk.add hlocal)
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply (measureReal_mono ?_ (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_cases hr : (riskSet a s T : ℝ) < (n : ℝ) * q
  · exact Or.inl hr
  · apply Or.inr
    have he : aggregateIntegral (referenceDeathHazard P a)
        (fun t x => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2)
        1 (observedDeathSample a s) =
      aggregateIntegral (referenceDeathHazard P a)
        (localizedDeathVariationIntegrand (fixedDeathVariationTarget H T) q)
        1 (observedDeathSample a s) := by
      unfold aggregateIntegral subjectIntegral
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      · split_ifs <;> try rfl
        exact fixedDeathVariationIntegrand_eq_localized_of_horizonRisk_lower
          H a (by omega) s hq (le_of_not_gt hr) _
      · apply integral_congr_ae
        filter_upwards [] with t
        rw [fixedDeathVariationIntegrand_eq_localized_of_horizonRisk_lower
          H a (by omega) s hq (le_of_not_gt hr) t]
    change ε < |_|
    rw [← he]
    exact hs

/-- The paper's exact remaining target satisfies fixed-horizon death-remainder
negligibility, with no additional model premises. -/
-- @node: ordinaryFixedDeathVariationIntegral_probability_tendsto_zero
lemma ordinaryFixedDeathVariationIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T ε : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (fun t x => (n : ℝ) *
          fixedDeathVariationTarget (ordinaryDeathVariationTarget c P a) T t ^ 2 *
          inverseRisk t x ^ 2) 1 (observedDeathSample a s)|}) atTop (nhds 0) := by
  have hm : Measurable (ordinaryDeathVariationTarget c P a) :=
    (continuousOn_remainingTarget_zero c P hP a).measurable_piecewise
      continuousOn_const measurableSet_Icc
  apply fixedDeathVariationIntegral_probability_tendsto_zero c P hP a _ hm
    hT0 hT1 (B := c.lambdaMax) (c.lambdaMin_pos.trans c.lambdaMin_lt).le _ hε
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT1.le⟩
  have hb := remainingTarget_zero_mem_Icc c P hP a ht'
  simp only [ordinaryDeathVariationTarget, piecewise_eq_of_mem _ _ _ ht',
    abs_of_nonneg hb.1]
  exact hb.2.trans (by nlinarith [ht.1, (c.lambdaMin_pos.trans c.lambdaMin_lt)])

/-- The canonical restricted death integral equals the observable optional
variation minus its exact risk-set compensator. Positive observed death times
are the only path regularity used in the event identification. -/
-- @node: fixedDeathVariationIntegral_eq_optional_sub_compensator
lemma fixedDeathVariationIntegral_eq_optional_sub_compensator
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {n : ℕ} (s : Fin n → ObsHistory)
    {T B : ℝ} (hT : T ≤ 1) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, |H t| ≤ B)
    (hpos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit) :
    aggregateIntegral (referenceDeathHazard P a)
      (fun t x => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2)
      1 (observedDeathSample a s) =
    localizedDeathVariation a s T H - (n : ℝ) * ∫ t in Ioc (0 : ℝ) T,
      H t ^ 2 * invRisk a s t * P.hazard a t := by
  classical
  let x := observedDeathSample a s
  let W := fun t => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2
  have hw (t : ℝ) : |fixedDeathVariationTarget H T t| ≤ B := by
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · simpa only [fixedDeathVariationTarget, indicator_of_mem ht] using hB t ⟨ht.1.le, ht.2⟩
    · simpa only [fixedDeathVariationTarget, indicator_of_notMem ht, abs_zero] using hB0
  have hi (i : Fin n) : Integrable (fun t =>
      W t * referenceDeathHazard P a t * riskIndicator i t x)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    have hm : Measurable (fun t => W t * referenceDeathHazard P a t * riskIndicator i t x) := by
      dsimp [W]
      exact (((measurable_fixedDeathVariationTarget H hH T).pow_const 2 |>.const_mul n).mul
        ((inverseRisk_jointMeasurable.comp (measurable_id.prodMk measurable_const)).pow_const 2)
        |>.mul (measurable_referenceDeathHazard hP a)).mul
          ((measurable_referenceDeath_riskIndicator i).comp (measurable_const.prodMk measurable_id))
    apply Integrable.of_bound hm.aestronglyMeasurable ((n : ℝ) * B ^ 2 * c.dMax)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hd := hP.deathBounds a t ht
    have hr : riskIndicator i t x ∈ Icc (0 : ℝ) 1 := by
      unfold riskIndicator; split_ifs <;> norm_num
    have hd0 : 0 ≤ P.hazard a t := c.dMin_pos.le.trans hd.1
    have hdMax0 : 0 ≤ c.dMax := hd0.trans hd.2
    have hr0 : 0 ≤ riskIndicator i t x := hr.1
    have hh : fixedDeathVariationTarget H T t ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw t) 2
    have hinv := pairInverseRisk_mem_Icc t x
    have hinv2 : inverseRisk t x ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ hinv.1 hinv.2 2
    change ‖(n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2 *
      referenceDeathHazard P a t * riskIndicator i t x‖ ≤ _
    rw [referenceDeathHazard_eq P a ht, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (n : ℝ) * B ^ 2 * 1 * c.dMax * 1 := by
        gcongr <;> first | exact hr.2 | exact hd.2
      _ = _ := by ring
  have hevent : (∑ i : Fin n, if (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
      W (x i).2 else 0) = localizedDeathVariation a s T H := by
    unfold localizedDeathVariation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ha : (s i).treatment = a
    · by_cases hd : (s i).deathInd
      · have hp := hpos i ha hd
        have hx : (x i).2 = (s i).exit := by simp [x, observedDeathSample, observedDeathPair, ha, hd]
        have hxx : (x i).2 < (x i).1 := by simp [x, observedDeathSample, observedDeathPair, ha, hd]
        have hxx' : (s i).exit < (observedDeathSample a s i).1 := by
          simpa only [hx, x] using hxx
        rw [hx]
        by_cases ht : (s i).exit ≤ T
        · have hm : (s i).exit ∈ Ioc (0 : ℝ) T := ⟨hp, ht⟩
          simp [W, ht.trans hT, fixedDeathVariationTarget, hm, ha, hd,
            observedDeathSample_inverseRisk a s hp, x, hxx', ht, mul_assoc]
        · simp [W, fixedDeathVariationTarget, ht, ha, hd]
      · simp [x, observedDeathSample, observedDeathPair, ha, hd]
    · simp [x, observedDeathSample, observedDeathPair, ha]
  have hsum (t : ℝ) : (∑ i : Fin n,
      W t * referenceDeathHazard P a t * riskIndicator i t x) =
      (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 *
        referenceDeathHazard P a t * inverseRisk t x := by
    rw [← Finset.mul_sum]
    dsimp [W]
    calc
      _ = (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 *
          referenceDeathHazard P a t *
            (inverseRisk t x ^ 2 * ∑ i : Fin n, riskIndicator i t x) := by ring
      _ = _ := by rw [inverseRisk_square_risk]
  have hdrift : (∫ t in Icc (0 : ℝ) 1,
      (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 *
        referenceDeathHazard P a t * inverseRisk t x) =
      (n : ℝ) * ∫ t in Ioc (0 : ℝ) T, H t ^ 2 * invRisk a s t * P.hazard a t := by
    rw [← integral_const_mul]
    have hf : (fun t => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 *
        referenceDeathHazard P a t * inverseRisk t x) =
        (Ioc (0 : ℝ) T).indicator (fun t =>
          (n : ℝ) * H t ^ 2 * referenceDeathHazard P a t * inverseRisk t x) := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) T <;> simp [fixedDeathVariationTarget, ht]
    rw [hf, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) 1 from
        fun t ht => ⟨ht.1.le, ht.2.trans hT⟩)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [referenceDeathHazard_eq P a ⟨ht.1.le, ht.2.trans hT⟩,
      show inverseRisk t x = invRisk a s t from observedDeathSample_inverseRisk a s ht.1]
    ring
  change (∑ i : Fin n, subjectIntegral (referenceDeathHazard P a)
    (fun t x => (n : ℝ) * fixedDeathVariationTarget H T t ^ 2 * inverseRisk t x ^ 2) i 1 x) = _
  simp only [subjectIntegral, Finset.sum_sub_distrib]
  change (∑ i : Fin n, if (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then W (x i).2 else 0) -
    (∑ i : Fin n, ∫ t in Icc (0 : ℝ) 1, W t * referenceDeathHazard P a t * riskIndicator i t x) = _
  rw [hevent, ← integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hsum]
  rw [hdrift]

/-- The actual fixed-horizon deterministic death optional variation minus
its compensator is negligible under the observed model (roadmap (39)). -/
-- @node: ordinaryFixedDeathVariationRemainder_probability_tendsto_zero
lemma ordinaryFixedDeathVariationRemainder_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T ε : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingTarget c P a 0) -
        (n : ℝ) * ∫ t in Ioc (0 : ℝ) T,
          remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t|})
      atTop (nhds 0) := by
  have ht := ordinaryFixedDeathVariationIntegral_probability_tendsto_zero c P hP a hT0 hT1 hε
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  filter_upwards [DeathCP.sample_arm_death_exit_pos_ae P hP.deathHazard a n] with s hs
  have hm : Measurable (ordinaryDeathVariationTarget c P a) :=
    (continuousOn_remainingTarget_zero c P hP a).measurable_piecewise
      continuousOn_const measurableSet_Icc
  have hb : ∀ t ∈ Icc (0 : ℝ) T, |ordinaryDeathVariationTarget c P a t| ≤ c.lambdaMax := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT1.le⟩
    have hh := remainingTarget_zero_mem_Icc c P hP a ht'
    simp only [ordinaryDeathVariationTarget, piecewise_eq_of_mem _ _ _ ht', abs_of_nonneg hh.1]
    exact hh.2.trans (by nlinarith [ht.1, (c.lambdaMin_pos.trans c.lambdaMin_lt)])
  change (ε < |aggregateIntegral (referenceDeathHazard P a)
    (fun t x => (n : ℝ) * fixedDeathVariationTarget (ordinaryDeathVariationTarget c P a) T t ^ 2 *
      inverseRisk t x ^ 2) 1 (observedDeathSample a s)|) =
    (ε < |localizedDeathVariation a s T (remainingTarget c P a 0) -
      (n : ℝ) * ∫ t in Ioc (0 : ℝ) T,
        remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t|)
  rw [fixedDeathVariationIntegral_eq_optional_sub_compensator c P hP a _ hm s hT1.le
    (c.lambdaMin_pos.trans c.lambdaMin_lt).le hb hs]
  have he : localizedDeathVariation a s T (ordinaryDeathVariationTarget c P a) =
      localizedDeathVariation a s T (remainingTarget c P a 0) := by
    unfold localizedDeathVariation
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [ordinaryDeathVariationTarget, piecewise_eq_of_mem _ _ _
        (show (s i).exit ∈ Icc (0 : ℝ) 1 from ⟨(hs i hi.1 hi.2.1).le, hi.2.2.trans hT1.le⟩)]
    · rfl
  have hi : (∫ t in Ioc (0 : ℝ) T,
      ordinaryDeathVariationTarget c P a t ^ 2 * invRisk a s t * P.hazard a t) =
      ∫ t in Ioc (0 : ℝ) T,
        remainingTarget c P a 0 t ^ 2 * invRisk a s t * P.hazard a t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [ordinaryDeathVariationTarget, piecewise_eq_of_mem _ _ _
      (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.trans hT1.le⟩)]
  rw [he, hi]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedDeathOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPlugin

/-!
# Localized deterministic death optional-variation remainder

Roadmap (39): truncate the reciprocal risk before applying the predictable
counting-process isometry. The coefficient is n times a deterministic squared
remaining target times inverse risk squared. Its energy vanishes without
independence of the empirical risk set and death marks.
-/

@[expose] public section

open MeasureTheory Set Filter
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The deterministic death-variation payoff, localized by reciprocal risk. -/
-- @node: localizedDeathVariationIntegrand
noncomputable def localizedDeathVariationIntegrand (H : ℝ → ℝ) {n : ℕ}
    (q : ℝ) (t : ℝ) (x : Sample n) : ℝ :=
  if inverseRisk t x ≤ 1 / ((n : ℝ) * q) then
    (n : ℝ) * H t ^ 2 * inverseRisk t x ^ 2 else 0

/-- Reciprocal-risk localization preserves left predictability. -/
-- @node: localizedDeathVariationIntegrand_leftPredictable
lemma localizedDeathVariationIntegrand_leftPredictable (H : ℝ → ℝ) (n : ℕ) (q : ℝ) :
    LeftPredictable (localizedDeathVariationIntegrand H (n := n) q) := by
  intro t x y hh
  unfold localizedDeathVariationIntegrand
  rw [inverseRisk_leftPredictable t x y hh]

/-- The localized deterministic coefficient is jointly measurable. -/
-- @node: measurable_localizedDeathVariationIntegrand
@[fun_prop] lemma measurable_localizedDeathVariationIntegrand (H : ℝ → ℝ)
    (hH : Measurable H) (n : ℕ) (q : ℝ) :
    Measurable (fun p : ℝ × Sample n => localizedDeathVariationIntegrand H q p.1 p.2) := by
  unfold localizedDeathVariationIntegrand
  exact (((hH.comp measurable_fst).pow_const 2).const_mul n |>.mul
    (inverseRisk_jointMeasurable.pow_const 2)).ite
      (measurableSet_le inverseRisk_jointMeasurable measurable_const) measurable_const

/-- The risk cutoff makes the variation payoff of order one over sample size. -/
-- @node: localizedDeathVariationIntegrand_abs_le
lemma localizedDeathVariationIntegrand_abs_le (H : ℝ → ℝ) {n : ℕ}
    (hn : 0 < n) {q : ℝ} (hq : 0 < q) {B t : ℝ} (hB : |H t| ≤ B)
    (x : Sample n) :
    |localizedDeathVariationIntegrand H q t x| ≤ B ^ 2 / ((n : ℝ) * q ^ 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold localizedDeathVariationIntegrand
  split_ifs with hi
  · rw [abs_of_nonneg (by positivity)]
    have hH2 : H t ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hB 2
    calc
      _ ≤ (n : ℝ) * B ^ 2 * (1 / ((n : ℝ) * q)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH2 hnR.le)
          (pow_le_pow_left₀ (pairInverseRisk_mem_Icc t x).1 hi 2)
          (sq_nonneg _) (by positivity)
      _ = _ := by field_simp
  · simp only [abs_zero]; positivity

/-- The actual localized death energy has the explicit inverse-sample-size
bound, retaining the full empirical risk dependence. -/
-- @node: localizedDeathVariationIntegrand_energyDensity_le
lemma localizedDeathVariationIntegrand_energyDensity_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 0 < q)
    {B t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hB : |H t| ≤ B) (x : Sample n) :
    localizedDeathVariationIntegrand H q t x ^ 2 * referenceDeathHazard P a t *
        (∑ i : Fin n, riskIndicator i t x) ≤
      B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd : 0 ≤ c.dMax := c.dMin_pos.le.trans
    ((hP.deathBounds a t ht).1.trans (hP.deathBounds a t ht).2)
  have hr0 : 0 ≤ ∑ i : Fin n, riskIndicator i t x := by
    apply Finset.sum_nonneg; intro i _; unfold riskIndicator; split_ifs <;> norm_num
  have hr : (∑ i : Fin n, riskIndicator i t x) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro i _; unfold riskIndicator; split_ifs <;> norm_num
      _ = _ := by simp
  have hw := localizedDeathVariationIntegrand_abs_le H hn hq hB x
  have hw2 : localizedDeathVariationIntegrand H q t x ^ 2 ≤
      (B ^ 2 / ((n : ℝ) * q ^ 2)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  rw [referenceDeathHazard_eq P a ht]
  calc
    _ ≤ (B ^ 2 / ((n : ℝ) * q ^ 2)) ^ 2 * c.dMax * (n : ℝ) :=
      mul_le_mul (mul_le_mul hw2 (hP.deathBounds a t ht).2
        (c.dMin_pos.le.trans (hP.deathBounds a t ht).1) (sq_nonneg _))
        hr hr0 (by positivity)
    _ = _ := by field_simp

/-- The localized death payoff has integrable sample-by-time energy. -/
-- @node: localizedDeathVariationIntegrand_energy_integrable_prod
lemma localizedDeathVariationIntegrand_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {n : ℕ} (hn : 0 < n)
    {q B : ℝ} (hq : 0 < q) (hB : ∀ t ∈ Icc (0 : ℝ) 1, |H t| ≤ B) :
    Integrable (fun p : Sample n × ℝ =>
      localizedDeathVariationIntegrand H q p.2 p.1 ^ 2 * referenceDeathHazard P a p.2 *
        (∑ i : Fin n, riskIndicator i p.2 p.1))
      ((Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).prod
          (volume.restrict (Icc (0 : ℝ) 1))) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw; infer_instance
  have hm : Measurable (fun p : Sample n × ℝ =>
      localizedDeathVariationIntegrand H q p.2 p.1 ^ 2 * referenceDeathHazard P a p.2 *
        (∑ i : Fin n, riskIndicator i p.2 p.1)) :=
    (((measurable_localizedDeathVariationIntegrand H hH n q).comp measurable_swap).pow_const 2
      |>.mul ((measurable_referenceDeathHazard hP a).comp measurable_snd)).mul
        (Finset.measurable_sum _ (fun i _ => measurable_referenceDeath_riskIndicator i))
  apply Integrable.of_bound hm.aestronglyMeasurable (B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4))
  have ht : ∀ᵐ p : Sample n × ℝ ∂(Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)).prod
        (volume.restrict (Icc (0 : ℝ) 1)), p.2 ∈ Icc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
    (referenceDeathHazard_nonneg hP a p.2))
      (Finset.sum_nonneg (fun i _ => by unfold riskIndicator; split_ifs <;> norm_num)))]
  exact localizedDeathVariationIntegrand_energyDensity_le c P hP a H hn hq hp (hB _ hp) _

/-- Isometry bounds the genuine localized compensated death variation by
its inverse-sample-size energy; no independent-weight argument is used. -/
-- @node: localizedDeathVariationIntegral_secondMoment_le
lemma localizedDeathVariationIntegral_secondMoment_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {n : ℕ} (hn : 0 < n)
    {q B : ℝ} (hq : 0 < q) (hB : ∀ t ∈ Icc (0 : ℝ) 1, |H t| ≤ B) :
    Integrable (fun x : Sample n =>
      aggregateIntegral (referenceDeathHazard P a) (localizedDeathVariationIntegrand H q) 1 x ^ 2)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ∧
    (∫ x : Sample n,
      aggregateIntegral (referenceDeathHazard P a) (localizedDeathVariationIntegrand H q) 1 x ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw; infer_instance
  have hp := localizedDeathVariationIntegrand_energy_integrable_prod c P hP a H hH hn hq hB
  have hj := deathAggregateIntegral_moments_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a) _
    (localizedDeathVariationIntegrand_leftPredictable H n q)
    (measurable_localizedDeathVariationIntegrand H hH n q) 1 (by norm_num) hp
  refine ⟨hj.2.2.1, ?_⟩
  rw [hj.2.2.2]
  have he (x : Sample n) : predictableEnergy (referenceDeathHazard P a)
      (localizedDeathVariationIntegrand H q) 1 x ≤ B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4) := by
    unfold predictableEnergy
    have hslice : Integrable (fun t => localizedDeathVariationIntegrand H q t x ^ 2 *
        referenceDeathHazard P a t * (∑ i : Fin n, riskIndicator i t x))
        (volume.restrict (Icc (0 : ℝ) 1)) := by
      apply Integrable.of_bound
        ((((measurable_localizedDeathVariationIntegrand H hH n q).comp
          (measurable_id.prodMk measurable_const)).pow_const 2).mul
            (measurable_referenceDeathHazard hP a) |>.mul
              (Finset.measurable_sum _ (fun i _ =>
                (measurable_referenceDeath_riskIndicator i).comp
                  (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
        (B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change ‖localizedDeathVariationIntegrand H q t x ^ 2 * referenceDeathHazard P a t *
        (∑ i : Fin n, riskIndicator i t x)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
        (referenceDeathHazard_nonneg hP a t))
          (Finset.sum_nonneg (fun i _ => by unfold riskIndicator; split_ifs <;> norm_num)))]
      exact localizedDeathVariationIntegrand_energyDensity_le c P hP a H hn hq ht (hB _ ht) x
    calc
      _ ≤ ∫ _t in Icc (0 : ℝ) 1, B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4) :=
        integral_mono_ae hslice (integrable_const _) (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact localizedDeathVariationIntegrand_energyDensity_le c P hP a H hn hq ht (hB _ ht) x)
      _ = _ := by simp
  calc
    _ ≤ ∫ _x : Sample n, B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4) ∂μ :=
      integral_mono hp.integral_prod_left (integrable_const _) he
    _ = _ := by simp

/-- Chebyshev and the predictable isometry make the localized deterministic
death optional-variation remainder negligible in probability. -/
-- @node: localizedDeathVariationIntegral_probability_tendsto_zero
lemma localizedDeathVariationIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {q B ε : ℝ} (hq : 0 < q)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, |H t| ≤ B) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).real {x |
          ε < |aggregateIntegral (referenceDeathHazard P a)
            (localizedDeathVariationIntegrand H q) 1 x|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  have ht : Tendsto (fun n : ℕ =>
      (B ^ 4 * c.dMax / ((n : ℝ) * q ^ 4)) / ε ^ 2) atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (B ^ 4 * c.dMax / q ^ 4 / ε ^ 2)
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_left_comm, mul_comm] using h
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  letI : IsProbabilityMeasure μ := by
    unfold μ Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw; infer_instance
  let J := aggregateIntegral (referenceDeathHazard P a)
    (localizedDeathVariationIntegrand H (n := n) q) 1
  obtain ⟨hi, hb⟩ := localizedDeathVariationIntegral_secondMoment_le
    c P hP a H hH (show 0 < n by omega) hq hB
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg (J x))) hi (ε ^ 2)
  have hsub : {x | ε < |J x|} ⊆ {x | ε ^ 2 ≤ J x ^ 2} := by
    intro x hx
    change ε < |J x| at hx
    change ε ^ 2 ≤ J x ^ 2
    nlinarith [sq_abs (J x)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  exact ((mul_le_mul_of_nonneg_right (measureReal_mono hsub (by finiteness))
    (sq_nonneg ε)).trans (by simpa only [mul_comm] using hm)).trans hb

/-- The vanishing localized remainder transfers to the actual observed law
through the stopped reference sample, preserving its predictable dependence. -/
-- @node: observedLocalizedDeathVariationIntegral_probability_tendsto_zero
lemma observedLocalizedDeathVariationIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (H : ℝ → ℝ) (hH : Measurable H) {q B ε : ℝ} (hq : 0 < q)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, |H t| ≤ B) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (localizedDeathVariationIntegrand H q) 1 (observedDeathSample a s)|})
      atTop (nhds 0) := by
  apply (localizedDeathVariationIntegral_probability_tendsto_zero c P hP a H hH hq hB hε).congr'
  apply Eventually.of_forall
  intro n
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J := aggregateIntegral (referenceDeathHazard P a)
    (localizedDeathVariationIntegrand H (n := n) q) 1
  have hJ : Measurable J := measurable_deathAggregateIntegral_joint _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_localizedDeathVariationIntegrand H hH n q) 1
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hP.deathHazard
      hP.randomAssignment hP.independentCensoring a
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (localizedDeathVariationIntegrand_leftPredictable H n q) x hx.1 hx.2.1 hx.2.2
      (by norm_num) (by norm_num)
  have hset : MeasurableSet {x : Sample n | ε < |J x|} :=
    measurableSet_lt measurable_const hJ.abs
  have he : (sampleLaw P n).real {s | ε < |J (observedDeathSample a s)|} =
      μ.real {x | ε < |J x|} := by
    simp only [measureReal_def]
    change ((sampleLaw P n) (observedDeathSample a ⁻¹' {x | ε < |J x|})).toReal =
      (μ {x | ε < |J x|}).toReal
    rw [← Measure.map_apply hs hset, hmap,
      Measure.map_apply measurable_referenceStoppedSyntheticSample hset]
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hreg] with x hx
    change (ε < |J (referenceStoppedSyntheticSample x)|) = (ε < |J x|)
    rw [hx]
  exact he.symm

/-- The actual remaining target restricted to the study window; this uses
only within-window continuity, without any smooth global extension. -/
-- @node: ordinaryDeathVariationTarget
noncomputable def ordinaryDeathVariationTarget (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).piecewise (remainingTarget c P a 0) (fun _ => 0) t

/-- The paper's deterministic squared remaining-target payoff has a negligible
risk-localized compensated death remainder under the actual observed sample. -/
-- @node: ordinaryLocalizedDeathVariationIntegral_probability_tendsto_zero
lemma ordinaryLocalizedDeathVariationIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (localizedDeathVariationIntegrand (ordinaryDeathVariationTarget c P a) q)
        1 (observedDeathSample a s)|}) atTop (nhds 0) := by
  have hm : Measurable (ordinaryDeathVariationTarget c P a) :=
    (continuousOn_remainingTarget_zero c P hP a).measurable_piecewise
      continuousOn_const measurableSet_Icc
  apply observedLocalizedDeathVariationIntegral_probability_tendsto_zero
    c P hP a _ hm hq (B := c.lambdaMax) _ hε
  intro t ht
  have hb := remainingTarget_zero_mem_Icc c P hP a ht
  simp only [ordinaryDeathVariationTarget, piecewise_eq_of_mem _ _ _ ht,
    abs_of_nonneg hb.1]
  have hl : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans
    ((hP.recurrenceBounds a t ht).1.trans (hP.recurrenceBounds a t ht).2)
  exact hb.2.trans (by nlinarith [ht.1])

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

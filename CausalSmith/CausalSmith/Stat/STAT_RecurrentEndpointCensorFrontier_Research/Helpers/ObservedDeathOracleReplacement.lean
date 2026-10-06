module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathOracleDifferenceMoments

/-!
# Observed full-horizon death oracle replacement

Roadmap (18)--(19): transport the predictable difference integral through the
stopped reference law, preserving its second moment and deriving the actual
observed probability limit without a bounded endpoint-weight assumption.
-/

public section

open MeasureTheory Set Filter
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Joint measurability of a coefficient gives measurability of its finite
compensated death integral, including unbounded coefficients. -/
-- @node: measurable_deathAggregateIntegral_joint
@[fun_prop]
lemma measurable_deathAggregateIntegral_joint {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (hh : Measurable hazard) (hH : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (u : ℝ) : Measurable (aggregateIntegral hazard H u) := by
  unfold aggregateIntegral
  apply Finset.measurable_sum
  intro i _
  unfold subjectIntegral
  apply Measurable.sub
  · have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
    have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
    exact (hH.comp (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter
        (measurableSet_lt hc hf)) measurable_const
  · have hm : Measurable (fun p : Sample n × ℝ =>
        H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1) :=
      ((hH.comp measurable_swap).mul (hh.comp measurable_snd)).mul
        (measurable_referenceDeath_riskIndicator i)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The observed predictable difference integral is centered and square
integrable; its second moment equals the canonical reference second moment. -/
-- @node: observedDeathOracleDifferenceIntegral_moments
lemma observedDeathOracleDifferenceIntegral_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    let J := aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1
    Integrable (fun s => J (observedDeathSample a s)) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => J (observedDeathSample a s) ^ 2) (sampleLaw P n) ∧
    (∫ s, J (observedDeathSample a s) ^ 2 ∂sampleLaw P n) =
      ∫ x : Sample n, J x ^ 2
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J := aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  have hJ : Measurable J := measurable_deathAggregateIntegral_joint _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_deathOracleDifferenceIntegrand c P hP a n) 1
  have hj := deathOracleDifferenceIntegrand_full_moments c P hP hk a n
  have hreg : (fun x => J (referenceStoppedSyntheticSample x)) =ᵐ[μ] J := by
    filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
    exact DeathCP.aggregateIntegral_referenceStoppedSyntheticSample _ _
      (deathOracleDifferenceIntegrand_leftPredictable c P a n) x hx.1 hx.2.1 hx.2.2
      (by norm_num) (by norm_num)
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have hmap : (sampleLaw P n).map (observedDeathSample a) =
      μ.map referenceStoppedSyntheticSample :=
    observedDeathSample_map_eq_reference P hP.deathHazard
      hP.randomAssignment hP.independentCensoring a
  have transfer (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ s, f (J (observedDeathSample a s)) ∂sampleLaw P n) =
        ∫ x, f (J x) ∂μ := by
    change (∫ s, (f ∘ J) (observedDeathSample a s) ∂sampleLaw P n) =
      ∫ x, (f ∘ J) x ∂μ
    rw [← integral_map hs.aemeasurable (hf.comp hJ).aestronglyMeasurable, hmap,
      integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
        (hf.comp hJ).aestronglyMeasurable]
    exact integral_congr_ae (hreg.fun_comp f)
  have integrable_transfer (f : ℝ → ℝ) (hf : Measurable f)
      (hi : Integrable (fun x => f (J x)) μ) :
      Integrable (fun s => f (J (observedDeathSample a s))) (sampleLaw P n) := by
    apply (integrable_map_measure (hf.comp hJ).aestronglyMeasurable hs.aemeasurable).1
    rw [hmap]
    exact (integrable_map_measure (hf.comp hJ).aestronglyMeasurable
      measurable_referenceStoppedSyntheticSample.aemeasurable).2
        (hi.congr (hreg.fun_comp f).symm)
  refine ⟨integrable_transfer id measurable_id hj.1, ?_,
    integrable_transfer (fun x : ℝ => x ^ 2) (by fun_prop) hj.2.2.1,
    transfer (fun x : ℝ => x ^ 2) (by fun_prop)⟩
  exact (transfer id measurable_id).trans hj.2.1

/-- The actual observed full-horizon death difference vanishes in second
mean, by stopped-law transport of the predictable isometry. -/
-- @node: observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
lemma observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s,
      (aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)) ^ 2
      ∂sampleLaw P n) atTop (nhds 0) := by
  apply (deathOracleDifferenceIntegral_secondMoment_tendsto_zero c P hP hk a).congr'
  exact Eventually.of_forall (fun n =>
    (observedDeathOracleDifferenceIntegral_moments c P hP hk a n).2.2.2.symm)

/-- Chebyshev gives the full-horizon observed death difference probability
limit, with the singular endpoint handled by its proved integrable energy. -/
-- @node: observedDeathOracleDifferenceIntegral_probability_tendsto_zero
lemma observedDeathOracleDifferenceIntegral_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |aggregateIntegral (referenceDeathHazard P a)
        (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hlim := (observedDeathOracleDifferenceIntegral_secondMoment_tendsto_zero
    c P hP hk a).div_const (ε ^ 2)
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let J := fun s : Fin n → ObsHistory => aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)
  have hi := (observedDeathOracleDifferenceIntegral_moments c P hP hk a n).2.2.1
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (J s))) hi (ε ^ 2)
  have hsub : {s | ε < |J s|} ⊆ {s | ε ^ 2 ≤ J s ^ 2} := by
    intro s hs
    change ε < |J s| at hs
    change ε ^ 2 ≤ J s ^ 2
    nlinarith [sq_abs (J s)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [mul_comm, J] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
      (sq_nonneg ε)).trans hm

/-- Finite quadratic energies supply the pathwise integrability needed for
linearity of the normalized death difference on the reference law. -/
-- @node: deathOracleDifferenceIntegral_eq_scaled_difference_ae
lemma deathOracleDifferenceIntegral_eq_scaled_difference_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    (aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a (n := n)) 1) =ᵐ[
        Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)]
      fun x => Real.sqrt n * aggregateIntegral (referenceDeathHazard P a)
        (deathCPIntegrand c P a 0) 1 x -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1 x /
            Real.sqrt n := by
  classical
  have hq := (deathAggregateIntegral_energy_conditions_of_integrable_prod _ _ _
    (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t)
    1 (subcriticalDeathOracle_energy_integrable_prod c P hP hk a n)).1
  have hp : ∀ᵐ x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a), ∀ i : Fin n,
      Integrable (fun t => deathCPIntegrand c P a 0 t x *
        referenceDeathHazard P a t * riskIndicator i t x)
        (volume.restrict (Icc (0 : ℝ) 1)) ∧
      Integrable (fun t => subcriticalDeathOracleWeight c P a t *
        referenceDeathHazard P a t * riskIndicator i t x)
        (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Filter.eventually_all]
    intro i
    exact (subject_hazard_path_integrable_ae _ _ _
      (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a)
      _ (deathCPIntegrand_jointMeasurable c P hP a (by norm_num) (by norm_num))
      i 1 (by norm_num)
      (by simpa only [sub_zero] using (DeathCP.deathCPIntegrand_quadraticEnergyFinite
        c P hP a (h := 0) (by norm_num) (by norm_num)))).and
      (subject_hazard_path_integrable_ae _ _ _
        (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a)
        _ ((measurable_subcriticalDeathOracleWeight c P hP a).comp measurable_fst)
        i 1 (by norm_num) hq)
  filter_upwards [hp] with x hx
  unfold aggregateIntegral
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold subjectIntegral deathOracleDifferenceIntegrand
  have he : (fun t => (Real.sqrt n * deathCPIntegrand c P a 0 t x -
      subcriticalDeathOracleWeight c P a t / Real.sqrt n) *
        referenceDeathHazard P a t * riskIndicator i t x) =
      fun t => Real.sqrt n * (deathCPIntegrand c P a 0 t x *
        referenceDeathHazard P a t * riskIndicator i t x) -
        (subcriticalDeathOracleWeight c P a t * referenceDeathHazard P a t *
          riskIndicator i t x) / Real.sqrt n := by funext t; ring
  rw [he, integral_sub ((hx i).1.const_mul _) ((hx i).2.div_const _),
    integral_const_mul, integral_div]
  split_ifs <;> ring

/-- The predictable integral equals the actual root-n estimated death error
minus the normalized endpoint oracle, almost surely on observed samples. -/
-- @node: observedDeathOracleDifferenceIntegral_eq_deathError_ae
lemma observedDeathOracleDifferenceIntegral_eq_deathError_ae
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    (fun s => aggregateIntegral (referenceDeathHazard P a)
      (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)) =ᵐ[sampleLaw P n]
      fun s => Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n := by
  let μ := Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
    (armDeathFailureLaw P a) (referenceDeathLaw P a)
  let J := aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a (n := n)) 1
  let K := aggregateIntegral (referenceDeathHazard P a)
    (deathCPIntegrand c P a 0 (n := n)) 1
  let O := aggregateIntegral (referenceDeathHazard P a)
    (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
  have hJ : Measurable J := measurable_deathAggregateIntegral_joint _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_deathOracleDifferenceIntegrand c P hP a n) 1
  have hK : Measurable K := measurable_deathAggregateIntegral_joint _ _
    (measurable_referenceDeathHazard hP a)
    (deathCPIntegrand_jointMeasurable c P hP a (by norm_num) (by norm_num)) 1
  have hO : Measurable O := measurable_deathAggregateIntegral_deterministic _ _
    (measurable_referenceDeathHazard hP a)
    (measurable_subcriticalDeathOracleWeight c P hP a) 1
  have he : J =ᵐ[μ.map referenceStoppedSyntheticSample]
      fun x => Real.sqrt n * K x - O x / Real.sqrt n := by
    apply (ae_map_iff measurable_referenceStoppedSyntheticSample.aemeasurable
      (measurableSet_eq_fun hJ ((hK.const_mul _).sub (hO.div_const _)))).2
    filter_upwards [deathOracleDifferenceIntegral_eq_scaled_difference_ae c P hP hk a n,
      DeathCP.referenceSample_regular_ae c P hP a n] with x hx hr
    have stop (H : ℝ → Sample n → ℝ) (hH : LeftPredictable H) :=
      DeathCP.aggregateIntegral_referenceStoppedSyntheticSample
        (referenceDeathHazard P a) H hH x hr.1 hr.2.1 hr.2.2
        (u := 1) (by norm_num) (by norm_num)
    change J (referenceStoppedSyntheticSample x) =
      Real.sqrt n * K (referenceStoppedSyntheticSample x) -
        O (referenceStoppedSyntheticSample x) / Real.sqrt n
    dsimp only [J, K, O]
    rw [stop _ (deathOracleDifferenceIntegrand_leftPredictable c P a n),
      stop _ (deathCPIntegrand_leftPredictable c P a 0),
      stop _ (by intro t x y hh; rfl)]
    exact hx
  rw [← observedDeathSample_map_eq_reference P hP.deathHazard
    hP.randomAssignment hP.independentCensoring a] at he
  have hs : Measurable (observedDeathSample a (n := n)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have ho := (ae_map_iff hs.aemeasurable
    (measurableSet_eq_fun hJ ((hK.const_mul _).sub (hO.div_const _)))).1 he
  have hd := DeathCP.aggregateIntegral_observedDeathSample_eq_deathError_ae
    c P hP a n (h := 0) (by norm_num) (by norm_num)
  simp only [sub_zero] at hd
  filter_upwards [ho, hd] with s hs hd
  change J (observedDeathSample a s) = _ at hs ⊢
  rw [hs]
  change Real.sqrt n * K (observedDeathSample a s) -
    O (observedDeathSample a s) / Real.sqrt n = _
  rw [show K (observedDeathSample a s) = deathError c P a s 0 from hd]

/-- The actual ordinary death martingale admits full-horizon endpoint oracle
replacement at root-n scale, as required in roadmap (18)--(19). -/
-- @node: deathError_zero_oracle_difference_probability_tendsto_zero
lemma deathError_zero_oracle_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n|}) atTop (nhds 0) := by
  apply (observedDeathOracleDifferenceIntegral_probability_tendsto_zero c P hP hk a hε).congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  filter_upwards [observedDeathOracleDifferenceIntegral_eq_deathError_ae c P hP hk a n]
    with s hs
  change (ε < |aggregateIntegral (referenceDeathHazard P a)
    (deathOracleDifferenceIntegrand c P a) 1 (observedDeathSample a s)|) =
      (ε < |Real.sqrt n * deathError c P a s 0 -
        aggregateIntegral (referenceDeathHazard P a)
          (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
          (observedDeathSample a s) / Real.sqrt n|)
  rw [hs]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

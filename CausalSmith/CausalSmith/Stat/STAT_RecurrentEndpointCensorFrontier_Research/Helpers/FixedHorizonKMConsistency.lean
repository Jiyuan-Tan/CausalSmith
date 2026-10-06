module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonLocalization

/-!
# Ordinary KM consistency on strict horizons

Roadmap (9)--(13): remove the inverse-risk weight from the verified dependent
KM second moment. Nonempty risk sets have scaled inverse risk at least one;
the exceptional empty-risk event vanishes by the actual iid risk marginal.
No independence between KM and the risk set is used.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- On a nonempty risk set, the scaled inverse risk is at least one. -/
-- @node: one_le_scaledInvRisk_of_nonempty
lemma one_le_scaledInvRisk_of_nonempty {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (hr : riskSet a s t ≠ 0) :
    1 ≤ (n : ℝ) * invRisk a s t := by
  have hcard : riskSet a s t ≤ n := by
    unfold riskSet
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hpos : (0 : ℝ) < riskSet a s t := by
    exact_mod_cast Nat.pos_of_ne_zero hr
  simp only [invRisk, hr, if_false, ← div_eq_mul_inv]
  apply (le_div_iff₀ hpos).2
  simpa only [one_mul] using (show (riskSet a s t : ℝ) ≤ n by exact_mod_cast hcard)

/-- At any strict horizon the actual empirical risk set is empty with
probability tending to zero. -/
-- @node: observed_strictHorizon_emptyRisk_probability_tendsto_zero
lemma observed_strictHorizon_emptyRisk_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s | riskSet a s t = 0})
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  obtain ⟨q, hq, hlim⟩ := exists_observed_horizonRisk_localization c P hP a ht0 ht1
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  change riskSet a s t = 0 at hs
  change (riskSet a s t : ℝ) < (n : ℝ) * q
  rw [hs, Nat.cast_zero]
  exact mul_pos (by exact_mod_cast (show 0 < n by omega)) hq

/-- Removing the inverse-risk weight costs only the empty-risk probability.
The KM and risk factors remain dependent throughout this estimate. -/
-- @node: observed_KM_error_secondMoment_le_weighted_add_emptyRisk
lemma observed_KM_error_secondMoment_le_weighted_add_emptyRisk
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory, (deathKMLeft a s t - survival P a t) ^ 2
      ∂sampleLaw P n) ≤
    (∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) *
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) +
      (sampleLaw P n).real {s | riskSet a s t = 0} := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := fun s : Fin n → ObsHistory => deathKMLeft a s t - survival P a t
  let X := fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t
  let Z : Set (Fin n → ObsHistory) := {s | riskSet a s t = 0}
  have hE : Measurable E := by dsimp [E]; fun_prop
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hZ : MeasurableSet Z :=
    measurableSet_eq_fun ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const
  have hb (s : Fin n → ObsHistory) : E s ^ 2 ≤ 1 := by
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht
    have hs0 := Real.exp_pos (-c.dMax)
    dsimp [E]
    nlinarith [hk.1, hk.2, hs.1, hs.2]
  have hEi : Integrable (fun s => E s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hE.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E s))] using hb s
  have hXE : Integrable (fun s => X s * E s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hX.mul (hE.pow_const 2)).aestronglyMeasurable n
    filter_upwards [] with s
    have hi := recurrence_invRisk_mem_Icc a s t
    change |(n : ℝ) * invRisk a s t * E s ^ 2| ≤ n
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hi.1) (sq_nonneg _))]
    calc
      _ ≤ (n : ℝ) * 1 * 1 := by
        gcongr
        · exact hi.2
        · exact hb s
      _ = _ := by ring
  have hZi : Integrable (Z.indicator (fun _ => (1 : ℝ))) (sampleLaw P n) :=
    (integrable_const 1).indicator hZ
  calc
    _ ≤ ∫ s, X s * E s ^ 2 + Z.indicator (fun _ => (1 : ℝ)) s
        ∂sampleLaw P n := by
      apply integral_mono hEi (hXE.add hZi)
      intro s
      change E s ^ 2 ≤ X s * E s ^ 2 + Z.indicator (fun _ => (1 : ℝ)) s
      by_cases hz : s ∈ Z
      · rw [Set.indicator_of_mem hz]
        have hx0 : 0 ≤ X s := mul_nonneg (Nat.cast_nonneg _) (recurrence_invRisk_mem_Icc a s t).1
        nlinarith [sq_nonneg (E s), hb s]
      · rw [Set.indicator_of_notMem hz, add_zero]
        exact le_mul_of_one_le_left (sq_nonneg _) (one_le_scaledInvRisk_of_nonempty a s t hz)
    _ = _ := by
      rw [integral_add hXE hZi, integral_indicator hZ]
      simp only [integral_const, smul_eq_mul, mul_one]
      simp [X, E, Z, measureReal_def]

/-- The ordinary KM left limit is consistent in second mean at every strict
horizon, derived from the dependent weighted second moment and empty-risk limit. -/
-- @node: observed_KM_error_secondMoment_tendsto_zero
lemma observed_KM_error_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => observed_KM_error_secondMoment_le_weighted_add_emptyRisk c P hP a n ⟨ht0, ht1.le⟩)
  simpa only [add_zero] using
    (DeathCP.observed_integral_scaledInvRisk_KM_error_sq_tendsto_zero c P hP a ht0 ht1).add
      (observed_strictHorizon_emptyRisk_probability_tendsto_zero c P hP a ht0 ht1)

/-- The KM left limit converges in probability under the actual observed law. -/
-- @node: observed_KM_probability_tendsto_zero
lemma observed_KM_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |deathKMLeft a s t - survival P a t|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (by simpa only [zero_div] using
      (observed_KM_error_secondMoment_tendsto_zero c P hP a ht0 ht1).div_const (ε ^ 2))
  intro n
  have hm : Measurable (fun s : Fin n → ObsHistory => deathKMLeft a s t - survival P a t) := by
    fun_prop
  have hi : Integrable (fun s : Fin n → ObsHistory =>
      (deathKMLeft a s t - survival P a t) ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory => sq_nonneg
      (deathKMLeft a s t - survival P a t))) hi (ε ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [mul_comm]
  apply (mul_le_mul_of_nonneg_left (measureReal_mono (show
      {s : Fin n → ObsHistory | ε < |deathKMLeft a s t - survival P a t|} ⊆
      {s | ε ^ 2 ≤ (deathKMLeft a s t - survival P a t) ^ 2} from ?_) (by finiteness))
      (sq_nonneg ε)).trans
  · simpa only [mul_comm] using hmarkov
  · intro s hs
    change ε < |deathKMLeft a s t - survival P a t| at hs
    change ε ^ 2 ≤ (deathKMLeft a s t - survival P a t) ^ 2
    nlinarith [sq_abs (deathKMLeft a s t - survival P a t)]

/-- The KM error is jointly integrable in square over the entire study window.
The survival function is extended measurably only for this integration step. -/
-- @node: observed_KM_error_sq_integrable_prod
lemma observed_KM_error_sq_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - g p.2) ^ 2) :=
    ((measurable_recurrenceDeathKMLeft_joint a).sub (hg.comp measurable_snd)).pow_const 2
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1)), p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  have heq : (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - g p.2) ^ 2) =ᵐ[
        (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) 1))]
      (fun p => (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2) := by
    filter_upwards [htprod] with p hp
    simp only [g, Set.piecewise, if_pos hp]
  apply Integrable.congr _ heq
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [htprod] with p hp
  simp only [g, Set.piecewise, if_pos hp, Real.norm_eq_abs, abs_pow, sq_abs]
  have hk := deathKMLeft_mem_Icc a p.1 p.2
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a hp
  nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]

/-- Dominated convergence upgrades strict-horizon KM second-mean convergence
to integrated second-mean convergence through the endpoint. No endpoint
retention bound is needed because both survival functions are bounded by one. -/
-- @node: observed_KM_integrated_error_secondMoment_tendsto_zero
lemma observed_KM_integrated_error_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Icc (0 : ℝ) 1, (deathKMLeft a s t - survival P a t) ^ 2)
      ∂sampleLaw P n) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hi (n : ℕ) := observed_KM_error_sq_integrable_prod c P hP a n
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := fun n t => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => (hi n).integral_prod_right.aestronglyMeasurable) (integrable_const 1)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Icc, (hi n).prod_left_ae] with t ht hit
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
      calc
        _ ≤ ∫ _s : Fin n → ObsHistory, (1 : ℝ) ∂sampleLaw P n := by
          apply integral_mono hit (integrable_const 1)
          intro s
          have hk := deathKMLeft_mem_Icc a s t
          have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht
          nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
        _ = 1 := by simp)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc (0 : ℝ) 1)).ae_ne (1 : ℝ)] with t ht htne
      exact observed_KM_error_secondMoment_tendsto_zero c P hP a ht.1
        (lt_of_le_of_ne ht.2 htne))
  simp only [integral_zero] at h
  convert h using 1
  funext n
  exact integral_integral_swap (hi n)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

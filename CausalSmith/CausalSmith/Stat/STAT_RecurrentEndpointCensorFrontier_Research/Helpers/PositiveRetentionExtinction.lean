module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskSet

/-!
# Extinction energy under positive horizon retention

Roadmap (8)--(12) and (27): the zero-cutoff extinction correction is supported
on empty terminal risk. The probability bound supplies an exponential second
moment envelope and negligibility at root-n scale, without endpoint smoothness.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The zero-cutoff remaining target has the ordinary remaining-horizon envelope,
using only the two hazard bands. -/
-- @node: positiveRetention_remainingTarget_zero_abs_le
lemma positiveRetention_remainingTarget_zero_abs_le
    (c : ClassConstants) (P : SubjectLaw) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    |remainingTarget c P a 0 u| ≤ c.lambdaMax * (1 - u) := by
  simp only [remainingTarget, continuationWeight, if_true, sub_zero, one_mul]
  have hb : ‖∫ t in u..1, survival P a t * P.lam a t‖ ≤
      c.lambdaMax * |1 - u| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hu.2] at ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1.le, ht.2⟩
    have hs := (survival_bounds_of_deathBounds c P hDeathBounds a ht01).2
    have hl := hRecurBounds a t ht01
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < survival P a t from Real.exp_pos _),
      abs_of_nonneg (c.lambdaMin_pos.le.trans hl.1)]
    exact (mul_le_mul_of_nonneg_right hs (c.lambdaMin_pos.le.trans hl.1)).trans
      (by simpa using hl.2)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu.2)] using hb

/-- The ordinary extinction correction is zero unless terminal risk is empty;
its nonzero values obey the deterministic survival and recurrence envelope. -/
-- @node: positiveRetention_extinctionError_zero_abs_le_indicator
lemma positiveRetention_extinctionError_zero_abs_le_indicator
    (c : ClassConstants) (P : SubjectLaw) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).treatment = a → 0 ≤ (s i).exit ∧ (s i).exit ≤ 1) :
    |extinctionError c P a s 0| ≤
      if riskSet a s 1 = 0 then Real.exp c.dMax * c.lambdaMax else 0 := by
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  by_cases he : extinction a s < 1
  · have he0 := extinction_nonneg_of_exit_bounds a s hExit
    have hs0 : 0 < survival P a (extinction a s) := Real.exp_pos _
    have hs := (survival_bounds_of_deathBounds c P hDeathBounds a ⟨he0, he.le⟩).1
    have hinv : (survival P a (extinction a s))⁻¹ ≤ Real.exp c.dMax := by
      simpa only [Real.exp_neg, inv_inv] using
        (inv_le_inv₀ hs0 (Real.exp_pos (-c.dMax))).2 hs
    have hkm := deathKM_mem_Icc a s (extinction a s)
    have hr := positiveRetention_remainingTarget_zero_abs_le c P hRecurBounds
      hDeathBounds a ⟨he0, he.le⟩
    have hr' : |remainingTarget c P a 0 (extinction a s)| ≤ c.lambdaMax :=
      hr.trans (by nlinarith)
    rw [if_pos (riskSet_zero_after_extinction a s 1 zero_le_one le_rfl he),
      extinctionError, sub_zero, if_pos he, abs_mul, abs_div,
      abs_of_nonneg hkm.1, abs_of_pos hs0, div_eq_mul_inv]
    calc
      _ ≤ (1 * Real.exp c.dMax) * c.lambdaMax :=
        mul_le_mul (mul_le_mul hkm.2 hinv (inv_nonneg.mpr hs0.le) zero_le_one)
          hr' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [extinctionError, sub_zero, if_neg he, abs_zero]
    split_ifs <;> positivity

/-- The squared extinction correction has an almost-sure terminal indicator
bound, including empty treatment arms. -/
-- @node: positiveRetention_extinctionError_zero_sq_le_indicator_ae
lemma positiveRetention_extinctionError_zero_sq_le_indicator_ae
    (c : ClassConstants) (P : SubjectLaw) (hDeath : DeathHazard P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (a : Arm) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, extinctionError c P a s 0 ^ 2 ≤
      ({s : Fin n → ObsHistory | riskSet a s 1 = 0}).indicator
        (fun _ => (Real.exp c.dMax * c.lambdaMax) ^ 2) s := by
  filter_upwards [sample_exit_nonneg P hDeath n, sample_exit_le_one P n] with s hs0 hs1
  have hb := positiveRetention_extinctionError_zero_abs_le_indicator c P hRecurBounds
    hDeathBounds a s (fun i _ => ⟨hs0 i, hs1 i⟩)
  have hB : 0 ≤ Real.exp c.dMax * c.lambdaMax :=
    mul_nonneg (Real.exp_nonneg _) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  by_cases hz : riskSet a s 1 = 0
  · simpa [hz, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (by simpa [hz] using hb)
  · have he : extinctionError c P a s 0 = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa [hz] using hb) (abs_nonneg _))
    simp [hz, he]

/-- Averaging the terminal-risk indicator proves the exponential extinction
second-moment bound in the positive-retention roadmap. -/
-- @node: positiveRetention_extinctionError_zero_secondMoment_le_exp
lemma positiveRetention_extinctionError_zero_secondMoment_le_exp
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    (∫ s : Fin n → ObsHistory, extinctionError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      (Real.exp c.dMax * c.lambdaMax) ^ 2 *
        Real.exp (-(n * (c.pMin * Real.exp (-c.dMax) * c.Ghor))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := {s : Fin n → ObsHistory | riskSet a s 1 = 0}
  let B := (Real.exp c.dMax * c.lambdaMax) ^ 2
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const
  calc
    _ ≤ ∫ s, E.indicator (fun _ => B) s ∂sampleLaw P n :=
      integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _))
        ((integrable_const B).indicator hE)
        (positiveRetention_extinctionError_zero_sq_le_indicator_ae c P hDeath
          hRecurBounds hDeathBounds a n)
    _ = (sampleLaw P n).real E * B := by rw [integral_indicator_const B hE]; rfl
    _ ≤ Real.exp (-(n * (c.pMin * Real.exp (-c.dMax) * c.Ghor))) * B :=
      mul_le_mul_of_nonneg_right
        (positiveRetention_riskSet_zero_probability_le_exp c P hRandom hAssignment
          hOverlap hDeath hCensor hDeathBounds hHorizon a n (by norm_num)) (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- The nonnegative extinction second moment obeys the same envelope.
This bound controls the outer integral even before any measurability transport. -/
-- @node: positiveRetention_extinctionError_zero_lintegral_le_exp
lemma positiveRetention_extinctionError_zero_lintegral_le_exp
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    (∫⁻ s : Fin n → ObsHistory, ENNReal.ofReal (extinctionError c P a s 0 ^ 2)
      ∂sampleLaw P n) ≤
      ENNReal.ofReal ((Real.exp c.dMax * c.lambdaMax) ^ 2 *
        Real.exp (-(n * (c.pMin * Real.exp (-c.dMax) * c.Ghor)))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := {s : Fin n → ObsHistory | riskSet a s 1 = 0}
  let B := (Real.exp c.dMax * c.lambdaMax) ^ 2
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const
  calc
    _ ≤ ∫⁻ s, E.indicator (fun _ => ENNReal.ofReal B) s ∂sampleLaw P n := by
      apply lintegral_mono_ae
      filter_upwards [positiveRetention_extinctionError_zero_sq_le_indicator_ae
        c P hDeath hRecurBounds hDeathBounds a n] with s hs
      have hb := ENNReal.ofReal_le_ofReal hs
      by_cases hz : s ∈ E
      · simpa [E, B, hz, Set.indicator_of_mem] using hb
      · have hz' : riskSet a s 1 ≠ 0 := hz
        simpa [E, B, hz'] using hb
    _ = ENNReal.ofReal B * (sampleLaw P n) E := lintegral_indicator_const hE _
    _ = ENNReal.ofReal (B * (sampleLaw P n).real E) := by
      rw [ENNReal.ofReal_mul (sq_nonneg _), measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (positiveRetention_riskSet_zero_probability_le_exp c P hRandom hAssignment
          hOverlap hDeath hCensor hDeathBounds hHorizon a n (by norm_num)) (sq_nonneg _))

/-- The exponential extinction moment is bounded by an explicit C/n for
all positive sample sizes, as required by the finite-sample risk assembly. -/
-- @node: positiveRetention_extinctionError_zero_secondMoment_le_inv_sampleSize
lemma positiveRetention_extinctionError_zero_secondMoment_le_inv_sampleSize
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, extinctionError c P a s 0 ^ 2 ∂sampleLaw P n) ≤
      ((Real.exp c.dMax * c.lambdaMax) ^ 2 * Real.exp (-1) /
        (c.pMin * Real.exp (-c.dMax) * c.Ghor)) / n := by
  let q := c.pMin * Real.exp (-c.dMax) * c.Ghor
  let B := (Real.exp c.dMax * c.lambdaMax) ^ 2
  have hq : 0 < q := mul_pos (mul_pos c.pMin_pos (Real.exp_pos _)) c.Ghor_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp (-(n * q)) ≤ Real.exp (-1) / (n * q) :=
    (le_div_iff₀ (mul_pos hnR hq)).2
      (by simpa [mul_comm] using Real.mul_exp_neg_le_exp_neg_one ((n : ℝ) * q))
  calc
    _ ≤ B * Real.exp (-(n * q)) :=
      positiveRetention_extinctionError_zero_secondMoment_le_exp c P hRandom hAssignment
        hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a n
    _ ≤ B * (Real.exp (-1) / (n * q)) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by dsimp [B, q]; ring

/-- Terminal empty risk alone implies negligibility of the ordinary extinction
correction at root-n scale, without needing a shrinking endpoint horizon. -/
-- @node: positiveRetention_extinctionError_rootn_probability_tendsto_zero
lemma positiveRetention_extinctionError_rootn_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hOverlap : TreatmentOverlap c P)
    (hDeath : DeathHazard P) (hCensor : IndependentCensoring P)
    (hRecurBounds : RecurrenceBounds c P) (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Real.sqrt n * extinctionError c P a s 0|}) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (positiveRetention_terminal_emptyRisk_probability_tendsto_zero c P hRandom
      hAssignment hOverlap hDeath hCensor hDeathBounds hHorizon a)
  intro n
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  filter_upwards [sample_exit_nonneg P hDeath n, sample_exit_le_one P n] with s hs0 hs1
  intro hs
  change ε < |Real.sqrt n * extinctionError c P a s 0| at hs
  change riskSet a s 1 = 0
  by_contra hz
  have hb := positiveRetention_extinctionError_zero_abs_le_indicator c P hRecurBounds
    hDeathBounds a s (fun i _ => ⟨hs0 i, hs1 i⟩)
  have he : extinctionError c P a s 0 = 0 :=
    abs_eq_zero.mp (le_antisymm (by simpa [hz] using hb) (abs_nonneg _))
  rw [he, mul_zero, abs_zero] at hs
  exact (not_lt_of_ge hε.le) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

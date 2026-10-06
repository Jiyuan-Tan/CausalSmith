module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleCentered
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# Fixed-horizon integrated death KM coefficient energy

This module supplies the observed-sample inverse-risk moment bounds and the
strict-left Kaplan--Meier null-boundary bridge used in fixed-horizon energy
control. Young's inequality yields a vanishing mixed KM/inverse-risk moment
without independence; an exact coefficient split isolates the remaining
centered inverse-risk term.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Adding a time at which there is no death jump does not change the death
Kaplan--Meier product. -/
lemma deathKMLeft_eq_deathKM_of_deathJump_eq_zero {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) (hjump : deathJump a s t = 0) :
    deathKMLeft a s t = deathKM a s t := by
  classical
  unfold deathKMLeft deathKM
  apply Finset.prod_subset
  · intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, hu.2.le⟩
  · intro u hu hnot
    simp only [Finset.mem_filter] at hu
    have hut : u = t := le_antisymm hu.2 (le_of_not_gt (by
      intro hut
      exact hnot (Finset.mem_filter.mpr ⟨hu.1, hut⟩)))
    simp [hut, hjump]

/-- At a fixed deterministic time, strict-left and right-continuous death KM
agree almost surely under the observed iid law. -/
lemma deathKMLeft_eq_deathKM_ae_fixed
    (P : SubjectLaw) (hDeath : DeathHazard P) (a : Arm) (n : ℕ) (t : ℝ) :
    ∀ᵐ s ∂sampleLaw P n, deathKMLeft a s t = deathKM a s t := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hObs : ∀ᵐ o ∂observedLaw P,
      ¬ (o.treatment = a ∧ o.deathInd ∧ o.exit = t) := by
    apply ae_iff.mpr
    simpa only [not_not] using observed_death_exit_fixed_null P hDeath a t
  have hall : ∀ᵐ s ∂sampleLaw P n, ∀ i : Fin n,
      ¬ ((s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = t) := by
    rw [Filter.eventually_all]
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n ↦ observedLaw P) (i := i)) hObs
  filter_upwards [hall] with s hs
  apply deathKMLeft_eq_deathKM_of_deathJump_eq_zero
  unfold deathJump
  apply Finset.sum_eq_zero
  intro i _
  simp [hs i]

/-- The scaled observed inverse risk has a uniform second-moment bound at a
fixed time. -/
lemma observed_integral_scaledInvRisk_sq_le
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    {T t : ℝ} (hT1 : T < 1) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) ^ 2
      ∂sampleLaw P n) ≤
      6 / (P.p a * survival P a t * retention P a t) ^ 2 := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  let q : ℝ := P.p a * survival P a t * retention P a t
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (mul_pos (c.pMin_pos.trans_le (hP.treatmentOverlap a))
      (Real.exp_pos _)) (retention_pos_of_modelClass c P hP a t ht.1
        (ht.2.trans_lt hT1))
  have hmass : (observedLaw P).real A = q := by
    simpa [A, q] using observed_arm_risk_probability P hP a
      ⟨ht.1, ht.2.trans hT1.le⟩
  let F : ℕ → ℝ := fun k ↦ (if 0 < k then (n : ℝ) / k else 0) ^ 2
  have hpath (s : Fin n → ObsHistory) :
      ((n : ℝ) * invRisk a s t) ^ 2 =
        F (Finset.univ.filter fun i ↦ s i ∈ A).card := by
    unfold invRisk riskSet
    dsimp [F, A]
    by_cases hz : (Finset.univ.filter fun i : Fin n ↦
        (s i).treatment = a ∧ t ≤ (s i).exit).card = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, div_eq_mul_inv]
  simp_rw [hpath]
  have heq := integral_eventCount_eq_binomial (observedLaw P) A hA n F
  have hs := binomial_totalized_inverse_count_sq_le n q hq (by
    rw [← hmass]
    exact measureReal_le_one)
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n ((observedLaw P).real A) k * F k := by
      change (∫ z : Fin n → ObsHistory,
        F (Finset.univ.filter fun i ↦ z i ∈ A).card
        ∂Measure.pi fun _ : Fin n ↦ observedLaw P) = _
      simpa only [A] using heq
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n q k * (if 0 < k then (k : ℝ)⁻¹ ^ 2 else 0) *
          (n : ℝ) ^ 2 := by
      rw [hmass]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : 0 < k <;> simp [F, hk0]
      field_simp
    _ ≤ (6 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * q ^ 2)) *
        (n : ℝ) ^ 2 := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ ≤ 6 / q ^ 2 := by
      have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
      have hnle : (n : ℝ) ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      have hden : 0 < ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by positivity
      calc
        _ = ((n : ℝ) ^ 2 /
            (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) *
              (6 / q ^ 2) := by field_simp
        _ ≤ 1 * (6 / q ^ 2) := mul_le_mul_of_nonneg_right
          ((div_le_one hden).2 hnle) (div_nonneg (by norm_num) hq2.le)
        _ = _ := one_mul _
    _ = _ := rfl

/-- The centered inverse-risk coefficient bound holds directly for the
observed at-risk count. -/
lemma observed_integral_riskFraction_scaledInvRisk_center_sq_le
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T t : ℝ} (hT1 : T < 1) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        (((n : ℝ) * invRisk a s t) -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2
      ∂sampleLaw P n) ≤
      5 / (((n + 1 : ℕ) : ℝ) *
        (P.p a * survival P a t * retention P a t) ^ 2) := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  let q : ℝ := P.p a * survival P a t * retention P a t
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (mul_pos (c.pMin_pos.trans_le (hP.treatmentOverlap a))
      (Real.exp_pos _)) (retention_pos_of_modelClass c P hP a t ht.1
        (ht.2.trans_lt hT1))
  have hmass : (observedLaw P).real A = q := by
    simpa [A, q] using observed_arm_risk_probability P hP a
      ⟨ht.1, ht.2.trans hT1.le⟩
  let F : ℕ → ℝ := fun k ↦ ((k : ℝ) / n) *
    ((if 0 < k then (n : ℝ) / k else 0) - 1 / q) ^ 2
  have hpath (s : Fin n → ObsHistory) :
      ((riskSet a s t : ℝ) / n) *
          (((n : ℝ) * invRisk a s t) - 1 / q) ^ 2 =
        F (Finset.univ.filter fun i ↦ s i ∈ A).card := by
    unfold invRisk riskSet
    dsimp [F, A]
    by_cases hz : (Finset.univ.filter fun i : Fin n ↦
        (s i).treatment = a ∧ t ≤ (s i).exit).card = 0
    · simp [hz]
    · simp [hz, Nat.pos_of_ne_zero hz, div_eq_mul_inv]
  simp_rw [show P.p a * survival P a t * retention P a t = q by rfl, hpath]
  have heq := integral_eventCount_eq_binomial (observedLaw P) A hA n F
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        binomialWeight n ((observedLaw P).real A) k * F k := by
      change (∫ z : Fin n → ObsHistory,
        F (Finset.univ.filter fun i ↦ z i ∈ A).card
        ∂Measure.pi fun _ : Fin n ↦ observedLaw P) = _
      simpa only [A] using heq
    _ = ∑ k ∈ Finset.range (n + 1), binomialWeight n q k * F k := by
      rw [hmass]
    _ ≤ 5 / (((n + 1 : ℕ) : ℝ) * q ^ 2) := by
      dsimp [F]
      simpa [mul_assoc] using
        (binomial_weighted_scaledInverse_center_sq_le n q hn hq
          (by rw [← hmass]; exact measureReal_le_one))

/-- Young's inequality controls the KM/inverse-risk product without an
independence assumption; the KM error lies in the unit interval. -/
-- @node: km_error_weight_young
lemma km_error_weight_young {z X δ : ℝ} (hz : z ^ 2 ≤ 1) (hδ : 0 < δ) :
    z ^ 2 * X ≤ δ * X ^ 2 + z ^ 2 / δ := by
  have hz4 : (z ^ 2) ^ 2 ≤ z ^ 2 := by nlinarith [sq_nonneg z]
  apply (mul_le_mul_iff_right₀ hδ).mp
  have hs := sq_nonneg (δ * X - z ^ 2)
  have heq : δ * (δ * X ^ 2 + z ^ 2 / δ) =
      δ ^ 2 * X ^ 2 + z ^ 2 := by field_simp <;> ring
  rw [heq]
  nlinarith [sq_nonneg (δ * X)]

/-- The left-limit KM mean-square bound uses the deterministic-time null
boundary bridge, so no jump-at-the-evaluation-time term is introduced. -/
-- @node: deathKMLeft_secondMoment_le_fixedRate
lemma deathKMLeft_secondMoment_le_fixedRate
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory,
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) ≤
      (2 / ((n : ℝ) *
        (c.pMin * retention P a t * Real.exp (-c.dMax)))) *
        ∫ u in Set.Icc 0 t,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a u ∂volume +
      1 / ((n : ℝ) *
        (c.pMin * retention P a t * Real.exp (-c.dMax))) := by
  rw [integral_congr_ae (by
    filter_upwards [deathKMLeft_eq_deathKM_ae_fixed P hP.deathHazard a n t]
      with s hs
    rw [hs])]
  exact deathKM_secondMoment_le_fixedRate c P hP a hn ht0 ht1

/-- A fixed-time weighted KM error is bounded by the inverse-risk second
moment and the KM mean-square error through Young's inequality. -/
-- @node: observed_integral_scaledInvRisk_KM_error_sq_le
lemma observed_integral_scaledInvRisk_KM_error_sq_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hδ : 0 < δ) :
    (∫ s : Fin n → ObsHistory,
      ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) ≤
      δ * (6 / (P.p a * survival P a t * retention P a t) ^ 2) +
      ((2 / ((n : ℝ) *
        (c.pMin * retention P a t * Real.exp (-c.dMax)))) *
        ∫ u in Set.Icc 0 t,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a u ∂volume +
      1 / ((n : ℝ) *
        (c.pMin * retention P a t * Real.exp (-c.dMax)))) / δ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let X := fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t
  let E := fun s : Fin n → ObsHistory => deathKMLeft a s t - survival P a t
  have hX : Measurable X := by
    dsimp [X]
    exact measurable_const.mul ((measurable_recurrenceInvRisk_joint a).comp
      (measurable_id.prodMk measurable_const))
  have hE : Measurable E := by
    dsimp [E]
    exact ((measurable_recurrenceDeathKMLeft_joint a).comp
      (measurable_id.prodMk measurable_const)).sub measurable_const
  have hEbound (s : Fin n → ObsHistory) : E s ^ 2 ≤ 1 := by
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    have hs0 := Real.exp_pos (-c.dMax)
    dsimp [E]
    have he : |deathKMLeft a s t - survival P a t| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hk.1, hk.2, hs.1, hs.2],
        by linarith [hk.1, hk.2, hs.1, hs.2]⟩
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 he
  have hEi : Integrable (fun s => E s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hE.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E s))] using hEbound s
  have hXi : Integrable (fun s => X s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable ((n : ℝ) ^ 2)
    filter_upwards [] with s
    have hi : 0 ≤ invRisk a s t ∧ invRisk a s t ≤ 1 := by
      unfold invRisk
      split_ifs with hz
      · norm_num
      · have hr : (1 : ℝ) ≤ riskSet a s t := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        exact ⟨inv_nonneg.mpr (by positivity), inv_le_one_of_one_le₀ hr⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X s))]
    dsimp [X]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hi.2 hn0, mul_nonneg hn0 hi.1]
  calc
    _ ≤ ∫ s, δ * X s ^ 2 + E s ^ 2 / δ ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => by
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by
          unfold invRisk; split_ifs <;> positivity)) (sq_nonneg _)))
        ((hXi.const_mul δ).add (hEi.div_const δ))
        (Filter.Eventually.of_forall (fun s => by
          simpa [X, E, mul_comm] using km_error_weight_young (hEbound s) hδ))
    _ = δ * (∫ s, X s ^ 2 ∂sampleLaw P n) +
        (∫ s, E s ^ 2 ∂sampleLaw P n) / δ := by
      rw [integral_add (hXi.const_mul δ) (hEi.div_const δ),
        integral_const_mul, integral_div]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (observed_integral_scaledInvRisk_sq_le P hP a ht1 ⟨ht0, le_rfl⟩) hδ.le)
      (div_le_div_of_nonneg_right
        (deathKMLeft_secondMoment_le_fixedRate c P hP a hn ht0 ht1) hδ.le)

/-- Choosing the Young parameter as `n^(-1/2)` gives an explicit vanishing
fixed-time mixed coefficient energy. The bound does not factor dependent
random quantities. -/
-- @node: observed_integral_scaledInvRisk_KM_error_sq_le_sqrtRate
lemma observed_integral_scaledInvRisk_KM_error_sq_le_sqrtRate
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory,
      ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) ≤
      (6 / (P.p a * survival P a t * retention P a t) ^ 2 +
        (2 * (∫ u in Set.Icc 0 t,
          (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a u ∂volume) + 1) /
          (c.pMin * retention P a t * Real.exp (-c.dMax))) / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hq : 0 < c.pMin * retention P a t * Real.exp (-c.dMax) :=
    mul_pos (mul_pos c.pMin_pos
      (retention_pos_of_modelClass c P hP a t ht0 ht1)) (Real.exp_pos _)
  have hb := observed_integral_scaledInvRisk_KM_error_sq_le c P hP a hn
    ht0 ht1 (one_div_pos.mpr hs)
  refine hb.trans_eq ?_
  have hsq := Real.sq_sqrt hnR.le
  field_simp
  rw [hsq]
  ring

/-- The mixed coefficient error tends to zero at each strict deterministic
horizon, as required before time integration and removal of the horizon. -/
-- @node: observed_integral_scaledInvRisk_KM_error_sq_tendsto_zero
lemma observed_integral_scaledInvRisk_KM_error_sq_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    integral_nonneg (fun s => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (by
        unfold invRisk; split_ifs <;> positivity)) (sq_nonneg _))))
    (Filter.eventually_atTop.2 ⟨1, fun n hn =>
      observed_integral_scaledInvRisk_KM_error_sq_le_sqrtRate c P hP a
        (by omega) ht0 ht1⟩)
  have hi := (Real.tendsto_sqrt_atTop.comp
    tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def, Pi.inv_apply] using
    (tendsto_const_nhds.mul hi)

/-- Splitting the observable recurrence coefficient around its oracle
separates the dependent KM error from the centered inverse risk. Exact
zero-risk cancellation supplies the multiplier of the KM term. -/
-- @node: observed_KM_oracle_coefficient_energy_split
lemma observed_KM_oracle_coefficient_energy_split
    (P : SubjectLaw) (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) (t : ℝ) :
    ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ≤
      2 * ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2 +
      2 * survival P a t ^ 2 * ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
  have hcancel : survival P a t /
      (P.p a * survival P a t * retention P a t) =
      1 / (P.p a * retention P a t) := by
    rw [show P.p a * survival P a t * retention P a t =
      survival P a t * (P.p a * retention P a t) by ring]
    simpa only [mul_one] using
      (mul_div_mul_left (1 : ℝ) (P.p a * retention P a t) hs)
  let U := (n : ℝ) * invRisk a s t * (deathKMLeft a s t - survival P a t)
  let V := survival P a t * ((n : ℝ) * invRisk a s t -
    1 / (P.p a * survival P a t * retention P a t))
  have hsplit : (n : ℝ) * deathKMLeft a s t * invRisk a s t -
      1 / (P.p a * retention P a t) = U + V := by
    dsimp [U, V]
    simp only [mul_sub, mul_one_div]
    rw [hcancel]
    ring
  have hsq : (U + V) ^ 2 ≤ 2 * U ^ 2 + 2 * V ^ 2 := by
    nlinarith [sq_nonneg (U - V)]
  have hweight : 0 ≤ (riskSet a s t : ℝ) / n := by positivity
  have hidentity : ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * invRisk a s t) ^ 2 = (n : ℝ) * invRisk a s t := by
    by_cases hz : riskSet a s t = 0
    · simp [invRisk, hz]
    · have hr : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
      simp only [invRisk, hz, ↓reduceIte]
      field_simp
  rw [hsplit]
  calc
    _ ≤ ((riskSet a s t : ℝ) / n) * (2 * U ^ 2 + 2 * V ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hweight
    _ = _ := by
      dsimp [U, V]
      linear_combination 2 * (deathKMLeft a s t - survival P a t) ^ 2 * hidentity

/-- Any bounded measurable sample coefficient has integrable risk-weighted
square; the risk count is bounded by the sample size. -/
-- @node: integrable_observed_risk_weighted_sq
lemma integrable_observed_risk_weighted_sq
    (P : SubjectLaw) (a : Arm) {n : ℕ} (t : ℝ)
    (f : (Fin n → ObsHistory) → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ s, |f s| ≤ B) :
    Integrable (fun s => ((riskSet a s t : ℝ) / n) * (f s) ^ 2)
      (sampleLaw P n) := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hr : Measurable (fun s : Fin n → ObsHistory => (riskSet a s t : ℝ)) := by
    fun_prop
  apply Integrable.of_bound ((hr.div_const _).mul (hf.pow_const 2)).aestronglyMeasurable
    (((n : ℝ) / n) * B ^ 2)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))]
  apply mul_le_mul
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hc : riskSet a s t ≤ n := by
      simpa [riskSet] using (Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun i => (s i).treatment = a ∧ t ≤ (s i).exit))
    exact_mod_cast hc
  · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (hb s)
  · positivity
  · positivity

/-- The scaled inverse-risk coefficient is bounded pathwise, including
empty risk sets. -/
-- @node: scaledInvRisk_mem_Icc
lemma scaledInvRisk_mem_Icc {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) :
    (n : ℝ) * invRisk a s t ∈ Set.Icc 0 (n : ℝ) := by
  have hi : invRisk a s t ∈ Set.Icc (0 : ℝ) 1 := by
    unfold invRisk
    split_ifs with hz
    · simp
    · have hr : (1 : ℝ) ≤ riskSet a s t := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      exact ⟨inv_nonneg.mpr (by positivity), inv_le_one_of_one_le₀ hr⟩
  exact ⟨mul_nonneg (Nat.cast_nonneg n) hi.1,
    by simpa using mul_le_mul_of_nonneg_left hi.2 (Nat.cast_nonneg n)⟩

/-- Combining the dependent KM error and centered inverse-risk terms gives
the complete fixed-time oracle coefficient energy bound. -/
-- @node: observed_KM_oracle_coefficient_energy_le
lemma observed_KM_oracle_coefficient_energy_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
      ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
        1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n) ≤
      2 * (∫ s : Fin n → ObsHistory, ((n : ℝ) * invRisk a s t) *
        (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) +
      2 * survival P a t ^ 2 *
        (5 / (((n + 1 : ℕ) : ℝ) *
          (P.p a * survival P a t * retention P a t) ^ 2)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let X := fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t
  let E := fun s : Fin n → ObsHistory => deathKMLeft a s t - survival P a t
  let Q := 1 / (P.p a * survival P a t * retention P a t)
  have hX : Measurable X := by
    dsimp [X]
    fun_prop
  have hE : Measurable E := by
    dsimp [E]
    fun_prop
  have he (s : Fin n → ObsHistory) : E s ^ 2 ≤ 1 := by
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht0, ht1.le⟩
    have hs0 := Real.exp_pos (-c.dMax)
    dsimp [E]
    have habs : |deathKMLeft a s t - survival P a t| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hk.1, hk.2, hs.1, hs.2],
        by linarith [hk.1, hk.2, hs.1, hs.2]⟩
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 habs
  have hi : Integrable (fun s => X s * E s ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (hX.mul (hE.pow_const 2)).aestronglyMeasurable n
    filter_upwards [] with s
    have hx := scaledInvRisk_mem_Icc a s t
    change |X s * E s ^ 2| ≤ (n : ℝ)
    rw [abs_of_nonneg (mul_nonneg hx.1 (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (he s) hx.1).trans (by simpa [X] using hx.2)
  have hj : Integrable (fun s : Fin n → ObsHistory =>
      ((riskSet a s t : ℝ) / n) * (X s - Q) ^ 2) (sampleLaw P n) := by
    apply integrable_observed_risk_weighted_sq P a t (fun s => X s - Q)
      (hX.sub measurable_const) (by positivity : 0 ≤ (n : ℝ) + |Q|)
    intro s
    have hxabs : |X s| ≤ (n : ℝ) := by
      simpa only [X, abs_of_nonneg (scaledInvRisk_mem_Icc a s t).1] using
        (scaledInvRisk_mem_Icc a s t).2
    exact (abs_sub _ _).trans (add_le_add hxabs (le_refl |Q|))
  calc
    _ ≤ ∫ s, 2 * (X s * E s ^ 2) +
        (2 * survival P a t ^ 2) *
          (((riskSet a s t : ℝ) / n) * (X s - Q) ^ 2) ∂sampleLaw P n := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun s => by positivity))
        ((hi.const_mul 2).add (hj.const_mul _))
      exact Filter.Eventually.of_forall (fun s => by
        simpa [X, E, Q, mul_assoc] using
          observed_KM_oracle_coefficient_energy_split P a hn s t)
    _ = 2 * (∫ s, X s * E s ^ 2 ∂sampleLaw P n) +
        (2 * survival P a t ^ 2) *
          (∫ s : Fin n → ObsHistory,
            ((riskSet a s t : ℝ) / n) * (X s - Q) ^ 2 ∂sampleLaw P n) := by
      rw [integral_add (hi.const_mul 2) (hj.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      exact mul_le_mul_of_nonneg_left
        (observed_integral_riskFraction_scaledInvRisk_center_sq_le P hP a hn
          ht1 ⟨ht0, le_rfl⟩) (by positivity : 0 ≤ 2 * survival P a t ^ 2)

/-- Full fixed-time observable-to-oracle coefficient energy vanishes without
factoring the dependent KM and inverse-risk errors. -/
-- @node: observed_KM_oracle_coefficient_energy_tendsto_zero
lemma observed_KM_oracle_coefficient_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ s : Fin n → ObsHistory, ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2 ∂sampleLaw P n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    integral_nonneg (fun s => by positivity)))
    (Filter.eventually_atTop.2 ⟨1, fun n hn =>
      observed_KM_oracle_coefficient_energy_le c P hP a (by omega) ht0 ht1⟩)
  have hmix := (observed_integral_scaledInvRisk_KM_error_sq_tendsto_zero
    c P hP a ht0 ht1).const_mul 2
  have hinv := ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).comp (Filter.tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  have hcenter := hinv.const_mul
    (2 * survival P a t ^ 2 * (5 /
      (P.p a * survival P a t * retention P a t) ^ 2))
  convert hmix.add hcenter using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, mul_zero, add_zero]
  funext n
  simp only [Function.comp_def, Pi.inv_apply, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, mul_inv_rev]
  ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

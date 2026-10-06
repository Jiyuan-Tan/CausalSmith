module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleCompensator

/-!
# Inverse-risk compensator consistency

Roadmap (39): the deterministic death optional variation has compensator
n times inverse risk, without a KM factor. The binomial centered energy and
Young's inequality prove its pointwise convergence in mean. The zero-risk
convention is retained throughout.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Multiplication by the risk fraction cancels one scaled inverse-risk
factor, including the empty-risk and empty-sample cases. -/
-- @node: riskFraction_scaledInvRisk_sq_eq
lemma riskFraction_scaledInvRisk_sq_eq {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (t : ℝ) :
    ((riskSet a s t : ℝ) / n) * ((n : ℝ) * invRisk a s t) ^ 2 =
      (n : ℝ) * invRisk a s t := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hr : riskSet a s t = 0
  · simp [invRisk, hr]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hr' : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  simp only [invRisk, if_neg hr]
  field_simp

/-- The binomial centered inverse-risk energy vanishes at every time strictly
before the endpoint. -/
-- @node: observed_scaledInvRisk_center_energy_tendsto_zero
lemma observed_scaledInvRisk_center_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)) ^ 2 ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    integral_nonneg (fun s => by positivity)))
    (by filter_upwards [eventually_ge_atTop 1] with n hn
        exact DeathCP.observed_integral_riskFraction_scaledInvRisk_center_sq_le
          P hP a (by omega) ht1 ⟨ht0, le_rfl⟩)
  have hi := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  convert hi.const_mul (5 / (P.p a * survival P a t * retention P a t) ^ 2)
    using 1 <;> try simp only [mul_zero]
  funext n
  simp only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Young's inequality upgrades centered inverse-risk energy to convergence
in mean of the risk-weighted square difference. -/
-- @node: observed_scaledInvRisk_squared_difference_mean_tendsto_zero
lemma observed_scaledInvRisk_squared_difference_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * invRisk a s t) ^ 2 -
          (1 / (P.p a * survival P a t * retention P a t)) ^ 2| ∂sampleLaw P n)
      atTop (nhds 0) := by
  let q := P.p a * survival P a t * retention P a t
  let W := fun (n : ℕ) (s : Fin n → ObsHistory) => (riskSet a s t : ℝ) / n
  let A := fun (n : ℕ) (s : Fin n → ObsHistory) => (n : ℝ) * invRisk a s t
  let B := fun (n : ℕ) (_ : Fin n → ObsHistory) => 1 / q
  have he (n : ℕ) : Integrable (fun s => W n s * (A n s - B n s) ^ 2)
      (sampleLaw P n) := by
    apply DeathCP.integrable_observed_risk_weighted_sq P a t _ (by dsimp [A, B]; fun_prop)
      (B := (n : ℝ) + |1 / q|) (by positivity)
    intro s
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a s t).1]
      exact add_le_add (DeathCP.scaledInvRisk_mem_Icc a s t).2 (le_refl _))
  have hb (n : ℕ) : Integrable (fun s => W n s * B n s ^ 2) (sampleLaw P n) :=
    DeathCP.integrable_observed_risk_weighted_sq P a t _ measurable_const
      (abs_nonneg (1 / q)) (fun _ => le_rfl)
  have hm (n : ℕ) : Measurable (fun s => W n s * |A n s ^ 2 - B n s ^ 2|) := by
    dsimp [W, A, B]; fun_prop
  have hW (n : ℕ) (s : Fin n → ObsHistory) : 0 ≤ W n s := by dsimp [W]; positivity
  let V := q * (1 / q) ^ 2
  have hveq (n : ℕ) (hn : 0 < n) :
      (∫ s, W n s * B n s ^ 2 ∂sampleLaw P n) = V := by
    dsimp [W, B, V]
    rw [integral_mul_const, DeathCP.observed_integral_riskFraction_eq c P hP a hn
      ⟨ht0, ht1.le⟩]
  have hV : 0 ≤ V := by
    rw [← hveq 1 (by norm_num)]
    exact integral_nonneg (fun s => mul_nonneg (hW _ _) (sq_nonneg _))
  exact squared_coefficient_integral_tendsto_zero (fun n => sampleLaw P n) W A B
    (fun n => (hm n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (hW n))
    (Eventually.of_forall he) (Eventually.of_forall hb) hV
    (by filter_upwards [eventually_ge_atTop 1] with n hn; exact (hveq n (by omega)).le)
    (observed_scaledInvRisk_center_energy_tendsto_zero c P hP a ht0 ht1)

/-- The actual inverse-risk compensator coefficient converges in mean to
inverse population risk before the endpoint. No KM multiplier is inserted. -/
-- @node: observed_scaledInvRisk_mean_abs_tendsto_zero
lemma observed_scaledInvRisk_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      |(n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t)| ∂sampleLaw P n)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let q := P.p a * survival P a t * retention P a t
  have hq : 0 < q := mul_pos
    (mul_pos (c.pMin_pos.trans_le (hP.treatmentOverlap a)) (Real.exp_pos _))
    (retention_pos_of_modelClass c P hP a t ht0 ht1)
  let W := fun (n : ℕ) (s : Fin n → ObsHistory) => (riskSet a s t : ℝ) / n
  let A := fun (n : ℕ) (s : Fin n → ObsHistory) => (n : ℝ) * invRisk a s t
  let b := 1 / q
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) => W n s * |A n s ^ 2 - b ^ 2|
  have hW (n : ℕ) (s : Fin n → ObsHistory) : 0 ≤ W n s := by dsimp [W]; positivity
  have he (n : ℕ) : Integrable (fun s => W n s * (A n s - b) ^ 2)
      (sampleLaw P n) := by
    apply DeathCP.integrable_observed_risk_weighted_sq P a t _ (by dsimp [A]; fun_prop)
      (B := (n : ℝ) + |b|) (by positivity)
    intro s
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a s t).1]
      exact add_le_add (DeathCP.scaledInvRisk_mem_Icc a s t).2 (le_refl _))
  have hb (n : ℕ) : Integrable (fun s => W n s * b ^ 2) (sampleLaw P n) :=
    DeathCP.integrable_observed_risk_weighted_sq P a t _ measurable_const
      (abs_nonneg b) (fun _ => le_rfl)
  have hF (n : ℕ) : Integrable (F n) (sampleLaw P n) :=
    (integral_squared_coefficient_young (sampleLaw P n) (W n) (A n) (fun _ => b)
      (by dsimp [W, A]; fun_prop) (Eventually.of_forall (hW n))
      (he n) (hb n) (by norm_num : (0 : ℝ) < 1)).1
  have hR (n : ℕ) : Integrable (fun s => |W n s - q|) (sampleLaw P n) := by
    have hi : Integrable (W n) (sampleLaw P n) := by
      simpa only [one_pow, mul_one] using
        DeathCP.integrable_observed_risk_weighted_sq P a t (fun _ => 1)
          measurable_const (B := 1) (by norm_num) (fun _ => by norm_num)
    exact (hi.sub (integrable_const q)).abs
  have hlim := (observed_scaledInvRisk_squared_difference_mean_tendsto_zero
    c P hP a ht0 ht1).add
    ((observed_riskFraction_mean_abs_tendsto_zero c P hP a ⟨ht0, ht1.le⟩).const_mul
      (b ^ 2))
  apply squeeze_zero (fun n => integral_nonneg (fun s => abs_nonneg _)) _
    (by simpa only [mul_zero, add_zero] using hlim)
  intro n
  calc
    _ ≤ ∫ s, F n s + b ^ 2 * |W n s - q| ∂sampleLaw P n := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun s => abs_nonneg _))
        ((hF n).add ((hR n).const_mul (b ^ 2)))
      apply Eventually.of_forall
      intro s
      have heq : A n s - b = W n s * (A n s ^ 2 - b ^ 2) +
          (W n s - q) * b ^ 2 := by
        have hc : W n s * A n s ^ 2 = A n s := riskFraction_scaledInvRisk_sq_eq a s t
        have hqb : q * b ^ 2 = b := by dsimp [b]; field_simp
        nlinarith [hc, hqb]
      change |A n s - b| ≤ _
      rw [heq]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (hW n s), abs_of_nonneg (sq_nonneg b)]
      change W n s * |A n s ^ 2 - b ^ 2| + |W n s - q| * b ^ 2 ≤
        W n s * |A n s ^ 2 - b ^ 2| + b ^ 2 * |W n s - q|
      exact le_of_eq (by ring)
    _ = _ := by rw [integral_add (hF n) ((hR n).const_mul _), integral_const_mul]

/-- A first-moment envelope for inverse-risk error is integrable under
subcritical retention. It follows from the existing binomial second moment. -/
-- @node: observed_scaledInvRisk_mean_abs_le
lemma observed_scaledInvRisk_mean_abs_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory,
      |(n : ℝ) * invRisk a s t -
        1 / (P.p a * survival P a t * retention P a t)| ∂sampleLaw P n) ≤
      5 / (P.p a * survival P a t * retention P a t) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let q := P.p a * survival P a t * retention P a t
  have hq : 0 < q := mul_pos
    (mul_pos (c.pMin_pos.trans_le (hP.treatmentOverlap a)) (Real.exp_pos _))
    (retention_pos_of_modelClass c P hP a t ht0 ht1)
  have hi : Integrable (fun s : Fin n → ObsHistory =>
      ((n : ℝ) * invRisk a s t) ^ 2) (sampleLaw P n) := by
    apply Integrable.of_bound (by fun_prop) ((n : ℝ) ^ 2)
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (DeathCP.scaledInvRisk_mem_Icc a s t).1 (by positivity)).2
      (DeathCP.scaledInvRisk_mem_Icc a s t).2
  have hs := DeathCP.observed_integral_scaledInvRisk_sq_le P hP a (n := n) ht1 ⟨ht0, le_rfl⟩
  change (∫ s, |(n : ℝ) * invRisk a s t - 1 / q| ∂sampleLaw P n) ≤ 5 / q
  calc
    _ ≤ ∫ s, q * ((n : ℝ) * invRisk a s t) ^ 2 / 2 + 3 / (2 * q)
        ∂sampleLaw P n := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun s => abs_nonneg _))
        (((hi.const_mul q).div_const 2).add (integrable_const _))
      apply Eventually.of_forall
      intro s
      change |(n : ℝ) * invRisk a s t - 1 / q| ≤
        q * ((n : ℝ) * invRisk a s t) ^ 2 / 2 + 3 / (2 * q)
      have ha := (DeathCP.scaledInvRisk_mem_Icc a s t).1
      have hb : 0 ≤ 1 / q := by positivity
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg ha, abs_of_nonneg hb]
      apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * q by positivity)).mp
      field_simp
      nlinarith [sq_nonneg (q * ((n : ℝ) * invRisk a s t) - 1)]
    _ = q * (∫ s, ((n : ℝ) * invRisk a s t) ^ 2 ∂sampleLaw P n) / 2 +
        3 / (2 * q) := by
      rw [integral_add ((hi.const_mul q).div_const 2) (integrable_const _),
        integral_div, integral_const_mul, integral_const]
      simp
    _ ≤ q * (6 / q ^ 2) / 2 + 3 / (2 * q) := by
      have hscaled : q * (∫ s, ((n : ℝ) * invRisk a s t) ^ 2 ∂sampleLaw P n) / 2 ≤
          q * (6 / q ^ 2) / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hq.le)
          (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add hscaled le_rfl
    _ ≤ 5 / q := by
      field_simp
      nlinarith

/-- Dominated convergence integrates the actual inverse-risk compensator
error over the full horizon. The endpoint envelope uses only subcritical
retention, without requiring bounded oracle weights. -/
-- @node: subcritical_inverseRisk_density_mean_abs_tendsto_zero
lemma subcritical_inverseRisk_density_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ) (hf : Measurable f)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1,
      |f t| * (∫ s : Fin n → ObsHistory,
        |(n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)| ∂sampleLaw P n))
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let S : ℝ → ℝ := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hS : Measurable S := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hSeq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : S t = survival P a t :=
    piecewise_eq_of_mem _ _ _ ⟨ht.1.le, ht.2.le⟩
  let E := fun (n : ℕ) (t : ℝ) => |f t| *
    (∫ s : Fin n → ObsHistory, |(n : ℝ) * invRisk a s t -
      1 / (P.p a * S t * retention P a t)| ∂sampleLaw P n)
  have hm (n : ℕ) : Measurable (E n) := by
    have hh : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
        |(n : ℝ) * invRisk a p.1 p.2 - 1 / (P.p a * S p.2 * retention P a p.2)|) := by
      have hs : Measurable (fun p : (Fin n → ObsHistory) × ℝ => S p.2) := hS.comp measurable_snd
      have hg : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
        (measurable_retention P a).comp measurable_snd
      fun_prop
    exact hf.abs.mul hh.stronglyMeasurable.integral_prod_left'.measurable
  have hi := (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a
    (fun t => |f t| / survival P a t)
    (hc.abs.div (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne'))).const_mul (5 / P.p a)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖E n t‖ ≤ (5 / P.p a) * ((|f t| / survival P a t) / retention P a t) := by
    apply Eventually.of_forall
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp [E]
    rw [hSeq t ht, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (integral_nonneg (fun s => abs_nonneg _)))]
    calc
      _ ≤ |f t| * (5 / (P.p a * survival P a t * retention P a t)) :=
        mul_le_mul_of_nonneg_left
          (observed_scaledInvRisk_mean_abs_le c P hP a n ht.1.le ht.2) (abs_nonneg _)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun n => E n t) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [E, hSeq t ht, mul_zero] using
      (observed_scaledInvRisk_mean_abs_tendsto_zero c P hP a ht.1.le ht.2).const_mul |f t|
  have hlim := tendsto_integral_filter_of_dominated_convergence _
    (Eventually.of_forall (fun n => (hm n).aestronglyMeasurable)) hbound hi hpoint
  simp only [integral_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [E, hSeq t ht]

/-- Study-window continuity suffices for the inverse-risk density limit;
no global extension of a paper hazard is assumed. -/
-- @node: subcritical_inverseRisk_density_mean_abs_tendsto_zero_of_continuousOn
lemma subcritical_inverseRisk_density_mean_abs_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1,
      |f t| * (∫ s : Fin n → ObsHistory,
        |(n : ℝ) * invRisk a s t -
          1 / (P.p a * survival P a t * retention P a t)| ∂sampleLaw P n))
      atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  apply (subcritical_inverseRisk_density_mean_abs_tendsto_zero c P hP hk a g hg
    (hc.congr he)).congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [he t ⟨ht.1.le, ht.2.le⟩]

/-- The deterministic remaining-target death compensator has vanishing
full-horizon integrated marginal error. This is the drift coefficient in
(39), prior to optional-martingale and future-mark replacement steps. -/
-- @node: subcritical_death_inverseRisk_density_mean_abs_tendsto_zero
lemma subcritical_death_inverseRisk_density_mean_abs_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1,
      (remainingTarget c P a 0 t ^ 2 * P.hazard a t) *
        (∫ s : Fin n → ObsHistory,
          |(n : ℝ) * invRisk a s t -
            1 / (P.p a * survival P a t * retention P a t)| ∂sampleLaw P n))
      atTop (nhds 0) := by
  have hc : ContinuousOn (fun t => remainingTarget c P a 0 t ^ 2 * P.hazard a t)
      (Icc (0 : ℝ) 1) :=
    ((continuousOn_remainingTarget_zero c P hP a).pow 2).mul
      (hP.deathHolder a).1.continuousOn
  apply (subcritical_inverseRisk_density_mean_abs_tendsto_zero_of_continuousOn
    c P hP hk a _ hc).congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (c.dMin_pos.le.trans (hP.deathBounds a t ⟨ht.1.le, ht.2.le⟩).1))]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

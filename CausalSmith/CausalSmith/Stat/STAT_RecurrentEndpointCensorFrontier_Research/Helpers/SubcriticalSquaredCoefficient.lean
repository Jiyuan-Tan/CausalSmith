module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleEnergy

/-!
# Squared empirical coefficients in the subcritical compensator

Roadmap (31)--(32): Young's inequality upgrades the dependent KM/oracle
quadratic error to an absolute difference of squared coefficients. Exact
oracle energy controls the cross term without independence or endpoint bounds.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Young's inequality controls the change in a squared coefficient by its
quadratic error and an arbitrarily small multiple of the oracle square. -/
-- @node: squared_coefficient_young
lemma squared_coefficient_young (A B δ : ℝ) (hδ : 0 < δ) :
    |A ^ 2 - B ^ 2| ≤ (1 + 1 / δ) * (A - B) ^ 2 + δ * B ^ 2 := by
  apply (mul_le_mul_iff_of_pos_left hδ).mp
  have hd : δ * (1 / δ) = 1 := by field_simp
  have hfactor : δ * (1 + 1 / δ) = δ + 1 := by rw [mul_add, mul_one, hd]
  rw [← abs_of_pos hδ, ← abs_mul, abs_of_pos hδ, mul_add, ← mul_assoc, hfactor, abs_le]
  constructor <;>
    nlinarith [sq_nonneg (A - B + δ * B), sq_nonneg (A - B - δ * B),
      mul_nonneg hδ.le (sq_nonneg (A - B))]

/-- Integrable error and oracle energies give an integrable absolute change
of squared coefficients and its weighted Young bound. -/
-- @node: integral_squared_coefficient_young
lemma integral_squared_coefficient_young {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W A B : Ω → ℝ)
    (hm : AEStronglyMeasurable (fun x => W x * |A x ^ 2 - B x ^ 2|) μ)
    (hW : ∀ᵐ x ∂μ, 0 ≤ W x)
    (he : Integrable (fun x => W x * (A x - B x) ^ 2) μ)
    (hb : Integrable (fun x => W x * B x ^ 2) μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => W x * |A x ^ 2 - B x ^ 2|) μ ∧
    (∫ x, W x * |A x ^ 2 - B x ^ 2| ∂μ) ≤
      (1 + 1 / δ) * (∫ x, W x * (A x - B x) ^ 2 ∂μ) +
        δ * (∫ x, W x * B x ^ 2 ∂μ) := by
  have hi := (he.const_mul (1 + 1 / δ)).add (hb.const_mul δ)
  have hbound : ∀ᵐ x ∂μ,
      W x * |A x ^ 2 - B x ^ 2| ≤
        (1 + 1 / δ) * (W x * (A x - B x) ^ 2) + δ * (W x * B x ^ 2) := by
    filter_upwards [hW] with x hx
    simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (squared_coefficient_young (A x) (B x) δ hδ) hx
  have hj : Integrable (fun x => W x * |A x ^ 2 - B x ^ 2|) μ := by
    apply hi.mono' hm
    filter_upwards [hW, hbound] with x hx hbnd
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (abs_nonneg _))]
      using hbnd
  refine ⟨hj, ?_⟩
  calc
    _ ≤ ∫ x, (1 + 1 / δ) * (W x * (A x - B x) ^ 2) +
        δ * (W x * B x ^ 2) ∂μ := integral_mono_ae hj hi hbound
    _ = _ := by rw [integral_add (he.const_mul _) (hb.const_mul _),
      integral_const_mul, integral_const_mul]

/-- A vanishing quadratic coefficient error and uniformly bounded oracle
energy imply convergence in mean of the absolute squared-coefficient change. -/
-- @node: squared_coefficient_integral_tendsto_zero
lemma squared_coefficient_integral_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (W A B : (n : ℕ) → Ω n → ℝ)
    (hm : ∀ n, AEStronglyMeasurable
      (fun x => W n x * |A n x ^ 2 - B n x ^ 2|) (μ n))
    (hW : ∀ n, ∀ᵐ x ∂μ n, 0 ≤ W n x)
    (he : ∀ᶠ n in atTop, Integrable (fun x => W n x * (A n x - B n x) ^ 2) (μ n))
    (hb : ∀ᶠ n in atTop, Integrable (fun x => W n x * B n x ^ 2) (μ n))
    {V : ℝ} (hV : 0 ≤ V)
    (hbound : ∀ᶠ n in atTop, (∫ x, W n x * B n x ^ 2 ∂μ n) ≤ V)
    (hlim : Tendsto (fun n => ∫ x, W n x * (A n x - B n x) ^ 2 ∂μ n)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, W n x * |A n x ^ 2 - B n x ^ 2| ∂μ n)
      atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le
      (integral_nonneg_of_ae (by filter_upwards [hW n] with x hx; positivity)))
  · intro ε hε
    let δ := ε / (2 * (V + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδV : δ * V < ε / 2 := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hsmall := (hlim.const_mul (1 + 1 / δ)).eventually
      (gt_mem_nhds (show (1 + 1 / δ) * 0 < ε / 2 by rw [mul_zero]; positivity))
    filter_upwards [he, hb, hbound, hsmall] with n hen hbn hvn hsn
    have hy := (integral_squared_coefficient_young (μ n) (W n) (A n) (B n)
      (hm n) (hW n) hen hbn hδ).2
    have hv := mul_le_mul_of_nonneg_left hvn hδ.le
    linarith

/-- On the entire study window, squared empirical KM/inverse-risk
coefficients approach their oracle squares in integrated mean. This is the
compensator comparison, with unbounded endpoint oracle weights included. -/
-- @node: subcritical_squared_coefficient_mean_tendsto_zero
lemma subcritical_squared_coefficient_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : Measurable f) (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t, 0 ≤ f t) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let μ := fun n => (sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))
  let W := fun (n : ℕ) (p : (Fin n → ObsHistory) × ℝ) =>
    f p.2 * ((riskSet a p.1 p.2 : ℝ) / n)
  let A := fun (n : ℕ) (p : (Fin n → ObsHistory) × ℝ) =>
    (n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2
  let B := fun (n : ℕ) (p : (Fin n → ObsHistory) × ℝ) =>
    1 / (P.p a * retention P a p.2)
  have hW (n : ℕ) (p : (Fin n → ObsHistory) × ℝ) : 0 ≤ W n p := by
    dsimp [W]; exact mul_nonneg (hf0 _) (by positivity)
  have hm (n : ℕ) : Measurable (fun p => W n p * |A n p ^ 2 - B n p ^ 2|) := by
    have hg : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
      (measurable_retention P a).comp measurable_snd
    dsimp [W, A, B]
    fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have he (n : ℕ) (hn : 0 < n) : Integrable (fun p => W n p * (A n p - B n p) ^ 2) (μ n) := by
    simpa only [W, A, B, μ, mul_assoc] using
      DeathCP.observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
        c P hP a hk hn f hf (le_max_right K 0) (fun t ht => by
          simpa only [Real.norm_eq_abs] using
            (hK t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left K 0))
  have hb (n : ℕ) (hn : 0 < n) : Integrable (fun p => W n p * B n p ^ 2) (μ n) := by
    simpa only [W, B, μ, mul_assoc] using
      subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc
  let V := (P.p a)⁻¹ * ∫ t in Ioo (0 : ℝ) 1,
    survival P a t * f t / retention P a t
  have hVeq (n : ℕ) (hn : 0 < n) : (∫ p, W n p * B n p ^ 2 ∂μ n) = V := by
    rw [integral_prod _ (hb n hn)]
    simpa only [W, B, V, mul_assoc] using
      subcritical_oracle_expected_energy c P hP hk a hn f hf hc
  have hV : 0 ≤ V := by
    rw [← hVeq 1 (by norm_num)]
    exact integral_nonneg (fun p => mul_nonneg (hW _ _) (sq_nonneg _))
  have helim : Tendsto (fun n => ∫ p, W n p * (A n p - B n p) ^ 2 ∂μ n)
      atTop (nhds 0) := by
    apply (DeathCP.observed_KM_oracle_subcritical_expected_continuous_time_energy_tendsto_zero
      c P hP hk a f hc).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [integral_prod _ (he n (by omega))]
    simp only [W, A, B, mul_assoc, integral_Icc_eq_integral_Ioo]
  have hlim := squared_coefficient_integral_tendsto_zero μ W A B
    (fun n => (hm n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (hW n))
    (by filter_upwards [eventually_ge_atTop 1] with n hn; exact he n (by omega))
    (by filter_upwards [eventually_ge_atTop 1] with n hn; exact hb n (by omega))
    hV (by filter_upwards [eventually_ge_atTop 1] with n hn; exact (hVeq n (by omega)).le)
    helim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := (integral_squared_coefficient_young (μ n) (W n) (A n) (B n)
    (hm n).aestronglyMeasurable (Eventually.of_forall (hW n))
    (he n (by omega)) (hb n (by omega)) (by norm_num : (0 : ℝ) < 1)).1
  exact integral_prod _ hi

/-- Continuous nonnegative coefficients on the study window suffice for
the squared-coefficient comparison; no extension assumption is imposed. -/
-- @node: subcritical_squared_coefficient_mean_tendsto_zero_of_continuousOn
lemma subcritical_squared_coefficient_mean_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hg0 (t : ℝ) : 0 ≤ g t := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [he t ht]; exact hf0 t ht
    · simp only [g, Set.piecewise, if_neg ht, le_refl]
  apply (subcritical_squared_coefficient_mean_tendsto_zero c P hP hk a g hg hgc hg0).congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [he t ⟨ht.1.le, ht.2.le⟩]

/-- The empirical recurrence compensator coefficient and its risk-weighted
oracle have vanishing full-horizon absolute difference in mean. -/
-- @node: subcritical_recurrence_squared_coefficient_mean_tendsto_zero
lemma subcritical_recurrence_squared_coefficient_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1, P.lam a t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  exact subcritical_squared_coefficient_mean_tendsto_zero_of_continuousOn
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn
    (fun t ht => c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)

/-- The deterministic remaining-target death compensator coefficient has the
same full-horizon mean comparison. The future-mark plug-in is not inserted. -/
-- @node: subcritical_death_squared_coefficient_mean_tendsto_zero
lemma subcritical_death_squared_coefficient_mean_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (∫ t in Ioo (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|) ∂sampleLaw P n)
      atTop (nhds 0) := by
  apply subcritical_squared_coefficient_mean_tendsto_zero_of_continuousOn c P hP hk a
  · exact (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  · intro t ht
    exact mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)

/-- Markov's inequality upgrades the full-horizon mean comparison to
convergence in probability of the integrated absolute coefficient difference. -/
-- @node: subcritical_squared_coefficient_probability_tendsto_zero
lemma subcritical_squared_coefficient_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hf : Measurable f) (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t, 0 ≤ f t) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let F := fun (n : ℕ) (s : Fin n → ObsHistory) =>
    ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
      |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
        (1 / (P.p a * retention P a t)) ^ 2|
  have hF0 (n : ℕ) (s : Fin n → ObsHistory) : 0 ≤ F n s := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (mul_nonneg (hf0 _) (by positivity)) (abs_nonneg _)
  have hFi (n : ℕ) (hn : 0 < n) : Integrable (F n) (sampleLaw P n) := by
    let μ := (sampleLaw P n).prod (volume.restrict (Ioo (0 : ℝ) 1))
    let W := fun p : (Fin n → ObsHistory) × ℝ => f p.2 * ((riskSet a p.1 p.2 : ℝ) / n)
    let A := fun p : (Fin n → ObsHistory) × ℝ =>
      (n : ℝ) * deathKMLeft a p.1 p.2 * invRisk a p.1 p.2
    let B := fun p : (Fin n → ObsHistory) × ℝ => 1 / (P.p a * retention P a p.2)
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    have he : Integrable (fun p => W p * (A p - B p) ^ 2) μ := by
      simpa only [W, A, B, μ, mul_assoc] using
        DeathCP.observed_KM_oracle_subcritical_weighted_time_energy_integrable_prod
          c P hP a hk hn f hf (le_max_right K 0) (fun t ht => by
            simpa only [Real.norm_eq_abs] using
              (hK t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left K 0))
    have hb : Integrable (fun p => W p * B p ^ 2) μ := by
      simpa only [W, B, μ, mul_assoc] using
        subcritical_oracle_energy_integrable_prod c P hP hk a hn f hf hc
    have hm : Measurable (fun p => W p * |A p ^ 2 - B p ^ 2|) := by
      have hg : Measurable (fun p : (Fin n → ObsHistory) × ℝ => retention P a p.2) :=
        (measurable_retention P a).comp measurable_snd
      dsimp [W, A, B]
      fun_prop
    have hj := (integral_squared_coefficient_young μ W A B hm.aestronglyMeasurable
      (Eventually.of_forall (fun p => mul_nonneg (hf0 _) (by positivity)))
      he hb (by norm_num : (0 : ℝ) < 1)).1
    exact hj.integral_prod_left
  have hlim := (subcritical_squared_coefficient_mean_tendsto_zero c P hP hk a
    f hf hc hf0).div_const ε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using hlim)
  filter_upwards [eventually_ge_atTop 1] with n hn
  change (sampleLaw P n).real {s | ε < F n s} ≤ (∫ s, F n s ∂sampleLaw P n) / ε
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (hF0 n)) (hFi n (by omega)) ε
  have hsub : (sampleLaw P n).real {s | ε < F n s} ≤
      (sampleLaw P n).real {s | ε ≤ F n s} :=
    measureReal_mono (fun s (hs : ε < F n s) => (show ε ≤ F n s from hs.le)) (by finiteness)
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hsub hε.le).trans hm

/-- Study-window regularity suffices for the probability comparison, including
weights supplied only on the paper's closed horizon. -/
-- @node: subcritical_squared_coefficient_probability_tendsto_zero_of_continuousOn
lemma subcritical_squared_coefficient_probability_tendsto_zero_of_continuousOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Ioo (0 : ℝ) 1, f t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|}) atTop (nhds 0) := by
  classical
  let g := (Icc (0 : ℝ) 1).piecewise f (fun _ => 0)
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const measurableSet_Icc
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f t := piecewise_eq_of_mem _ _ _ ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hc.congr he
  have hg0 (t : ℝ) : 0 ≤ g t := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [he t ht]; exact hf0 t ht
    · simp only [g, Set.piecewise, if_neg ht, le_refl]
  apply (subcritical_squared_coefficient_probability_tendsto_zero c P hP hk a
    g hg hgc hg0 hε).congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq]
  apply Iff.of_eq
  apply congrArg (fun x : ℝ => ε < x)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [he t ⟨ht.1.le, ht.2.le⟩]

/-- The recurrence squared-coefficient compensator comparison holds in
probability on the full horizon. -/
-- @node: subcritical_recurrence_squared_coefficient_probability_tendsto_zero
lemma subcritical_recurrence_squared_coefficient_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Ioo (0 : ℝ) 1, P.lam a t * ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|}) atTop (nhds 0) := by
  exact subcritical_squared_coefficient_probability_tendsto_zero_of_continuousOn
    c P hP hk a (P.lam a) (hP.recurrenceHolder a).1.continuousOn
    (fun t ht => c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1) hε

/-- The deterministic death squared-coefficient comparison holds in
probability, without a predictability premise for the future-mark plug-in. -/
-- @node: subcritical_death_squared_coefficient_probability_tendsto_zero
lemma subcritical_death_squared_coefficient_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < ∫ t in Ioo (0 : ℝ) 1,
        ((remainingTarget c P a 0 t / survival P a t) ^ 2 * P.hazard a t) *
        ((riskSet a s t : ℝ) / n) *
        |((n : ℝ) * deathKMLeft a s t * invRisk a s t) ^ 2 -
          (1 / (P.p a * retention P a t)) ^ 2|}) atTop (nhds 0) := by
  apply subcritical_squared_coefficient_probability_tendsto_zero_of_continuousOn c P hP hk a
  · exact (((continuousOn_remainingTarget_zero c P hP a).div
      (modelClass_survival_continuousOn c P hP a)
      (fun t _ => (Real.exp_pos _).ne')).pow 2).mul
        (hP.deathHolder a).1.continuousOn
  · intro t ht
    exact mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)
  · exact hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

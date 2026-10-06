module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOrdinaryConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly

/-! # Root-n tightness of the actual ordinary estimator

Roadmap (20)--(23), (27): full-horizon recurrence and death second moments,
root-n negligible extinction, and the exact decomposition give tightness of
the raw arm means. Projection contracts error, and subtraction gives tightness
and consistency of the observable contrast without assuming an influence expansion.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A C/n second-moment bound gives a sample-size independent root-n tail bound. -/
-- @node: rootn_probability_le_of_secondMoment
lemma rootn_probability_le_of_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hi : Integrable (fun x => X x ^ 2) μ) {n : ℕ} (hn : 0 < n)
    {C K : ℝ} (hb : (∫ x, X x ^ 2 ∂μ) ≤ C / n) (hK : 0 < K) :
    μ.real {x | K < |Real.sqrt n * X x|} ≤ C / K ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hi' : Integrable (fun x => (Real.sqrt n * X x) ^ 2) μ := by
    simpa only [mul_pow] using hi.const_mul (Real.sqrt n ^ 2)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg (Real.sqrt n * X x))) hi' (K ^ 2)
  have hsub : {x | K < |Real.sqrt n * X x|} ⊆
      {x | K ^ 2 ≤ (Real.sqrt n * X x) ^ 2} := by
    intro x hx
    change K < |Real.sqrt n * X x| at hx
    change K ^ 2 ≤ (Real.sqrt n * X x) ^ 2
    nlinarith [sq_abs (Real.sqrt n * X x)]
  have hb' : (∫ x, (Real.sqrt n * X x) ^ 2 ∂μ) ≤ C := by
    simp only [mul_pow, hs, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hb hnR.le).trans_eq (by field_simp)
  apply (le_div_iff₀ (sq_pos_of_pos hK)).2
  simpa only [mul_comm] using
    ((mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
      (sq_nonneg K)).trans hm).trans hb'

/-- Recurrence and death are jointly tight at root-n scale from their genuine
second moments. No assertion about covariance or independence is needed. -/
-- @node: subcritical_stochasticErrors_rootn_uniform_tight
lemma subcritical_stochasticErrors_rootn_uniform_tight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      (sampleLaw P n).real {s | K < |Real.sqrt n * recurrenceError c P a s 0|} +
      (sampleLaw P n).real {s | K < |Real.sqrt n * deathError c P a s 0|} < ε := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let R := 2 * Real.exp c.dMax * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin *
    (∫ t in Ioo (0 : ℝ) 1, (retention P a t)⁻¹)
  have hR : 0 ≤ R := by
    dsimp [R]
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)) c.pMin_pos.le
    · exact integral_nonneg (fun _ => inv_nonneg.mpr measureReal_nonneg)
  obtain ⟨D, hD, hd⟩ := subcritical_deathError_zero_secondMoment_le c P hP hk a
  let K := Real.sqrt ((R + D) / ε) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hsq : (R + D) / ε < K ^ 2 := by
    have hs := Real.sq_sqrt (div_nonneg (add_nonneg hR hD) hε.le)
    have hp := Real.sqrt_nonneg ((R + D) / ε)
    dsimp [K]
    nlinarith
  have hbound : (R + D) / K ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hK)).2
    have h := (div_lt_iff₀ hε).1 hsq
    nlinarith
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hr := rootn_probability_le_of_secondMoment (sampleLaw P n)
    (fun s => recurrenceError c P a s 0)
    (recurrenceError_secondMoment_eq_exposure_energy_of_nonneg c P hP a n
      (h := 0) (by norm_num) (by norm_num)).1 hn
    (subcritical_recurrenceError_zero_secondMoment_le c P hP hk a hn) hK
  have he := rootn_probability_le_of_secondMoment (sampleLaw P n)
    (fun s => deathError c P a s 0)
    (deathError_sq_integrable c P hP a n (h := 0) (by norm_num) (by norm_num)) hn
    (hd n hn) hK
  exact (add_le_add hr he).trans_lt (by simpa only [add_div, R] using hbound)

/-- Raw ordinary arm means are asymptotically tight at root-n scale by the
exact decomposition, with extinction controlled separately in probability. -/
-- @node: subcritical_ordinaryMuTilde_rootn_tight
lemma subcritical_ordinaryMuTilde_rootn_tight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (sampleLaw P n).real {s |
        K < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a)|} < ε := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  obtain ⟨K, hK, hb⟩ := subcritical_stochasticErrors_rootn_uniform_tight
    c P hP hk a (half_pos hε)
  have hExt := subcritical_extinctionError_rootn_probability_tendsto_zero c P hP hk a hK
  have he := hExt.eventually_lt_const (half_pos hε)
  refine ⟨3 * K, by positivity, ?_⟩
  filter_upwards [he, eventually_ge_atTop 3] with n hen hn
  let A : Set (Fin n → ObsHistory) := {s | K < |Real.sqrt n * recurrenceError c P a s 0|}
  let B : Set (Fin n → ObsHistory) := {s | K < |Real.sqrt n * deathError c P a s 0|}
  let E : Set (Fin n → ObsHistory) := {s | K < |Real.sqrt n * extinctionError c P a s 0|}
  have hsub : ∀ᵐ s ∂sampleLaw P n,
      3 * K < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a)| →
        s ∈ (A ∪ B) ∪ E := by
    filter_upwards [ordinaryMuTilde_error_decomposition_ae c P hP a hn] with s hs
    intro ht
    rw [hs, mul_sub, mul_sub] at ht
    by_contra hnot
    have hR : |Real.sqrt n * recurrenceError c P a s 0| ≤ K := by
      simpa [A, B, E, not_or, not_lt] using (not_or.mp (not_or.mp hnot).1).1
    have hD : |Real.sqrt n * deathError c P a s 0| ≤ K := by
      simpa [A, B, E, not_or, not_lt] using (not_or.mp (not_or.mp hnot).1).2
    have hE : |Real.sqrt n * extinctionError c P a s 0| ≤ K := by
      simpa [A, B, E, not_lt] using (not_or.mp hnot).2
    have ht' := (abs_sub (Real.sqrt n * recurrenceError c P a s 0 -
      Real.sqrt n * deathError c P a s 0) (Real.sqrt n * extinctionError c P a s 0)).trans
        (add_le_add (abs_sub _ _) le_rfl)
    linarith
  have hm : (sampleLaw P n).real {s |
      3 * K < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a)|} ≤
      (sampleLaw P n).real A + (sampleLaw P n).real B + (sampleLaw P n).real E := by
    calc
      _ ≤ (sampleLaw P n).real ((A ∪ B) ∪ E) :=
        ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
      _ ≤ (sampleLaw P n).real (A ∪ B) + (sampleLaw P n).real E := measureReal_union_le _ _
      _ ≤ _ := add_le_add (measureReal_union_le A B) le_rfl
  have hst := hb n (by omega)
  exact hm.trans_lt (by dsimp [A, B, E]; linarith)

/-- Projection contracts absolute arm error as well as squared error. -/
-- @node: ordinaryMuHat_abs_error_le
lemma ordinaryMuHat_abs_error_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) :
    |ordinaryMuHat c a s - armMean P a| ≤ |ordinaryMuTilde a s - armMean P a| := by
  apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
  simpa only [sq_abs, ordinaryMuHat] using projectArm_sq_error_le c
    (ordinaryMuTilde a s) (armMean P a) (armMean_mem_projectionRange c P hP a)

/-- The actual projected ordinary arm estimator is tight at root-n scale. -/
-- @node: subcritical_ordinaryMuHat_rootn_tight
lemma subcritical_ordinaryMuHat_rootn_tight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (sampleLaw P n).real {s |
        K < |Real.sqrt n * (ordinaryMuHat c a s - armMean P a)|} < ε := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  obtain ⟨K, hK, hb⟩ := subcritical_ordinaryMuTilde_rootn_tight c P hP hk a hε
  refine ⟨K, hK, hb.mono (fun n hn => ?_)⟩
  apply lt_of_le_of_lt (measureReal_mono ?_ (by finiteness)) hn
  intro s hs
  change K < |Real.sqrt n * (ordinaryMuHat c a s - armMean P a)| at hs
  change K < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a)|
  rw [abs_mul] at hs ⊢
  exact hs.trans_le (mul_le_mul_of_nonneg_left (ordinaryMuHat_abs_error_le c P hP a s)
    (abs_nonneg _))

/-- Subtracting the two tight arm errors gives root-n tightness of the
actual observable treatment contrast. -/
-- @node: subcritical_ordinaryEstimator_rootn_tight
lemma subcritical_ordinaryEstimator_rootn_tight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (sampleLaw P n).real {s |
        K < |Real.sqrt n * (ordinaryEstimator c s - causalTarget P)|} < ε := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  obtain ⟨K₁, hK₁, hb₁⟩ := subcritical_ordinaryMuHat_rootn_tight c P hP hk true (half_pos hε)
  obtain ⟨K₀, hK₀, hb₀⟩ := subcritical_ordinaryMuHat_rootn_tight c P hP hk false (half_pos hε)
  refine ⟨K₁ + K₀, add_pos hK₁ hK₀, ?_⟩
  filter_upwards [hb₁, hb₀] with n hn₁ hn₀
  have hsub : {s : Fin n → ObsHistory |
      K₁ + K₀ < |Real.sqrt n * (ordinaryEstimator c s - causalTarget P)|} ⊆
      {s | K₁ < |Real.sqrt n * (ordinaryMuHat c true s - armMean P true)|} ∪
      {s | K₀ < |Real.sqrt n * (ordinaryMuHat c false s - armMean P false)|} := by
    intro s hs
    change K₁ + K₀ < |Real.sqrt n * (ordinaryEstimator c s - causalTarget P)| at hs
    by_contra hnot
    have hb := not_or.mp hnot
    have h₁ : |Real.sqrt n * (ordinaryMuHat c true s - armMean P true)| ≤ K₁ :=
      le_of_not_gt hb.1
    have h₀ : |Real.sqrt n * (ordinaryMuHat c false s - armMean P false)| ≤ K₀ :=
      le_of_not_gt hb.2
    have hid : Real.sqrt n * (ordinaryEstimator c s - causalTarget P) =
        Real.sqrt n * (ordinaryMuHat c true s - armMean P true) -
        Real.sqrt n * (ordinaryMuHat c false s - armMean P false) := by
      rw [hP.causalTarget_eq_survival_intensity_contrast,
        intervalIntegral.integral_sub (hP.armMean_integrand_intervalIntegrable true)
          (hP.armMean_integrand_intervalIntegrable false)]
      unfold ordinaryEstimator armMean
      ring
    rw [hid] at hs
    have ha := abs_sub (Real.sqrt n * (ordinaryMuHat c true s - armMean P true))
      (Real.sqrt n * (ordinaryMuHat c false s - armMean P false))
    linarith
  exact ((measureReal_mono hsub (by finiteness)).trans (measureReal_union_le _ _)).trans_lt
    (by linarith)

/-- The projected arm estimator inherits consistency by contractivity. -/
-- @node: subcritical_ordinaryMuHat_probability_tendsto_zero
lemma subcritical_ordinaryMuHat_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |ordinaryMuHat c a s - armMean P a|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (subcritical_ordinaryMuTilde_probability_tendsto_zero c P hP hk a hε)
  apply Eventually.of_forall
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs
  exact hs.trans_le (ordinaryMuHat_abs_error_le c P hP a s)

/-- The actual ordinary treatment contrast is consistent without presuming
its asymptotic influence representation. -/
-- @node: subcritical_ordinaryEstimator_probability_tendsto_zero
lemma subcritical_ordinaryEstimator_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |ordinaryEstimator c s - causalTarget P|}) atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hlim := (subcritical_ordinaryMuHat_probability_tendsto_zero c P hP hk true
    (half_pos hε)).add (subcritical_ordinaryMuHat_probability_tendsto_zero c P hP hk false
      (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hlim)
  apply Eventually.of_forall
  intro n
  have hsub : {s : Fin n → ObsHistory | ε < |ordinaryEstimator c s - causalTarget P|} ⊆
      {s | ε / 2 < |ordinaryMuHat c true s - armMean P true|} ∪
      {s | ε / 2 < |ordinaryMuHat c false s - armMean P false|} := by
    intro s hs
    change ε < |ordinaryEstimator c s - causalTarget P| at hs
    by_contra hnot
    have hb := not_or.mp hnot
    have h₁ : |ordinaryMuHat c true s - armMean P true| ≤ ε / 2 := le_of_not_gt hb.1
    have h₀ : |ordinaryMuHat c false s - armMean P false| ≤ ε / 2 := le_of_not_gt hb.2
    have hid : ordinaryEstimator c s - causalTarget P =
        (ordinaryMuHat c true s - armMean P true) -
        (ordinaryMuHat c false s - armMean P false) := by
      rw [hP.causalTarget_eq_survival_intensity_contrast,
        intervalIntegral.integral_sub (hP.armMean_integrand_intervalIntegrable true)
          (hP.armMean_integrand_intervalIntegrable false)]
      unfold ordinaryEstimator armMean
      ring
    rw [hid] at hs
    have ha := abs_sub (ordinaryMuHat c true s - armMean P true)
      (ordinaryMuHat c false s - armMean P false)
    linarith
  exact (measureReal_mono hsub (by finiteness)).trans (measureReal_union_le _ _)

/-- At root-n scale, projection contributes a negligible contrast remainder
because its activity probability vanishes; no bound on the raw estimate is needed. -/
-- @node: subcritical_projection_rootn_probability_tendsto_zero
lemma subcritical_projection_rootn_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Real.sqrt n *
        (ordinaryEstimator c s - (ordinaryMuTilde true s - ordinaryMuTilde false s))|})
      atTop (nhds 0) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (subcritical_projectionActivity_probability_tendsto_zero c P hP hk)
  apply Eventually.of_forall
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs heq
  change ε < |Real.sqrt n *
    (ordinaryEstimator c s - (ordinaryMuTilde true s - ordinaryMuTilde false s))| at hs
  rw [heq, sub_self, mul_zero, abs_zero] at hs
  exact (not_lt_of_ge hε.le) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

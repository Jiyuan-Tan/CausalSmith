module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariancePlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalNonfallback
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalEstimatorTightness
public import Causalean.Mathlib.Probability.StdNormalCDF
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Length of the subcritical observable interval

Roadmap (46): variance consistency gives standard-error consistency and a
shrinking radius. Consistency of the actual estimator and strict interiority
of the target remove clipping with probability tending to one. Vanishing
fallback then transfers the exact untruncated length to the stated interval.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The paper's normal quantile is the standard-normal probit. -/
-- @node: normalQuantile_eq_probit
lemma normalQuantile_eq_probit (alpha : ℝ) :
    normalQuantile alpha = Causalean.Mathlib.probit (1 - alpha / 2) := by
  unfold normalQuantile normalCDF Causalean.Mathlib.probit Causalean.Mathlib.stdNormalCDF
  simp only [cdf_eq_real]

/-- The two-sided normal critical value is positive in the paper's range. -/
-- @node: normalQuantile_pos
lemma normalQuantile_pos {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2) :
    0 < normalQuantile alpha := by
  have hp := Causalean.Mathlib.stdNormalCDF_probit
    (show 0 < 1 - alpha / 2 by linarith) (show 1 - alpha / 2 < 1 by linarith)
  have hz : Causalean.Mathlib.stdNormalCDF 0 = 1 / 2 := by
    have h := Causalean.Mathlib.stdNormalCDF_neg 0
    simp only [neg_zero] at h
    linarith
  rw [normalQuantile_eq_probit]
  apply Causalean.Mathlib.stdNormalCDF_strictMono.lt_iff_lt.mp
  rw [hz, hp]
  linarith

/-- Continuous square root transfers the proved observable variance limit. -/
-- @node: subcritical_standardError_probability_tendsto_zero
lemma subcritical_standardError_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Real.sqrt (sigmaHatSq c s) - Real.sqrt (subcriticalVariance c P)|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt Real.sqrt (subcriticalVariance c P) from
      Real.continuous_sqrt.continuousAt) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (sigmaHatSq_probability_tendsto_subcriticalVariance c P hP hk (half_pos hδ))
  apply Eventually.of_forall
  intro n
  apply measureReal_mono _ (by finiteness)
  intro s hs
  by_contra hn
  have hd : dist (sigmaHatSq c s) (subcriticalVariance c P) < δ := by
    rw [Real.dist_eq]
    have : |sigmaHatSq c s - subcriticalVariance c P| ≤ δ / 2 := le_of_not_gt hn
    linarith
  have ht := hb hd
  rw [Real.dist_eq] at ht
  change ε < |Real.sqrt (sigmaHatSq c s) - Real.sqrt (subcriticalVariance c P)| at hs
  linarith

/-- A fixed multiple of the observable standard error divided by root n
vanishes in probability. No independence of numerator and denominator is used. -/
-- @node: subcritical_intervalRadius_probability_tendsto_zero
lemma subcritical_intervalRadius_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (z : ℝ) (hz : 0 ≤ z) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < z * Real.sqrt (sigmaHatSq c s) / Real.sqrt n}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have ht : Tendsto (fun n : ℕ =>
      z * (Real.sqrt (subcriticalVariance c P) + 1) / Real.sqrt n) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_def] using
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop.const_mul
        (z * (Real.sqrt (subcriticalVariance c P) + 1)))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (subcritical_standardError_probability_tendsto_zero c P hP hk (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  apply measureReal_mono _ (by finiteness)
  intro s hs
  by_contra hnot
  have hb : Real.sqrt (sigmaHatSq c s) ≤ Real.sqrt (subcriticalVariance c P) + 1 := by
    have : |Real.sqrt (sigmaHatSq c s) - Real.sqrt (subcriticalVariance c P)| ≤ 1 :=
      le_of_not_gt hnot
    have := (le_abs_self (Real.sqrt (sigmaHatSq c s) - Real.sqrt (subcriticalVariance c P))).trans this
    linarith
  have hle := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hz) (Real.sqrt_nonneg (n : ℝ))
  exact (not_lt_of_ge (hle.trans hn.le)) hs

/-- On nonfallback samples whose center error and radius fit in the target's
interior margin, clipping has no effect on the Gaussian interval. -/
-- @node: subcriticalInterval_eq_unclipped_of_margin
lemma subcriticalInterval_eq_unclipped_of_margin
    (c : ClassConstants) (P : SubjectLaw) (alpha : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) {δ : ℝ}
    (hleft : -c.lambdaMax + 2 * δ ≤ causalTarget P)
    (hright : causalTarget P ≤ c.lambdaMax - 2 * δ)
    (hf : nonFallbackSub c s)
    (he : |ordinaryEstimator c s - causalTarget P| ≤ δ)
    (hr : normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n ≤ δ) :
    subcriticalInterval c alpha s =
      Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
        (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n) := by
  classical
  rw [subcriticalInterval, if_pos hf]
  apply inter_eq_left.mpr
  intro x hx
  have hab := abs_le.mp he
  constructor <;> linarith [hx.1, hx.2, hab.1, hab.2]

/-- Fallback and clipping are asymptotically inactive for the actual interval. -/
-- @node: subcriticalInterval_clipping_probability_tendsto_zero
lemma subcriticalInterval_clipping_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      subcriticalInterval c alpha s ≠
        Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
          (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hi := causalTarget_mem_projectionInterior c P hP
  let δ := min (causalTarget P + c.lambdaMax) (c.lambdaMax - causalTarget P) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min (by linarith [hi.1]) (by linarith [hi.2])) (by norm_num)
  have hl : -c.lambdaMax + 2 * δ ≤ causalTarget P := by
    have := min_le_left (causalTarget P + c.lambdaMax) (c.lambdaMax - causalTarget P)
    dsimp [δ] at hδ ⊢; linarith
  have hr : causalTarget P ≤ c.lambdaMax - 2 * δ := by
    have := min_le_right (causalTarget P + c.lambdaMax) (c.lambdaMax - causalTarget P)
    dsimp [δ] at hδ ⊢; linarith
  have ht := ((nonFallbackSub_compl_probability_tendsto_of_variance_consistency
    c P hP hk (fun ε hε => sigmaHatSq_probability_tendsto_subcriticalVariance c P hP hk hε)).add
    (subcritical_ordinaryEstimator_probability_tendsto_zero c P hP hk hδ)).add
    (subcritical_intervalRadius_probability_tendsto_zero c P hP hk (normalQuantile alpha)
      (normalQuantile_pos ha0 ha1).le hδ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ht)
  apply Eventually.of_forall
  intro n
  let A : Set (Fin n → ObsHistory) := {s | ¬ nonFallbackSub c s}
  let B : Set (Fin n → ObsHistory) := {s | δ < |ordinaryEstimator c s - causalTarget P|}
  let C : Set (Fin n → ObsHistory) :=
    {s | δ < normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n}
  have hb : {s : Fin n → ObsHistory |
      subcriticalInterval c alpha s ≠
        Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
          (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)} ⊆
      (A ∪ B) ∪ C := by
    intro s hs
    by_contra hn
    have hn' : (nonFallbackSub c s ∧ |ordinaryEstimator c s - causalTarget P| ≤ δ) ∧
        normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n ≤ δ := by
      simpa only [A, B, C, mem_union, mem_setOf_eq, not_or, not_not, not_lt] using hn
    exact hs (subcriticalInterval_eq_unclipped_of_margin c P alpha s hl hr hn'.1.1 hn'.1.2 hn'.2)
  exact (measureReal_mono hb (by finiteness)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le A B) le_rfl))

/-- The untruncated interval has its exact root-n scaled length, including
all constants in the paper's normal critical value. -/
-- @node: subcriticalInterval_scaled_length_of_unclipped
lemma subcriticalInterval_scaled_length_of_unclipped
    (c : ClassConstants) (alpha : ℝ) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) (hz : 0 ≤ normalQuantile alpha)
    (he : subcriticalInterval c alpha s =
      Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
        (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)) :
    Real.sqrt n * volume.real (subcriticalInterval c alpha s) =
      2 * normalQuantile alpha * Real.sqrt (sigmaHatSq c s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n :=
    div_nonneg (mul_nonneg hz (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [he, Real.volume_real_Icc_of_le (by linarith)]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  field_simp
  <;> ring

/-- Roadmap (46), with the actual observable studentizer, full-range fallback,
and clipping: scaled interval length converges to the exact normal length. -/
-- @node: subcriticalInterval_scaled_length_probability_tendsto_zero
lemma subcriticalInterval_scaled_length_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |Real.sqrt n * volume.real (subcriticalInterval c alpha s) -
        2 * normalQuantile alpha * Real.sqrt (subcriticalVariance c P)|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hz := normalQuantile_pos ha0 ha1
  have hδ : 0 < ε / (2 * normalQuantile alpha) := by positivity
  have ht := (subcriticalInterval_clipping_probability_tendsto_zero c P hP hk alpha ha0 ha1).add
    (subcritical_standardError_probability_tendsto_zero c P hP hk hδ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ht)
  filter_upwards [eventually_ge_atTop 1] with n hn
  let A : Set (Fin n → ObsHistory) := {s | subcriticalInterval c alpha s ≠
      Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
        (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)}
  let B : Set (Fin n → ObsHistory) := {s |
    ε / (2 * normalQuantile alpha) <
      |Real.sqrt (sigmaHatSq c s) - Real.sqrt (subcriticalVariance c P)|}
  have hb : {s : Fin n → ObsHistory |
      ε < |Real.sqrt n * volume.real (subcriticalInterval c alpha s) -
        2 * normalQuantile alpha * Real.sqrt (subcriticalVariance c P)|} ⊆ A ∪ B := by
    intro s hs
    by_cases ha : s ∈ A
    · exact Or.inl ha
    · right
      have he : subcriticalInterval c alpha s =
          Icc (ordinaryEstimator c s - normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
            (ordinaryEstimator c s + normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n) :=
        not_ne_iff.mp ha
      change ε < |Real.sqrt n * volume.real (subcriticalInterval c alpha s) -
        2 * normalQuantile alpha * Real.sqrt (subcriticalVariance c P)| at hs
      rw [subcriticalInterval_scaled_length_of_unclipped c alpha (by omega) s hz.le he,
        ← mul_sub, abs_mul, abs_of_pos (mul_pos (by norm_num) hz)] at hs
      exact (div_lt_iff₀ (mul_pos (by norm_num) hz)).2 (by simpa only [mul_comm] using hs)
  exact (measureReal_mono hb (by finiteness)).trans (measureReal_union_le A B)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

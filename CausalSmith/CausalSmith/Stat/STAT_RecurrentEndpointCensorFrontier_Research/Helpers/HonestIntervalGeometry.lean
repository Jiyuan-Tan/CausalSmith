module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedFullIdentification
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Geometry and length of the conservative interval

Clipping the symmetric interval to the target range preserves coverage and
bounds its length by twice its radius. The bounded measurable length is
integrable, so its deterministic bound also controls expected length.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The squared-risk scale is strictly positive at every allowed sample size. -/
-- @node: riskScale_pos
lemma riskScale_pos (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n) :
    0 < riskScale c n := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  unfold riskScale
  split_ifs
  · exact inv_pos.mpr hn0
  · exact div_pos (Real.log_pos hn1) hn0
  · exact Real.rpow_pos_of_pos hn0 _

/-- Projection puts every estimated arm mean in the clinical range. -/
-- @node: projectArm_mem_range
lemma projectArm_mem_range (c : ClassConstants) (x : ℝ) :
    projectArm c x ∈ Icc (0 : ℝ) c.lambdaMax := by
  have hl : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  exact ⟨le_max_left _ _, max_le hl (min_le_left _ _)⟩

/-- Both projected arms keep the estimated contrast in the target range. -/
-- @node: observableEstimator_mem_range
lemma observableEstimator_mem_range (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) :
    observableEstimator c s ∈ Icc (-c.lambdaMax) c.lambdaMax := by
  have h1 := projectArm_mem_range c (muTildeAt c (bandwidth c n) true s)
  have h0 := projectArm_mem_range c (muTildeAt c (bandwidth c n) false s)
  change 0 ≤ muHatAt c (bandwidth c n) true s ∧
    muHatAt c (bandwidth c n) true s ≤ c.lambdaMax at h1
  change 0 ≤ muHatAt c (bandwidth c n) false s ∧
    muHatAt c (bandwidth c n) false s ≤ c.lambdaMax at h0
  unfold observableEstimator
  constructor <;> linarith [h1.1, h1.2, h0.1, h0.2]

/-- The causal target is the contrast of the identified arm means. -/
-- @node: causalTarget_eq_armMean_contrast
lemma causalTarget_eq_armMean_contrast (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) : causalTarget P = armMean P true - armMean P false := by
  rw [hP.causalTarget_eq_survival_intensity_contrast,
    intervalIntegral.integral_sub (hP.armMean_integrand_intervalIntegrable true)
      (hP.armMean_integrand_intervalIntegrable false)]
  rfl

/-- The two arm-mean bounds put the causal contrast in the clipping range. -/
-- @node: causalTarget_mem_range
lemma causalTarget_mem_range (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) : causalTarget P ∈ Icc (-c.lambdaMax) c.lambdaMax := by
  have h1 := armMean_mem_projectionRange c P hP true
  have h0 := armMean_mem_projectionRange c P hP false
  rw [causalTarget_eq_armMean_contrast c P hP]
  constructor <;> linarith [h1.1, h1.2, h0.1, h0.2]

/-- Projecting the measurable recurrence sum gives a measurable arm estimate. -/
-- @node: measurable_muHatAt
@[fun_prop]
lemma measurable_muHatAt (c : ClassConstants) (h : ℝ) (a : Arm) (n : ℕ) :
    Measurable (muHatAt c h a (n := n)) := by
  unfold muHatAt projectArm
  fun_prop

/-- The contrast of the measurable projected arm estimates is measurable. -/
-- @node: measurable_observableEstimator
@[fun_prop]
lemma measurable_observableEstimator (c : ClassConstants) (n : ℕ) :
    Measurable (observableEstimator c (n := n)) := by
  unfold observableEstimator
  fun_prop

/-- Membership in the clipped interval is precisely the symmetric error
bound for any target in the clinical range. -/
-- @node: mem_conservativeInterval_iff
lemma mem_conservativeInterval_iff (c : ClassConstants) (K m : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) (hm : m ∈ Icc (-c.lambdaMax) c.lambdaMax) :
    m ∈ conservativeInterval c K s ↔
      |observableEstimator c s - m| ≤ Real.sqrt (K * riskScale c n) := by
  simp only [conservativeInterval, mem_inter_iff, mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, _⟩
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    exact ⟨⟨by linarith, by linarith⟩, hm⟩

/-- The clipped interval is a closed interval with explicitly clipped ends. -/
-- @node: conservativeInterval_eq_Icc
lemma conservativeInterval_eq_Icc (c : ClassConstants) (K : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) :
    conservativeInterval c K s =
      Icc (max (observableEstimator c s - Real.sqrt (K * riskScale c n)) (-c.lambdaMax))
        (min (observableEstimator c s + Real.sqrt (K * riskScale c n)) c.lambdaMax) := by
  exact Icc_inter_Icc

/-- Clipping cannot enlarge the symmetric interval's length. -/
-- @node: conservativeInterval_length_le
lemma conservativeInterval_length_le (c : ClassConstants) (K : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) :
    volume.real (conservativeInterval c K s) ≤ 2 * Real.sqrt (K * riskScale c n) := by
  rw [conservativeInterval_eq_Icc, Real.volume_real_Icc]
  apply max_le
  · have hl := le_max_left (observableEstimator c s - Real.sqrt (K * riskScale c n))
      (-c.lambdaMax)
    have hu := min_le_left (observableEstimator c s + Real.sqrt (K * riskScale c n))
      c.lambdaMax
    linarith
  · positivity

/-- The explicit endpoint formula makes interval length measurable. -/
-- @node: measurable_conservativeInterval_length
@[fun_prop]
lemma measurable_conservativeInterval_length (c : ClassConstants) (K : ℝ) (n : ℕ) :
    Measurable (fun s : Fin n → ObsHistory => volume.real (conservativeInterval c K s)) := by
  simp_rw [conservativeInterval_eq_Icc, Real.volume_real_Icc]
  fun_prop

/-- The deterministic length bound implies integrability under any finite law. -/
-- @node: integrable_conservativeInterval_length
lemma integrable_conservativeInterval_length (c : ClassConstants) (K : ℝ) (n : ℕ)
    (μ : Measure (Fin n → ObsHistory)) [IsFiniteMeasure μ] :
    Integrable (fun s => volume.real (conservativeInterval c K s)) μ := by
  apply Integrable.of_bound (measurable_conservativeInterval_length c K n).aestronglyMeasurable
    (2 * Real.sqrt (K * riskScale c n))
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact conservativeInterval_length_le c K s)

/-- Under the iid probability law, expected length is bounded by twice the radius. -/
-- @node: conservativeInterval_expected_length_le
lemma conservativeInterval_expected_length_le (c : ClassConstants) (P : SubjectLaw)
    (K : ℝ) (n : ℕ) :
    (∫ s, volume.real (conservativeInterval c K s) ∂sampleLaw P n) ≤
      2 * Real.sqrt (K * riskScale c n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi := integral_mono (integrable_conservativeInterval_length c K n (sampleLaw P n))
    (integrable_const (2 * Real.sqrt (K * riskScale c n)))
    (conservativeInterval_length_le c K)
  simpa using hi

/-- Projection bounds make the observable contrast's squared loss integrable. -/
-- @node: integrable_observableEstimator_sq_loss
lemma integrable_observableEstimator_sq_loss (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (n : ℕ) :
    Integrable (fun s : Fin n → ObsHistory =>
      (observableEstimator c s - causalTarget P) ^ 2) (sampleLaw P n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      (observableEstimator c s - causalTarget P) ^ 2) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 * c.lambdaMax) ^ 2)
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs := observableEstimator_mem_range c s
  have ht := causalTarget_mem_range c P hP
  have habs : |observableEstimator c s - causalTarget P| ≤ 2 * c.lambdaMax := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hb : 0 ≤ 2 * c.lambdaMax := by
    linarith [c.lambdaMin_pos, c.lambdaMin_lt]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 habs

/-- Markov's inequality converts a squared-risk bound into coverage of the
clipped conservative interval. The only input is the risk at its radius. -/
-- @node: conservativeInterval_coverage_of_sqRisk
lemma conservativeInterval_coverage_of_sqRisk (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (n : ℕ) (hn : 3 ≤ n) (K alpha : ℝ) (hK : 0 < K)
    (hRisk : Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c)
      (causalTarget P) ≤ alpha * (K * riskScale c n)) :
    1 - alpha ≤ (sampleLaw P n).real
      {s | causalTarget P ∈ conservativeInterval c K s} := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let R := K * riskScale c n
  have hR : 0 < R := mul_pos hK (riskScale_pos c hn)
  let E := {s : Fin n → ObsHistory | |observableEstimator c s - causalTarget P| ≤
    Real.sqrt R}
  have hE : MeasurableSet E := by
    apply measurableSet_le _ measurable_const
    fun_prop
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun s : Fin n → ObsHistory =>
      sq_nonneg (observableEstimator c s - causalTarget P)))
    (integrable_observableEstimator_sq_loss c P hP n) R
  have hsub : Eᶜ ⊆ {s : Fin n → ObsHistory |
      R ≤ (observableEstimator c s - causalTarget P) ^ 2} := by
    intro s hs
    have hs' : Real.sqrt R < |observableEstimator c s - causalTarget P| :=
      lt_of_not_ge hs
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg R) (abs_nonneg _)).2 hs'
    rw [Real.sq_sqrt hR.le, sq_abs] at hsq
    exact hsq.le
  have hprob := measureReal_mono (μ := sampleLaw P n) hsub
  have hbound : (sampleLaw P n).real Eᶜ ≤ alpha := by
    have hmul := mul_le_mul_of_nonneg_left hprob hR.le
    change R * _ ≤ Causalean.Stat.sqRisk (sampleLaw P n)
      (observableEstimator c) (causalTarget P) at hmarkov
    change _ ≤ alpha * R at hRisk
    nlinarith [hmarkov, hRisk]
  have hcompl := measureReal_add_measureReal_compl (μ := sampleLaw P n) hE
  rw [probReal_univ] at hcompl
  have heq : {s : Fin n → ObsHistory | causalTarget P ∈ conservativeInterval c K s} = E := by
    ext s
    exact mem_conservativeInterval_iff c K (causalTarget P) s (causalTarget_mem_range c P hP)
  rw [heq]
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

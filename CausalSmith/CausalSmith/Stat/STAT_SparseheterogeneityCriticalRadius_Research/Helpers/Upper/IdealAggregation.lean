module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.IdealRisk
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Pilot
public import Mathlib.Probability.Moments.Variance

/-! Independent-cell aggregation for the ideal Poisson experiment. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

lemma independent_sum_sqRisk_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ι → Ω → ℝ) (target : ℝ)
    (hT : ∀ i, MemLp (T i) 2 μ) (hind : iIndepFun T μ) :
    (∫ ω, ((∑ i, T i ω) - target) ^ 2 ∂μ) =
      (∑ i, variance (T i) μ) +
        ((∑ i, ∫ ω, T i ω ∂μ) - target) ^ 2 := by
  have hsum : MemLp (fun ω => ∑ i, T i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hT i)
  have hvar : variance (fun ω => ∑ i, T i ω) μ =
      ∑ i, variance (T i) μ := by
    have hfun : (∑ i, T i) = (fun ω => ∑ i, T i ω) := by
      funext ω
      simp
    rw [← hfun]
    exact IndepFun.variance_sum (X := T) (s := Finset.univ)
      (fun i _ => hT i) (fun i _ j _ hij => hind.indepFun hij)
  rw [← hvar]
  have hInt := hsum.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hCross : Integrable (fun ω => (2 * target) * (∑ i, T i ω)) μ :=
    hInt.const_mul (2 * target)
  have hDiff : Integrable (fun ω => (∑ i, T i ω) ^ 2 -
      (2 * target) * (∑ i, T i ω)) μ := hsum.integrable_sq.sub hCross
  rw [show (fun ω => ((∑ i, T i ω) - target) ^ 2) = fun ω =>
      (∑ i, T i ω) ^ 2 - (2 * target) * (∑ i, T i ω) + target ^ 2 by
    funext ω
    ring]
  rw [integral_add hDiff (integrable_const _),
    integral_sub hsum.integrable_sq hCross, integral_const_mul,
    integral_const, probReal_univ, one_smul, variance_eq_sub hsum,
    integral_finsetSum _ (fun i _ => (hT i).integrable (by norm_num))]
  simp only [Pi.pow_apply]
  ring

abbrev IdealCellSample (n : ℕ) :=
  FiniteSample (SampleObs n) × (FiniteSample ℝ × FiniteSample ℝ)

noncomputable def idealCellLaw {n : ℕ} (P : Law n) (k : Fin n) :
    Measure (IdealCellSample n) :=
  (finitePoissonSampleLaw P.observedLaw
    (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)

noncomputable def idealProductLaw {n : ℕ} (P : Law n) :
    Measure (Fin n → IdealCellSample n) :=
  Measure.pi (fun k => idealCellLaw P k)

noncomputable instance idealCellLaw_isProbability {n : ℕ} (P : Law n)
    (k : Fin n) : IsProbabilityMeasure (idealCellLaw P k) := by
  unfold idealCellLaw cellOutcomePoissonLaw
  infer_instance

noncomputable instance idealProductLaw_isProbability {n : ℕ} (P : Law n) :
    IsProbabilityMeasure (idealProductLaw P) := by
  unfold idealProductLaw
  infer_instance

noncomputable def idealCellStatistic {n : ℕ} (P : Law n) (k : Fin n)
    (t rho : ℝ) (q : IdealCellSample n) : ℝ :=
  if 0 < P.cellMass k then idealSelectedCorrection P k t rho q else 0

lemma measurable_idealCellStatistic {n : ℕ} (P : Law n) (k : Fin n)
    (t rho : ℝ) : Measurable (idealCellStatistic P k t rho) := by
  unfold idealCellStatistic
  split
  · unfold idealSelectedCorrection
    exact Measurable.ite
      (measurableSet_le
        ((measurable_finiteSampleCellCount k).comp measurable_fst) measurable_const)
      ((measurable_idealLightCorrection P k t rho).comp measurable_snd)
      ((measurable_idealHeavyCorrection P k t).comp measurable_snd)
  · exact measurable_const

lemma idealCellStatistic_memLp_two {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    MemLp (idealCellStatistic P k t rho) 2 (idealCellLaw P k) := by
  rw [memLp_two_iff_integrable_sq
    (measurable_idealCellStatistic P k t rho).aestronglyMeasurable]
  by_cases hp : 0 < P.cellMass k
  · simpa only [idealCellStatistic, if_pos hp, idealCellLaw] using
      idealSelectedCorrection_sq_integrable M rho P k t hn hp hmean hvariance ht
  · simp [idealCellStatistic, hp]

lemma idealCellStatistic_first_moment {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ q, idealCellStatistic P k t rho q ∂idealCellLaw P k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        upperAuditWeights n rho P k := by
  by_cases hp : 0 < P.cellMass k
  · simpa only [idealCellStatistic, if_pos hp, idealCellLaw] using
      idealSelectedCorrection_first_moment M rho P k t hn hp hmean hvariance ht
  · have hp0 : P.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hp) (P.cellMass_range k).1
    rw [upperAuditWeights_eq_zero_of_cellMass_eq_zero rho P k hp0]
    simp [idealCellStatistic, hp]

/-- The canonical independent-cell ideal experiment has the concrete global
variance budget from equation (44). -/
lemma idealProduct_variance_le {n : ℕ} (M rho : ℝ) (P : Law n) (t : ℝ)
    (hn : 0 < n) (hoverlap : FixedOverlap P) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    variance (fun q : Fin n → IdealCellSample n =>
      ∑ k, idealCellStatistic P k t rho (q k)) (idealProductLaw P) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) := by
  have hLp (k : Fin n) :=
    idealCellStatistic_memLp_two M rho P k t hn hmean hvariance ht
  rw [show (fun q : Fin n → IdealCellSample n =>
      ∑ k, idealCellStatistic P k t rho (q k)) =
      ∑ k, fun q => idealCellStatistic P k t rho (q k) by
    funext q
    simp]
  unfold idealProductLaw
  rw [variance_sum_pi hLp]
  apply selectedCorrection_variance_sum_le_of_cell M rho t P
    (fun k => variance (idealCellStatistic P k t rho) (idealCellLaw P k))
    hn hoverlap hmean hvariance ht
  intro k
  by_cases hp : 0 < P.cellMass k
  · have hmem := hLp k
    rw [variance_eq_sub hmem]
    change (∫ q, idealCellStatistic P k t rho q ^ 2 ∂idealCellLaw P k) -
      (∫ q, idealCellStatistic P k t rho q ∂idealCellLaw P k) ^ 2 ≤ _
    simpa only [idealCellStatistic, if_pos hp, idealCellLaw] using
      idealSelectedCorrection_variance_le_cell M rho P k t hn hp hoverlap
        hmean hvariance ht
  · rw [show idealCellStatistic P k t rho = fun _ => 0 by
      funext q
      simp [idealCellStatistic, hp]]
    simp [variance_eq_integral]
    obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
    have hL : 0 ≤ ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k)) :=
      integral_nonneg fun N0 => integral_nonneg fun N1 =>
        mul_nonneg (conditionalNumeratorSecond_nonneg P k t N0 N1)
          (factorialCorrectionSquare_nonneg n rho N0 N1)
    have hH := heavyCellConditionalVariance_nonneg P k t
    have hp0 := (P.cellMass_range k).1
    have hbeta : 0 ≤ 1 - classificationProbability n rho P k :=
      sub_nonneg.mpr ha1
    exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hL)
        (mul_nonneg hbeta hH))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M))
            (sq_nonneg (P.cellMass k))) ha0) hbeta)

/-- Conditional ideal MSE, equations (45)--(46), retaining the pilot
displacement for later integration. -/
lemma idealProduct_sqRisk_le {n : ℕ} (M rho t : ℝ)
    (P : KnownRadiusClass n M rho) (ht : AdmissiblePilotValue M t) :
    (∫ q : Fin n → IdealCellSample n,
      (t + ∑ k, idealCellStatistic P.law k t rho (q k) -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
      ∂idealProductLaw P.law) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) +
      (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
        (M ^ 2 * rho ^ 2 +
          (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t) ^ 2) := by
  let T : Fin n → (Fin n → IdealCellSample n) → ℝ := fun k q =>
    idealCellStatistic P.law k t rho (q k)
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) P.n_ge_three
  have hcellLp (k : Fin n) := idealCellStatistic_memLp_two M rho P.law k t hn
    P.mean_envelope P.variance_envelope ht
  have hTLp (k : Fin n) : MemLp (T k) 2 (idealProductLaw P.law) := by
    exact hcellLp k |>.comp_measurePreserving
      (measurePreserving_eval (fun j => idealCellLaw P.law j) k)
  have hind : iIndepFun T (idealProductLaw P.law) := by
    unfold T idealProductLaw
    exact iIndepFun_pi fun k =>
      (measurable_idealCellStatistic P.law k t rho).aemeasurable
  have hrisk := independent_sum_sqRisk_eq (idealProductLaw P.law) T
    (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t) hTLp hind
  have hmeanProd (k : Fin n) :
      (∫ q, T k q ∂idealProductLaw P.law) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t) *
        upperAuditWeights n rho P.law k := by
    have hmap := measurePreserving_eval (fun j => idealCellLaw P.law j) k
    rw [show (∫ q, T k q ∂idealProductLaw P.law) =
        ∫ x, idealCellStatistic P.law k t rho x ∂idealCellLaw P.law k by
      unfold T idealProductLaw
      rw [← hmap.map_eq]
      exact (integral_map hmap.aemeasurable
        (measurable_idealCellStatistic P.law k t rho).aestronglyMeasurable).symm]
    exact idealCellStatistic_first_moment M rho P.law k t hn P.mean_envelope
      P.variance_envelope ht
  have hbias :
      ((∑ k, ∫ q, T k q ∂idealProductLaw P.law) -
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t)) ^ 2 ≤
      (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
        (M ^ 2 * rho ^ 2 +
          (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t) ^ 2) := by
    simp_rw [hmeanProd]
    rw [show (∑ k : Fin n,
        (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t) *
          upperAuditWeights n rho P.law k) -
          (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t) =
        ∑ k : Fin n, (upperAuditWeights n rho P.law k - P.law.cellMass k) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t) by
      have hid := selectedCorrection_sum_bias_identity rho t P.law
        (fun k => (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t) *
          upperAuditWeights n rho P.law k) (fun _ => rfl)
      linarith]
    exact selectedCorrection_audit_bias_sq_radius_le M rho t P
  have hvar := idealProduct_variance_le M rho P.law t hn P.overlap
    P.mean_envelope P.variance_envelope ht
  have hvarSum : (∑ k, variance (T k) (idealProductLaw P.law)) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) := by
    have hvs : variance (∑ k, T k) (idealProductLaw P.law) =
        ∑ k, variance (T k) (idealProductLaw P.law) :=
      IndepFun.variance_sum (X := T) (s := Finset.univ)
        (fun k _ => hTLp k) (fun i _ j _ hij => hind.indepFun hij)
    calc
      _ = variance (∑ k, T k) (idealProductLaw P.law) := hvs.symm
      _ = variance (fun q : Fin n → IdealCellSample n =>
          ∑ k, idealCellStatistic P.law k t rho (q k))
          (idealProductLaw P.law) := by
        congr 1
        funext q
        unfold T
        simp
      _ ≤ _ := hvar
  rw [show (fun q : Fin n → IdealCellSample n =>
      (t + ∑ k, idealCellStatistic P.law k t rho (q k) -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2) =
      fun q => ((∑ k, T k q) -
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t)) ^ 2 by
    funext q
    dsimp only [T]
    congr 1
    ring]
  rw [hrisk]
  exact add_le_add hvarSum hbias

/-- Integrating the conditional ideal experiment over the retained pilot
turns its only pilot-dependent term into the pilot MSE. -/
lemma idealProduct_pilot_sqRisk_le {n : ℕ} (M rho C : ℝ)
    (P : KnownRadiusClass n M rho)
    (hpilot : DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M) ≤
      C * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) :
    (∫ sample : Fin n → SampleObs n,
      ∫ q : Fin n → IdealCellSample n,
        (pilotTau n M sample +
          ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
          DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
        ∂idealProductLaw P.law
      ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) +
      (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
        (M ^ 2 * rho ^ 2 +
          C * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) := by
  let μ := DiscreteAteHeterogeneityFrontier.productLaw n P.law
  let target := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let V := 3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
    (degree n rho : ℝ) ^ 4 / n)
  let B := 2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hresMeas : StronglyMeasurable (fun sample : Fin n → SampleObs n =>
      (target - pilotTau n M sample) ^ 2) :=
    (((measurable_const.sub (pilotTau_measurable n M)).pow_const 2)).stronglyMeasurable
  have hresInt : Integrable (fun sample : Fin n → SampleObs n =>
      (target - pilotTau n M sample) ^ 2) μ := by
    apply Integrable.of_bound hresMeas.aestronglyMeasurable ((2 * M) ^ 2)
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ht := rawAte_mem_clip P
    have hp := pilotTau_range n M hM sample
    have habs : |target - pilotTau n M sample| ≤ 2 * M := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, hp.1, hp.2]
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (target - pilotTau n M sample))
        (mul_nonneg (by norm_num) hM)).2 habs
  have hB : 0 ≤ B := by
    unfold B
    positivity
  have hRhsInt : Integrable (fun sample : Fin n → SampleObs n =>
      V + B * (M ^ 2 * rho ^ 2 + (target - pilotTau n M sample) ^ 2)) μ := by
    have hsum : Integrable (fun sample : Fin n → SampleObs n =>
        M ^ 2 * rho ^ 2 + (target - pilotTau n M sample) ^ 2) μ :=
      (integrable_const (M ^ 2 * rho ^ 2)).add hresInt
    exact (integrable_const V).add (hsum.const_mul B)
  have hmono : (∫ sample : Fin n → SampleObs n,
      ∫ q : Fin n → IdealCellSample n,
        (pilotTau n M sample +
          ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
          target) ^ 2 ∂idealProductLaw P.law ∂μ) ≤
      ∫ sample : Fin n → SampleObs n,
        (V + B * (M ^ 2 * rho ^ 2 +
          (target - pilotTau n M sample) ^ 2)) ∂μ := by
    apply integral_mono_of_nonneg
    · filter_upwards with sample
      exact integral_nonneg fun q => sq_nonneg _
    · exact hRhsInt
    · filter_upwards with sample
      simpa only [target, V, B] using
        idealProduct_sqRisk_le M rho (pilotTau n M sample) P
          (pilotTau_range n M hM sample)
  calc
    _ ≤ ∫ sample : Fin n → SampleObs n,
        (V + B * (M ^ 2 * rho ^ 2 +
          (target - pilotTau n M sample) ^ 2)) ∂μ := hmono
    _ = V + B * (M ^ 2 * rho ^ 2 +
        DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M)) := by
      have hsum : Integrable (fun sample : Fin n → SampleObs n =>
          M ^ 2 * rho ^ 2 + (target - pilotTau n M sample) ^ 2) μ :=
        (integrable_const (M ^ 2 * rho ^ 2)).add hresInt
      have hsq : (∫ sample : Fin n → SampleObs n,
          (target - pilotTau n M sample) ^ 2 ∂μ) =
          DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M) := by
        unfold DiscreteAteHeterogeneityFrontier.mse μ target
        apply integral_congr_ae
        filter_upwards with sample
        ring
      rw [integral_add (integrable_const V) (hsum.const_mul B),
        integral_const, probReal_univ, one_smul, integral_const_mul,
        integral_add (integrable_const _) hresInt, integral_const,
        probReal_univ, one_smul, hsq]
    _ ≤ V + B * (M ^ 2 * rho ^ 2 +
        C * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) := by
      gcongr
    _ = _ := rfl

/-- Uniform pilot-integrated version of the ideal MSE bound. -/
-- keep: public uniform ideal-product risk endpoint before finite-sample transport
lemma idealProduct_pilot_sqRisk_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ n M rho (P : KnownRadiusClass n M rho),
      (∫ sample : Fin n → SampleObs n,
        ∫ q : Fin n → IdealCellSample n,
          (pilotTau n M sample +
            ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
            DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
          ∂idealProductLaw P.law
        ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) ≤
        3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
          (degree n rho : ℝ) ^ 4 / n) +
        (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
          (M ^ 2 * rho ^ 2 +
            C * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) := by
  obtain ⟨C, hC, hpilot⟩ := pilot_risk_bound
  refine ⟨C, hC, ?_⟩
  intro n M rho P
  exact idealProduct_pilot_sqRisk_le M rho C P
    (hpilot n M rho P P.n_ge_three)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

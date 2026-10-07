module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ClassifierMoments

/-! Conditional risk bounds for the ideal independently Poissonized selected
correction. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

lemma finitePoissonSample_count_ae_zero {X : Type*} [MeasurableSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] :
    ∀ᵐ s ∂finitePoissonSampleLaw Q 0, s.count = 0 := by
  have hset : MeasurableSet {s : FiniteSample X | s.count = 0} :=
    measurable_finiteSample_count (measurableSet_singleton 0)
  apply (mem_ae_iff_prob_eq_one hset).2
  change (finitePoissonSampleLaw Q 0) (FiniteSample.count ⁻¹' {0}) = 1
  rw [← Measure.map_apply measurable_finiteSample_count (measurableSet_singleton 0),
    finitePoissonSampleLaw_map_count, poissonMeasure_zero_eq_dirac]
  simp

lemma sq_integral_le_integral_sq_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Integrable f μ) (hfsq : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have hconst : Integrable (fun _ : X => c ^ 2) μ := integrable_const _
  have hlinear : Integrable (fun x => 2 * c * f x) μ := by
    simpa only [mul_assoc] using hf.const_mul (2 * c)
  have hnonneg : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  rw [show (fun x => (f x - c) ^ 2) =
      fun x => f x ^ 2 - 2 * c * f x + c ^ 2 by
    funext x
    ring] at hnonneg
  have hop : (fun x => f x ^ 2 - 2 * c * f x + c ^ 2) =
      ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
        (fun _ => c ^ 2) := by
    funext x
    rfl
  rw [hop] at hnonneg
  have hadd : integral μ (((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
      (fun _ => c ^ 2)) =
      integral μ ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) +
        integral μ (fun _ => c ^ 2) :=
    integral_add (hfsq.sub hlinear) hconst
  have hsub : integral μ ((fun x => f x ^ 2) - (fun x => 2 * c * f x)) =
      integral μ (fun x => f x ^ 2) - integral μ (fun x => 2 * c * f x) :=
    integral_sub hfsq hlinear
  rw [hadd, hsub, integral_const_mul] at hnonneg
  simp only [integral_const, probReal_univ, one_smul] at hnonneg
  dsimp only [c] at hnonneg
  nlinarith

lemma heavyAuditWeight_nonneg {n : ℕ} (P : Law n) (k : Fin n)
    (hn : 0 < n) : 0 ≤ heavyAuditWeight n P k := by
  rw [← heavyWeightedCount_integral_armMass P k hn]
  apply integral_nonneg
  intro N0
  apply integral_nonneg
  intro N1
  change 0 ≤ (N0 : ℝ) * (N1 : ℝ) * heavyCoefficient n N0 N1
  by_cases hz : N0 = 0 ∨ N1 = 0
  · rw [heavyCoefficient, if_pos hz]
    positivity
  · rw [heavyCoefficient, if_neg hz]
    have hm : 0 < blockMean n := blockMean_pos n hn
    positivity

/-- Concrete equation (44) input for one occupied cell. -/
lemma idealSelectedCorrection_variance_le_cell {n : ℕ} (M rho : ℝ)
    (P : Law n) (k : Fin n) (t : ℝ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ q, idealSelectedCorrection P k t rho q ^ 2
      ∂((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) -
      (∫ q, idealSelectedCorrection P k t rho q
        ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) ^ 2 ≤
      3 * classificationProbability n rho P k *
        (∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) +
      (1 - classificationProbability n rho P k) *
        heavyCellConditionalVariance P k t +
      8 * M ^ 2 * P.cellMass k ^ 2 * classificationProbability n rho P k *
        (1 - classificationProbability n rho P k) := by
  let L2 := ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
      factorialCorrectionSquare n rho N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))
  let H2 := ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))
  let l := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
    lightAuditWeight n rho P k
  let h := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
    heavyAuditWeight n P k
  have hL20 : 0 ≤ L2 := by
    dsimp only [L2]
    exact integral_nonneg fun N0 => integral_nonneg fun N1 =>
      mul_nonneg (conditionalNumeratorSecond_nonneg P k t N0 N1)
        (factorialCorrectionSquare_nonneg n rho N0 N1)
  have hlightVar : L2 - l ^ 2 ≤ L2 := by nlinarith [sq_nonneg l]
  let ν := cellOutcomePoissonLaw P k
  letI : IsProbabilityMeasure ν := by dsimp only [ν, cellOutcomePoissonLaw]; infer_instance
  have hlightJensen := sq_integral_le_integral_sq_of_integrable ν
    (idealLightCorrection P k t rho)
    (idealLightCorrection_integrable M rho P k t hn hp hmean hvariance ht)
    (idealLightCorrection_sq_integrable M rho P k t hn hp hmean hvariance ht)
  have hlightMean : l ^ 2 ≤ L2 := by
    dsimp only [ν] at hlightJensen
    have hfirst : (∫ q, idealLightCorrection P k t rho q
        ∂cellOutcomePoissonLaw P k) =
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          lightAuditWeight n rho P k := by
      simpa only [idealLightCorrection, cellOutcomePoissonLaw] using
        lightCorrection_first_moment_eq_weight M rho P k t hn hp hmean
          hvariance ht
    have hsecond : (∫ q, idealLightCorrection P k t rho q ^ 2
        ∂cellOutcomePoissonLaw P k) = L2 := by
      simpa only [idealLightCorrection, cellOutcomePoissonLaw] using
        lightCorrection_second_moment_cell M rho P k t _ _ hn hp hmean
          hvariance ht
    rw [hfirst, hsecond] at hlightJensen
    simpa only [l] using hlightJensen
  have hheavyVar : H2 - h ^ 2 ≤ heavyCellConditionalVariance P k t := by
    exact heavyCorrection_variance_le_conditional M P k t hn hp hvariance
  have hw0 : 0 ≤ heavyAuditWeight n P k := heavyAuditWeight_nonneg P k hn
  have hwp : heavyAuditWeight n P k ≤ P.cellMass k := by
    have hb := (heavyAuditWeight_bias_bound P k hn hoverlap).1
    linarith
  have hp0 := (P.cellMass_range k).1
  have hd := cellEffect_sub_pilot_abs_le P k t hp hmean ht
  have habs0 : 0 ≤ |DiscreteAteHeterogeneityFrontier.cellEffect P k - t| :=
    abs_nonneg _
  have hM0 : 0 ≤ M := by nlinarith
  have hheavyMean : h ^ 2 ≤ 4 * M ^ 2 * P.cellMass k ^ 2 := by
    dsimp only [h]
    have hd2 : (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 ≤
        4 * M ^ 2 := by
      have hs := sq_abs (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)
      nlinarith
    have hw2 : heavyAuditWeight n P k ^ 2 ≤ P.cellMass k ^ 2 := by nlinarith
    rw [mul_pow]
    exact mul_le_mul hd2 hw2 (sq_nonneg _) (by positivity)
  rw [idealSelectedCorrection_variance_eq M rho P k t hn hp hmean hvariance ht]
  have hmix := classifierMixtureVariance_le_three_light
    (heavyVariance := H2 - h ^ 2)
    (classificationProbability_mem_Icc rho P k) hL20 hlightVar hlightMean
    hheavyMean
  exact hmix.trans (by
    dsimp only [L2, H2, l, h] at hheavyVar ⊢
    gcongr
    exact sub_nonneg.mpr (classificationProbability_mem_Icc rho P k).2)

/-- Concrete global conditional variance bound for the ideal selected
correction vector. -/
-- keep: global conditional variance certificate for the ideal selected correction
lemma idealSelectedCorrection_variance_sum_le {n : ℕ} (M rho : ℝ)
    (P : Law n) (t : ℝ) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∑ k : Fin n,
      ((∫ q, idealSelectedCorrection P k t rho q ^ 2
        ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) -
       (∫ q, idealSelectedCorrection P k t rho q
        ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))) ^ 2)) ≤
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n) := by
  apply selectedCorrection_variance_sum_le_of_cell M rho t P _ hn hoverlap
    hmean hvariance ht
  intro k
  by_cases hp : 0 < P.cellMass k
  · exact idealSelectedCorrection_variance_le_cell M rho P k t hn hp hoverlap
      hmean hvariance ht
  · have hp0 : P.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hp) (P.cellMass_range k).1
    have harm (u : Bool) : armMass P u k = 0 := by simp [armMass, hp0]
    have hrate (u : Bool) :
        Real.toNNReal (blockMean n * armMass P u k) = 0 := by simp [harm]
    have houtcome : ∀ᵐ q ∂cellOutcomePoissonLaw P k,
        idealLightCorrection P k t rho q = 0 ∧
          idealHeavyCorrection P k t q = 0 := by
      letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
        P.outcome_isProbability false k
      letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
        P.outcome_isProbability true k
      unfold cellOutcomePoissonLaw
      rw [hrate false, hrate true]
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_eq_fun (measurable_idealLightCorrection P k t rho)
          measurable_const).inter
        (measurableSet_eq_fun (measurable_idealHeavyCorrection P k t)
          measurable_const))).2
      filter_upwards [finitePoissonSample_count_ae_zero (P.outcomeLaw false k)]
        with q0 hq0
      filter_upwards [finitePoissonSample_count_ae_zero (P.outcomeLaw true k)]
        with q1 hq1
      constructor
      · unfold idealLightCorrection
        change Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
            (centeredNumeratorKernel P k t) q0 q1 *
          lightFactorialCoefficient n rho q0.count q1.count = 0
        rw [show lightFactorialCoefficient n rho q0.count q1.count = 0 by
          simp [lightFactorialCoefficient, hq0, hq1]]
        simp
      · unfold idealHeavyCorrection
        change Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
            (centeredNumeratorKernel P k t) q0 q1 *
          heavyCoefficient n q0.count q1.count = 0
        rw [show heavyCoefficient n q0.count q1.count = 0 by
          simp [heavyCoefficient, hq0, hq1]]
        simp
    have hselected : ∀ᵐ q ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)),
        idealSelectedCorrection P k t rho q = 0 := by
      letI : SFinite (cellOutcomePoissonLaw P k) := by
        unfold cellOutcomePoissonLaw
        infer_instance
      have hset : MeasurableSet {q : FiniteSample (SampleObs n) ×
          (FiniteSample ℝ × FiniteSample ℝ) |
          idealSelectedCorrection P k t rho q = 0} := by
        have hm : Measurable (idealSelectedCorrection P k t rho) := by
          unfold idealSelectedCorrection
          exact Measurable.ite
            (measurableSet_le
              ((measurable_finiteSampleCellCount k).comp measurable_fst)
              measurable_const)
            ((measurable_idealLightCorrection P k t rho).comp measurable_snd)
            ((measurable_idealHeavyCorrection P k t).comp measurable_snd)
        exact measurableSet_eq_fun hm measurable_const
      apply (Measure.ae_prod_iff_ae_ae hset).2
      filter_upwards with qc
      filter_upwards [houtcome] with qe hqe
      unfold idealSelectedCorrection
      split <;> simp_all
    have hselectedSq : (fun q => idealSelectedCorrection P k t rho q ^ 2) =ᵐ[
        ((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k))]
        (fun _ => 0) := by
      filter_upwards [hselected] with q hq
      rw [hq]
      norm_num
    rw [integral_congr_ae hselectedSq]
    rw [integral_congr_ae hselected]
    rw [heavyCellConditionalVariance_eq_zero_of_cellMass_eq_zero P k t hp0]
    simp [harm, hp0, poissonMeasure_zero_eq_dirac, factorialCorrectionSquare]

/-- Radius-aware form of equation (45), before integrating the pilot. -/
lemma selectedCorrection_audit_bias_radius_le {n : ℕ} (M rho t : ℝ)
    (P : KnownRadiusClass n M rho) :
    |∑ k : Fin n, (upperAuditWeights n rho P.law k - P.law.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t)| ≤
      (M * rho +
        |DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t|) *
        (196612 / (degree n rho : ℝ)) := by
  let τ := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  have hfactor : 0 ≤ M * rho + |τ - t| := by
    have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
    have hrho : 0 ≤ rho := P.radius.1.1
    positivity
  have hcell (k : Fin n) :
      |(upperAuditWeights n rho P.law k - P.law.cellMass k) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t)| ≤
        |upperAuditWeights n rho P.law k - P.law.cellMass k| *
          (M * rho + |τ - t|) := by
    by_cases hp : 0 < P.law.cellMass k
    · rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hrad := P.radius.2 k hp
      change |DiscreteAteHeterogeneityFrontier.cellEffect P.law k - τ| ≤
        rho * M at hrad
      have htri : |DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t| ≤
          |DiscreteAteHeterogeneityFrontier.cellEffect P.law k - τ| + |τ - t| := by
        rw [show DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t =
          (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - τ) +
            (τ - t) by ring]
        exact abs_add_le _ _
      calc
        _ ≤ _ := htri
        _ ≤ _ := by nlinarith
    · have hp0 : P.law.cellMass k = 0 :=
        le_antisymm (le_of_not_gt hp) (P.law.cellMass_range k).1
      simp [hp0, upperAuditWeights_eq_zero_of_cellMass_eq_zero rho P.law k hp0]
  calc
    _ ≤ ∑ k : Fin n,
        |(upperAuditWeights n rho P.law k - P.law.cellMass k) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n,
        |upperAuditWeights n rho P.law k - P.law.cellMass k| *
          (M * rho + |τ - t|) := Finset.sum_le_sum fun k _ => hcell k
    _ = (M * rho + |τ - t|) *
        (∑ k : Fin n, |upperAuditWeights n rho P.law k - P.law.cellMass k|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (M * rho + |τ - t|) *
        (196612 / (degree n rho : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (audit_weight_bias_bound_explicit rho P.law
          (lt_of_lt_of_le (by norm_num) P.n_ge_three) P.overlap) hfactor

lemma selectedCorrection_audit_bias_sq_radius_le {n : ℕ} (M rho t : ℝ)
    (P : KnownRadiusClass n M rho) :
    (∑ k : Fin n, (upperAuditWeights n rho P.law k - P.law.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t)) ^ 2 ≤
      (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
        (M ^ 2 * rho ^ 2 +
          (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law - t) ^ 2) := by
  let τ := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let K : ℝ := degree n rho
  have hKnat : 0 < degree n rho := by simp [degree]
  have hK : 0 < K := by dsimp only [K]; exact_mod_cast hKnat
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hrho : 0 ≤ rho := P.radius.1.1
  have hb := selectedCorrection_audit_bias_radius_le M rho t P
  have hrhs : 0 ≤ (M * rho + |τ - t|) * (196612 / K) := by positivity
  have hsq :
      (∑ k : Fin n, (upperAuditWeights n rho P.law k - P.law.cellMass k) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P.law k - t)) ^ 2 ≤
        ((M * rho + |τ - t|) * (196612 / K)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hrhs).2 hb
  calc
    _ ≤ ((M * rho + |τ - t|) * (196612 / K)) ^ 2 := hsq
    _ ≤ (2 * 196612 ^ 2 / K ^ 2) *
        (M ^ 2 * rho ^ 2 + (τ - t) ^ 2) := by
      have habsSq := sq_abs (τ - t)
      have htwo : (M * rho + |τ - t|) ^ 2 ≤
          2 * ((M * rho) ^ 2 + |τ - t| ^ 2) := by
        nlinarith [sq_nonneg (M * rho - |τ - t|)]
      rw [mul_pow]
      have hscale : 0 ≤ (196612 / K) ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_right htwo hscale
      calc
        (M * rho + |τ - t|) ^ 2 * (196612 / K) ^ 2 ≤
            2 * ((M * rho) ^ 2 + |τ - t| ^ 2) * (196612 / K) ^ 2 := this
        _ = (2 * 196612 ^ 2 / K ^ 2) *
            (M ^ 2 * rho ^ 2 + (τ - t) ^ 2) := by
          rw [habsSq]
          field_simp

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Variance
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightFactorialMoment

/-! Two-arm composition of the light factorial second-moment bound. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment
open Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

/-- Pointwise form of equations (33)--(34), ready for the two independent
Poisson integrations. -/
lemma lightAuditIntegrand_le {n : ℕ} (M rho : ℝ) (P : Law n) (k : Fin n)
    (t : ℝ) (N0 N1 : ℕ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1 ≤
      12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) *
        (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
          (FK (degree n rho) (blockMean n * lightScale n rho) N0 ^ 2 +
            FK (degree n rho) (blockMean n * lightScale n rho) N1 ^ 2) := by
  have hM : 0 ≤ M := by
    have h := hmean true k hp
    linarith [abs_nonneg (P.outcomeMean true k)]
  have hB : 0 < lightScale n rho := lightScale_pos n rho hn
  have hm : 0 < blockMean n := by
    simp only [blockMean, postPilotSize, pilotSize]
    have : 0 < n - n / 2 := by omega
    positivity
  by_cases h0 : N0 = 0
  · subst N0
    simp [factorialCorrectionSquare]
  by_cases h1 : N1 = 0
  · subst N1
    simp [factorialCorrectionSquare]
  have hnum := conditionalNumeratorSecond_le_six M P k t N0 N1 hp hmean hvariance ht
  have hcorr : factorialCorrectionSquare n rho N0 N1 =
      ((FK (degree n rho) (blockMean n * lightScale n rho) N0 +
        FK (degree n rho) (blockMean n * lightScale n rho) N1) /
          (lightScale n rho * blockMean n ^ 2)) ^ 2 := by
    rw [factorialCorrectionSquare_eq_lightFactorialCoefficient_sq,
      lightFactorialCoefficient_eq_FK rho N0 N1 hn h0 h1]
  rw [hcorr]
  have hcorr0 : 0 ≤
      ((FK (degree n rho) (blockMean n * lightScale n rho) N0 +
        FK (degree n rho) (blockMean n * lightScale n rho) N1) /
          (lightScale n rho * blockMean n ^ 2)) ^ 2 := sq_nonneg _
  calc
    _ ≤ (6 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2) *
        ((FK (degree n rho) (blockMean n * lightScale n rho) N0 +
          FK (degree n rho) (blockMean n * lightScale n rho) N1) /
            (lightScale n rho * blockMean n ^ 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right hnum hcorr0
    _ ≤ 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) *
        (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
          (FK (degree n rho) (blockMean n * lightScale n rho) N0 ^ 2 +
            FK (degree n rho) (blockMean n * lightScale n rho) N1 ^ 2) := by
      let a := FK (degree n rho) (blockMean n * lightScale n rho) N0
      let b := FK (degree n rho) (blockMean n * lightScale n rho) N1
      have hs : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
        nlinarith [sq_nonneg (a - b)]
      have hden :
          ((a + b) / (lightScale n rho * blockMean n ^ 2)) ^ 2 =
            (a + b) ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) := by
        rw [div_pow]
        ring
      change (6 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2) *
          ((a + b) / (lightScale n rho * blockMean n ^ 2)) ^ 2 ≤ _
      rw [hden]
      calc
        _ = (6 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 /
            (lightScale n rho ^ 2 * blockMean n ^ 4)) * (a + b) ^ 2 := by ring
        _ ≤ (6 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 /
            (lightScale n rho ^ 2 * blockMean n ^ 4)) *
              (2 * (a ^ 2 + b ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hs
          positivity
        _ = _ := by dsimp [a, b]; ring

noncomputable def lightMomentEnvelope (K : ℕ) (R : ℝ) (N0 N1 : ℕ) : ℝ :=
  (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 * (FK K R N0 ^ 2 + FK K R N1 ^ 2)

lemma lightMomentEnvelope_integrable_inner (K : ℕ) (R : ℝ) (rate1 : ℝ≥0)
    (N0 : ℕ) :
    Integrable (fun N1 : ℕ => lightMomentEnvelope K R N0 N1)
      (poissonMeasure rate1) := by
  rw [show (fun N1 : ℕ => lightMomentEnvelope K R N0 N1) =
      fun N1 : ℕ =>
        ((N0 : ℝ) ^ 2 * FK K R N0 ^ 2) * (N1 : ℝ) ^ 2 +
        (N0 : ℝ) ^ 2 * ((N1 : ℝ) ^ 2 * FK K R N1 ^ 2) by
    funext N1
    simp only [lightMomentEnvelope]
    ring]
  exact ((integrable_poisson_count_sq rate1).const_mul _).add
    ((count_sq_FK_sq_integrable K R rate1).const_mul _)

lemma lightMomentEnvelope_inner_integral (K : ℕ) (R : ℝ) (rate1 : ℝ≥0)
    (N0 : ℕ) :
    (∫ N1 : ℕ, lightMomentEnvelope K R N0 N1 ∂poissonMeasure rate1) =
      ((N0 : ℝ) ^ 2 * FK K R N0 ^ 2) *
          ((rate1 : ℝ) ^ 2 + (rate1 : ℝ)) +
        (N0 : ℝ) ^ 2 *
          (∫ N1 : ℕ, (N1 : ℝ) ^ 2 * FK K R N1 ^ 2
            ∂poissonMeasure rate1) := by
  rw [show (fun N1 : ℕ => lightMomentEnvelope K R N0 N1) =
      fun N1 : ℕ =>
        ((N0 : ℝ) ^ 2 * FK K R N0 ^ 2) * (N1 : ℝ) ^ 2 +
        (N0 : ℝ) ^ 2 * ((N1 : ℝ) ^ 2 * FK K R N1 ^ 2) by
    funext N1
    simp only [lightMomentEnvelope]
    ring]
  rw [integral_add, integral_const_mul, integral_const_mul,
    poisson_count_second_moment]
  · exact (integrable_poisson_count_sq rate1).const_mul _
  · exact (count_sq_FK_sq_integrable K R rate1).const_mul _

lemma lightMomentEnvelope_integrable_outer (K : ℕ) (R : ℝ)
    (rate0 rate1 : ℝ≥0) :
    Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, lightMomentEnvelope K R N0 N1 ∂poissonMeasure rate1)
      (poissonMeasure rate0) := by
  rw [show (fun N0 : ℕ =>
      ∫ N1 : ℕ, lightMomentEnvelope K R N0 N1 ∂poissonMeasure rate1) =
      fun N0 : ℕ =>
        ((N0 : ℝ) ^ 2 * FK K R N0 ^ 2) *
            ((rate1 : ℝ) ^ 2 + (rate1 : ℝ)) +
          (N0 : ℝ) ^ 2 *
            (∫ N1 : ℕ, (N1 : ℝ) ^ 2 * FK K R N1 ^ 2
              ∂poissonMeasure rate1) by
    funext N0
    exact lightMomentEnvelope_inner_integral K R rate1 N0]
  exact ((count_sq_FK_sq_integrable K R rate0).mul_const _).add
    ((integrable_poisson_count_sq rate0).mul_const _)

/-- Independence reduces the two-arm polynomial envelope to two one-count
second moments. -/
lemma lightMomentEnvelope_iterated_integral (K : ℕ) (R : ℝ)
    (rate0 rate1 : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, lightMomentEnvelope K R N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0) =
      (∫ N0 : ℕ, (N0 : ℝ) ^ 2 * FK K R N0 ^ 2
        ∂poissonMeasure rate0) * ((rate1 : ℝ) ^ 2 + (rate1 : ℝ)) +
      ((rate0 : ℝ) ^ 2 + (rate0 : ℝ)) *
        (∫ N1 : ℕ, (N1 : ℝ) ^ 2 * FK K R N1 ^ 2
          ∂poissonMeasure rate1) := by
  rw [show (fun N0 : ℕ =>
      ∫ N1 : ℕ, lightMomentEnvelope K R N0 N1 ∂poissonMeasure rate1) =
      fun N0 : ℕ =>
        ((N0 : ℝ) ^ 2 * FK K R N0 ^ 2) *
            ((rate1 : ℝ) ^ 2 + (rate1 : ℝ)) +
          (N0 : ℝ) ^ 2 *
            (∫ N1 : ℕ, (N1 : ℝ) ^ 2 * FK K R N1 ^ 2
              ∂poissonMeasure rate1) by
    funext N0
    exact lightMomentEnvelope_inner_integral K R rate1 N0]
  rw [integral_add, integral_mul_const, integral_mul_const,
    poisson_count_second_moment]
  · exact (count_sq_FK_sq_integrable K R rate0).mul_const _
  · exact (integrable_poisson_count_sq rate0).mul_const _

lemma lightMomentEnvelope_iterated_integral_le (K : ℕ) (x0 x1 : ℝ)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hK : 1 ≤ K) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
        lightMomentEnvelope K (4096 * (K : ℝ)) N0 N1
        ∂poissonMeasure (Real.toNNReal (4096 * (K : ℝ) * x1))
        ∂poissonMeasure (Real.toNNReal (4096 * (K : ℝ) * x0))) ≤
      ((4096 * (K : ℝ)) ^ 2 * x0 * (1 + x0) ^ (2 * K) *
          (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
            Real.exp ((K : ℝ) / 4096)) *
          ((4096 * (K : ℝ) * x1) ^ 2 + 4096 * (K : ℝ) * x1) +
        ((4096 * (K : ℝ) * x0) ^ 2 + 4096 * (K : ℝ) * x0) *
          ((4096 * (K : ℝ)) ^ 2 * x1 * (1 + x1) ^ (2 * K) *
            (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
              Real.exp ((K : ℝ) / 4096)) := by
  rw [lightMomentEnvelope_iterated_integral]
  have hr0 : ((Real.toNNReal (4096 * (K : ℝ) * x0) : ℝ)) =
      4096 * (K : ℝ) * x0 := by
    exact Real.coe_toNNReal _
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hx0)
  have hr1 : ((Real.toNNReal (4096 * (K : ℝ) * x1) : ℝ)) =
      4096 * (K : ℝ) * x1 := by
    exact Real.coe_toNNReal _
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hx1)
  rw [hr0, hr1]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right (poisson_count_sq_FK_sq_le K x0 hx0 hK)
    positivity
  · apply mul_le_mul_of_nonneg_left (poisson_count_sq_FK_sq_le K x1 hx1 hK)
    positivity

lemma conditionalNumeratorSecond_nonneg {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) (N0 N1 : ℕ) : 0 ≤ conditionalNumeratorSecond P k t N0 N1 := by
  have hV0 : 0 ≤ ∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hV1 : 0 ≤ ∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k :=
    integral_nonneg (fun _ => sq_nonneg _)
  unfold conditionalNumeratorSecond
  positivity

/-- The exact light conditional second-moment kernel is integrable in the
inner Poisson count. -/
lemma lightAuditIntegrand_integrable_inner {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate1 : ℝ≥0) (N0 : ℕ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    Integrable (fun N1 : ℕ => conditionalNumeratorSecond P k t N0 N1 *
      factorialCorrectionSquare n rho N0 N1) (poissonMeasure rate1) := by
  let c : ℝ := 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4)
  have henv := (lightMomentEnvelope_integrable_inner (degree n rho)
    (blockMean n * lightScale n rho) rate1 N0).const_mul c
  apply henv.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with N1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (conditionalNumeratorSecond_nonneg P k t N0 N1)
    (factorialCorrectionSquare_nonneg n rho N0 N1))]
  calc
    _ ≤ 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) *
        (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
          (FK (degree n rho) (blockMean n * lightScale n rho) N0 ^ 2 +
            FK (degree n rho) (blockMean n * lightScale n rho) N1 ^ 2) :=
      lightAuditIntegrand_le M rho P k t N0 N1 hn hp hmean hvariance ht
    _ = _ := by dsimp only [c, lightMomentEnvelope]; ring

/-- The exact light conditional second-moment kernel is integrable after the
outer Poisson count integration. -/
lemma lightAuditIntegrand_integrable_outer {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1 ∂poissonMeasure rate1)
      (poissonMeasure rate0) := by
  let c : ℝ := 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4)
  have henv := (lightMomentEnvelope_integrable_outer (degree n rho)
    (blockMean n * lightScale n rho) rate0 rate1).const_mul c
  apply henv.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with N0
  have hinner := lightAuditIntegrand_integrable_inner M rho P k t rate1 N0
    hn hp hmean hvariance ht
  have hle : (∫ N1 : ℕ, conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1 ∂poissonMeasure rate1) ≤
      ∫ N1 : ℕ, c * lightMomentEnvelope (degree n rho)
        (blockMean n * lightScale n rho) N0 N1 ∂poissonMeasure rate1 := by
    apply integral_mono hinner
      ((lightMomentEnvelope_integrable_inner (degree n rho)
        (blockMean n * lightScale n rho) rate1 N0).const_mul c)
    intro N1
    calc
      _ ≤ 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) *
          (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
            (FK (degree n rho) (blockMean n * lightScale n rho) N0 ^ 2 +
              FK (degree n rho) (blockMean n * lightScale n rho) N1 ^ 2) :=
        lightAuditIntegrand_le M rho P k t N0 N1 hn hp hmean hvariance ht
      _ = _ := by dsimp only [c, lightMomentEnvelope]; ring
  rw [integral_const_mul] at hle
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun N1 => mul_nonneg
    (conditionalNumeratorSecond_nonneg P k t N0 N1)
    (factorialCorrectionSquare_nonneg n rho N0 N1))]
  exact hle

/-- Equations (33)--(35), retaining the exact two-arm moment envelope. -/
lemma lightAudit_iterated_integral_le_envelope {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
        conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0) ≤
      (12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4)) *
        (∫ N0 : ℕ, ∫ N1 : ℕ,
          lightMomentEnvelope (degree n rho)
            (blockMean n * lightScale n rho) N0 N1
          ∂poissonMeasure rate1 ∂poissonMeasure rate0) := by
  let c : ℝ := 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hinner (N0 : ℕ) :
      (∫ N1 : ℕ, conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1 ∂poissonMeasure rate1) ≤
        ∫ N1 : ℕ, c * lightMomentEnvelope (degree n rho)
          (blockMean n * lightScale n rho) N0 N1 ∂poissonMeasure rate1 := by
    apply integral_mono_of_nonneg
    · filter_upwards [] with N1
      exact mul_nonneg (conditionalNumeratorSecond_nonneg P k t N0 N1)
        (factorialCorrectionSquare_nonneg n rho N0 N1)
    · exact (lightMomentEnvelope_integrable_inner (degree n rho)
        (blockMean n * lightScale n rho) rate1 N0).const_mul c
    · filter_upwards [] with N1
      dsimp only [c, lightMomentEnvelope]
      calc
        _ ≤ 12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4) *
            (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
              (FK (degree n rho) (blockMean n * lightScale n rho) N0 ^ 2 +
                FK (degree n rho) (blockMean n * lightScale n rho) N1 ^ 2) :=
          lightAuditIntegrand_le M rho P k t N0 N1 hn hp hmean hvariance ht
        _ = _ := by ring
  calc
    _ ≤ ∫ N0 : ℕ, ∫ N1 : ℕ, c *
          lightMomentEnvelope (degree n rho)
            (blockMean n * lightScale n rho) N0 N1
          ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with N0
        exact integral_nonneg (fun N1 => mul_nonneg
          (conditionalNumeratorSecond_nonneg P k t N0 N1)
          (factorialCorrectionSquare_nonneg n rho N0 N1))
      · rw [show (fun N0 : ℕ => ∫ N1 : ℕ, c *
            lightMomentEnvelope (degree n rho)
              (blockMean n * lightScale n rho) N0 N1
            ∂poissonMeasure rate1) =
            fun N0 : ℕ => c * (∫ N1 : ℕ,
              lightMomentEnvelope (degree n rho)
                (blockMean n * lightScale n rho) N0 N1
              ∂poissonMeasure rate1) by
          funext N0
          rw [integral_const_mul]]
        exact (lightMomentEnvelope_integrable_outer (degree n rho)
          (blockMean n * lightScale n rho) rate0 rate1).const_mul c
      · filter_upwards [] with N0
        exact hinner N0
    _ = _ := by
      simp_rw [integral_const_mul]
      rfl

noncomputable def lightCellMomentBound {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) : ℝ :=
  let K := degree n rho
  let B := lightScale n rho
  let m := blockMean n
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  12 * M ^ 2 / (B ^ 2 * m ^ 4) *
    (((4096 * (K : ℝ)) ^ 2 * x0 * (1 + x0) ^ (2 * K) *
        (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
          Real.exp ((K : ℝ) / 4096)) *
        ((4096 * (K : ℝ) * x1) ^ 2 + 4096 * (K : ℝ) * x1) +
      ((4096 * (K : ℝ) * x0) ^ 2 + 4096 * (K : ℝ) * x0) *
        ((4096 * (K : ℝ)) ^ 2 * x1 * (1 + x1) ^ (2 * K) *
          (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
            Real.exp ((K : ℝ) / 4096)))

/-- Per-cell light second-moment bound before the classifier summation. -/
lemma lightAudit_cell_le {n : ℕ} (M rho : ℝ) (P : Law n) (k : Fin n)
    (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
        conditionalNumeratorSecond P k t N0 N1 *
          factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) ≤
      lightCellMomentBound M rho P k := by
  let K := degree n rho
  let B := lightScale n rho
  let m := blockMean n
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  have hB : 0 < B := lightScale_pos n rho hn
  have hx0 : 0 ≤ x0 := div_nonneg (by
    dsimp [x0, armMass]
    have hpRange := P.cellMass_range k
    have heRange := P.propensity_range k
    exact mul_nonneg hpRange.1 (sub_nonneg.mpr heRange.2)) hB.le
  have hx1 : 0 ≤ x1 := div_nonneg (by
    dsimp [x1, armMass]
    have hpRange := P.cellMass_range k
    have heRange := P.propensity_range k
    exact mul_nonneg hpRange.1 heRange.1) hB.le
  have hK : 1 ≤ K := by simp [K, degree]
  have hR : m * B = 4096 * (K : ℝ) := blockMean_mul_lightScale n rho hn
  have hr0 : m * armMass P false k = 4096 * (K : ℝ) * x0 := by
    dsimp [x0]
    rw [← hR]
    field_simp
  have hr1 : m * armMass P true k = 4096 * (K : ℝ) * x1 := by
    dsimp [x1]
    rw [← hR]
    field_simp
  calc
    _ ≤ (12 * M ^ 2 / (B ^ 2 * m ^ 4)) *
        (∫ N0 : ℕ, ∫ N1 : ℕ,
          lightMomentEnvelope K (m * B) N0 N1
          ∂poissonMeasure (Real.toNNReal (m * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (m * armMass P false k))) := by
      simpa only [K, B, m] using lightAudit_iterated_integral_le_envelope
        M rho P k t (Real.toNNReal (blockMean n * armMass P false k))
          (Real.toNNReal (blockMean n * armMass P true k)) hn hp hmean hvariance ht
    _ ≤ lightCellMomentBound M rho P k := by
      apply mul_le_mul_of_nonneg_left
      · rw [hR, hr0, hr1]
        exact lightMomentEnvelope_iterated_integral_le K x0 x1 hx0 hx1 hK
      · positivity

private lemma exp_tail_mul_power_le_self (K q : ℕ) (z : ℝ)
    (hK : 2 ≤ K) (hq : q ≤ 3) (hz : 1 < z) :
    Real.exp (-512 * (K : ℝ) * z) * z ^ q * (1 + z) ^ (2 * K) ≤ z := by
  have hz0 : 0 < z := lt_trans zero_lt_one hz
  have h1z : 0 < 1 + z := by linarith
  have hlogz : Real.log z ≤ z := Real.log_le_self hz0.le
  have hlog1z : Real.log (1 + z) ≤ z := by
    exact (Real.log_le_sub_one_of_pos h1z).trans_eq (by ring)
  have hqR : (q : ℝ) ≤ 3 := by exact_mod_cast hq
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hqlog : (q : ℝ) * Real.log z ≤ 3 * z := by
    calc
      _ ≤ (q : ℝ) * z := mul_le_mul_of_nonneg_left hlogz (Nat.cast_nonneg _)
      _ ≤ 3 * z := mul_le_mul_of_nonneg_right hqR hz0.le
  have h2klog : (2 * K : ℕ) * Real.log (1 + z) ≤
      (2 * (K : ℝ)) * z := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hlog1z (by positivity)
  have hexponent :
      -512 * (K : ℝ) * z + (q : ℝ) * Real.log z +
          (2 * K : ℕ) * Real.log (1 + z) ≤ Real.log z := by
    have hzlog0 : 0 ≤ Real.log z := Real.log_nonneg hz.le
    have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  calc
    _ = Real.exp (-512 * (K : ℝ) * z + (q : ℝ) * Real.log z +
        (2 * K : ℕ) * Real.log (1 + z)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hz0, Real.exp_log h1z]
    _ ≤ Real.exp (Real.log z) := Real.exp_le_exp.mpr hexponent
    _ = z := Real.exp_log hz0

/-- Coarse equation (36), with `exp(2K)` in place of `exp(K/4)`.  This is
still absorbed by the declared `A_star`. -/
lemma classifier_z_power_envelope {n : ℕ} (rho : ℝ) (P : Law n) (k : Fin n)
    (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (hn : 0 < n) :
    let z := P.cellMass k / lightScale n rho
    classificationProbability n rho P k * z ^ q *
        (1 + z) ^ (2 * degree n rho) ≤
      Real.exp (2 * degree n rho) * z := by
  let K := degree n rho
  let B := lightScale n rho
  let z := P.cellMass k / B
  have hK : 2 ≤ K := by simp [K, degree]
  have hB : 0 < B := lightScale_pos n rho hn
  have hz0 : 0 ≤ z := div_nonneg (P.cellMass_range k).1 hB.le
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  by_cases hz : z ≤ 1
  · have hzpow : z ^ q ≤ z := by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hq1
      rw [pow_add, pow_one]
      have := pow_le_one₀ hz0 hz (n := e)
      nlinarith
    have hbase : 1 + z ≤ 2 := by linarith
    have hpow : (1 + z) ^ (2 * K) ≤ (2 : ℝ) ^ (2 * K) :=
      pow_le_pow_left₀ (by linarith) hbase _
    have htwoexp : (2 : ℝ) ^ (2 * K) ≤ Real.exp (2 * K) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp 1
        norm_num at h
        exact h
      calc
        _ ≤ (Real.exp 1) ^ (2 * K) := pow_le_pow_left₀ (by norm_num) htwo _
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    calc
      _ ≤ z * (2 : ℝ) ^ (2 * K) := by
        have : classificationProbability n rho P k * z ^ q ≤ z := by
          calc
            _ ≤ 1 * z ^ q := mul_le_mul_of_nonneg_right ha1 (pow_nonneg hz0 _)
            _ ≤ z := by simpa using hzpow
        calc
          _ ≤ z * (1 + z) ^ (2 * K) :=
            mul_le_mul_of_nonneg_right this (pow_nonneg (by linarith) _)
          _ ≤ z * (2 : ℝ) ^ (2 * K) := mul_le_mul_of_nonneg_left hpow hz0
      _ ≤ z * Real.exp (2 * K) := by gcongr
      _ = _ := by ring
  · have hz' : 1 < z := lt_of_not_ge hz
    have hpB : B < P.cellMass k := by
      simpa [z] using (lt_div_iff₀ hB).mp hz'
    have halpha := heavy_classification_error_bound rho P k hn hpB
    have hmB := blockMean_mul_lightScale n rho hn
    have htail : classificationProbability n rho P k ≤
        Real.exp (-512 * (K : ℝ) * z) := by
      calc
        _ ≤ Real.exp (-blockMean n * P.cellMass k / 8) := halpha
        _ = _ := by
          congr 1
          dsimp [z, B, K]
          calc
            -blockMean n * P.cellMass k / 8 =
                -((blockMean n * lightScale n rho) * P.cellMass k /
                  lightScale n rho) / 8 := by
                    field_simp [(lightScale_pos n rho hn).ne']
            _ = _ := by rw [hmB]; ring
    calc
      _ ≤ Real.exp (-512 * (K : ℝ) * z) * z ^ q * (1 + z) ^ (2 * K) := by
        gcongr
      _ ≤ z := exp_tail_mul_power_le_self K q z hK hq3 hz'
      _ ≤ Real.exp (2 * K) * z := by
        have : 1 ≤ Real.exp (2 * K) := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          positivity
        nlinarith

/-- Classifier-weighted form of the per-cell light bound. -/
lemma classifier_mul_lightCellMomentBound_le {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n) :
    classificationProbability n rho P k * lightCellMomentBound M rho P k ≤
      24 * M ^ 2 *
        (∑ j ∈ Finset.range (degree n rho - 1), |gCoeff (degree n rho) j|) ^ 2 *
        Real.exp ((degree n rho : ℝ) / 4096) * Real.exp (2 * degree n rho) *
        (lightScale n rho ^ 2 + lightScale n rho / blockMean n) *
        (P.cellMass k / lightScale n rho) := by
  let K := degree n rho
  let B := lightScale n rho
  let m := blockMean n
  let z := P.cellMass k / B
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  let G : ℝ := ∑ j ∈ Finset.range (K - 1), |gCoeff K j|
  let E : ℝ := Real.exp ((K : ℝ) / 4096)
  let A : ℝ := Real.exp (2 * K)
  let R : ℝ := 4096 * (K : ℝ)
  have hB : 0 < B := lightScale_pos n rho hn
  have hm : 0 < m := blockMean_pos n hn
  have hR : R = m * B := (blockMean_mul_lightScale n rho hn).symm
  have hp0 := (P.cellMass_range k).1
  have he := P.propensity_range k
  have hx0 : 0 ≤ x0 := div_nonneg (mul_nonneg hp0 (sub_nonneg.mpr he.2)) hB.le
  have hx1 : 0 ≤ x1 := div_nonneg (mul_nonneg hp0 he.1) hB.le
  have hz0 : 0 ≤ z := div_nonneg hp0 hB.le
  have hx0z : x0 ≤ z := by
    apply (div_le_div_iff_of_pos_right hB).2
    dsimp [x0, z, armMass]
    nlinarith [mul_nonneg hp0 he.1]
  have hx1z : x1 ≤ z := by
    apply (div_le_div_iff_of_pos_right hB).2
    dsimp [x1, z, armMass]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr he.2)]
  have hpow0 : (1 + x0) ^ (2 * K) ≤ (1 + z) ^ (2 * K) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hpow1 : (1 + x1) ^ (2 * K) ≤ (1 + z) ^ (2 * K) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hGE : 0 ≤ G ^ 2 * E := mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hfirst :
      (R ^ 2 * x0 * (1 + x0) ^ (2 * K) * G ^ 2 * E) *
          (R ^ 2 * x1 ^ 2 + R * x1) ≤
        R ^ 2 * G ^ 2 * E * (1 + z) ^ (2 * K) *
          (R ^ 2 * z ^ 3 + R * z ^ 2) := by
    have hx1sq : x1 ^ 2 ≤ z ^ 2 := by nlinarith
    have hL : R ^ 2 * x1 ^ 2 + R * x1 ≤ R ^ 2 * z ^ 2 + R * z := by
      gcongr
    calc
      _ ≤ (R ^ 2 * z * (1 + z) ^ (2 * K) * G ^ 2 * E) *
          (R ^ 2 * z ^ 2 + R * z) := by gcongr
      _ = _ := by ring
  have hsecond :
      (R ^ 2 * x0 ^ 2 + R * x0) *
          (R ^ 2 * x1 * (1 + x1) ^ (2 * K) * G ^ 2 * E) ≤
        R ^ 2 * G ^ 2 * E * (1 + z) ^ (2 * K) *
          (R ^ 2 * z ^ 3 + R * z ^ 2) := by
    have hx0sq : x0 ^ 2 ≤ z ^ 2 := by nlinarith
    have hL : R ^ 2 * x0 ^ 2 + R * x0 ≤ R ^ 2 * z ^ 2 + R * z := by
      gcongr
    calc
      _ ≤ (R ^ 2 * z ^ 2 + R * z) *
          (R ^ 2 * z * (1 + z) ^ (2 * K) * G ^ 2 * E) := by gcongr
      _ = _ := by ring
  have hraw : lightCellMomentBound M rho P k ≤
      24 * M ^ 2 * G ^ 2 * E * (1 + z) ^ (2 * K) *
        (B ^ 2 * z ^ 3 + B / m * z ^ 2) := by
    dsimp only [lightCellMomentBound, K, B, m, x0, x1, G, E, R, z] at ⊢
    have hsum := add_le_add hfirst hsecond
    dsimp only [K, B, m, x0, x1, G, E, R, z] at hsum
    calc
      _ ≤ (12 * M ^ 2 / (lightScale n rho ^ 2 * blockMean n ^ 4)) *
          ((4096 * (degree n rho : ℝ)) ^ 2 *
              (∑ j ∈ Finset.range (degree n rho - 1), |gCoeff (degree n rho) j|) ^ 2 *
              Real.exp ((degree n rho : ℝ) / 4096) *
              (1 + P.cellMass k / lightScale n rho) ^ (2 * degree n rho) *
              ((4096 * (degree n rho : ℝ)) ^ 2 *
                  (P.cellMass k / lightScale n rho) ^ 3 +
                4096 * (degree n rho : ℝ) *
                  (P.cellMass k / lightScale n rho) ^ 2) * 2) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · positivity
      _ = _ := by
        rw [show 4096 * (degree n rho : ℝ) =
          blockMean n * lightScale n rho by
            exact (blockMean_mul_lightScale n rho hn).symm]
        field_simp [(blockMean_pos n hn).ne', (lightScale_pos n rho hn).ne']
        ring
  obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
  calc
    _ ≤ classificationProbability n rho P k *
        (24 * M ^ 2 * G ^ 2 * E * (1 + z) ^ (2 * K) *
          (B ^ 2 * z ^ 3 + B / m * z ^ 2)) :=
      mul_le_mul_of_nonneg_left hraw ha0
    _ = 24 * M ^ 2 * G ^ 2 * E *
        (B ^ 2 * (classificationProbability n rho P k * z ^ 3 * (1 + z) ^ (2 * K)) +
         B / m * (classificationProbability n rho P k * z ^ 2 * (1 + z) ^ (2 * K))) := by ring
    _ ≤ 24 * M ^ 2 * G ^ 2 * E *
        (B ^ 2 * (A * z) + B / m * (A * z)) := by
      have h3 := classifier_z_power_envelope rho P k 3 (by norm_num) (by norm_num) hn
      have h2 := classifier_z_power_envelope rho P k 2 (by norm_num) (by norm_num) hn
      dsimp only [z, K, A] at h3 h2
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left h3 (sq_nonneg B)
        · exact mul_le_mul_of_nonneg_left h2 (div_nonneg hB.le hm.le)
      · positivity
    _ = _ := by dsimp [K, B, m, z, G, E, A]; ring

/-- Global light second moment, after classifier weighting and summation over
the unknown cell masses.  This is equation (37) before the final numerical
coefficient-growth substitution. -/
lemma lightConditionalAudit_le_raw {n : ℕ} (M rho : ℝ) (P : Law n) (t : ℝ)
    (hn : 0 < n) (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    lightConditionalAudit n rho P t ≤
      24 * M ^ 2 *
        (∑ j ∈ Finset.range (degree n rho - 1), |gCoeff (degree n rho) j|) ^ 2 *
        Real.exp ((degree n rho : ℝ) / 4096) * Real.exp (2 * degree n rho) *
        (lightScale n rho + 1 / blockMean n) := by
  let C : ℝ := 24 * M ^ 2 *
    (∑ j ∈ Finset.range (degree n rho - 1), |gCoeff (degree n rho) j|) ^ 2 *
    Real.exp ((degree n rho : ℝ) / 4096) * Real.exp (2 * degree n rho) *
    (lightScale n rho ^ 2 + lightScale n rho / blockMean n)
  have hB : 0 < lightScale n rho := lightScale_pos n rho hn
  have hpoint (k : Fin n) :
      classificationProbability n rho P k *
        (∫ N0 : ℕ, ∫ N1 : ℕ,
          conditionalNumeratorSecond P k t N0 N1 *
            factorialCorrectionSquare n rho N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) ≤
        C * (P.cellMass k / lightScale n rho) := by
    by_cases hp : 0 < P.cellMass k
    · calc
        _ ≤ classificationProbability n rho P k * lightCellMomentBound M rho P k := by
          apply mul_le_mul_of_nonneg_left
          · exact lightAudit_cell_le M rho P k t hn hp hmean hvariance ht
          · exact (classificationProbability_mem_Icc rho P k).1
        _ ≤ C * (P.cellMass k / lightScale n rho) := by
          simpa only [C] using classifier_mul_lightCellMomentBound_le M rho P k hn
    · have hp0 : P.cellMass k = 0 := le_antisymm (le_of_not_gt hp) (P.cellMass_range k).1
      have harm (a : Bool) : armMass P a k = 0 := by simp [armMass, hp0]
      rw [harm false, harm true]
      simp only [mul_zero, Real.toNNReal_zero]
      simp [poissonMeasure_zero_eq_dirac, factorialCorrectionSquare, hp0]
  unfold lightConditionalAudit
  calc
    _ ≤ ∑ k : Fin n, C * (P.cellMass k / lightScale n rho) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = C * (1 / lightScale n rho) := by
      rw [← Finset.mul_sum, ← Finset.sum_div,
        DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
    _ = _ := by
      dsimp [C]
      field_simp [hB.ne']

/-- Equation (37), with an explicit universal numerical constant. -/
lemma lightConditionalAudit_le {n : ℕ} (M rho : ℝ) (P : Law n) (t : ℝ)
    (hn : 0 < n) (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    lightConditionalAudit n rho P t ≤
      1000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 3 / n := by
  let K := degree n rho
  let m := blockMean n
  have hK : 2 ≤ K := by simp [K, degree]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hm : 0 < m := blockMean_pos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hG := sum_abs_gCoeff_le K hK
  have hG0 : 0 ≤ ∑ j ∈ Finset.range (K - 1), |gCoeff K j| := by positivity
  have hpowG :
      (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 ≤
        ((K : ℝ) * 2 ^ (4 * K)) ^ 2 := by
    nlinarith [sq_nonneg ((∑ j ∈ Finset.range (K - 1), |gCoeff K j|) +
      (K : ℝ) * 2 ^ (4 * K))]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h
    exact h
  have htwoPow : (2 : ℝ) ^ (8 * K) ≤ Real.exp (8 * K) := by
    calc
      _ ≤ (Real.exp 1) ^ (8 * K) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hExp :
      (2 : ℝ) ^ (8 * K) * Real.exp ((K : ℝ) / 4096) *
          Real.exp (2 * K) ≤ auditConstant ^ K := by
    rw [auditConstant, ← Real.exp_nat_mul]
    rw [show (K : ℝ) * (2 ^ (20 : ℕ) : ℝ) =
      (2 ^ (20 : ℕ) : ℝ) * K by ring]
    calc
      _ ≤ Real.exp (8 * K) * Real.exp ((K : ℝ) / 4096) *
          Real.exp (2 * K) := by gcongr
      _ = Real.exp ((8 + 2 + (1 : ℝ) / 4096) * K) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((2 ^ (20 : ℕ) : ℝ) * K) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hscale : lightScale n rho + 1 / m ≤
      32776 * (K : ℝ) / n := by
    have hnm := sampleSize_div_blockMean_le_eight n hn
    rw [show lightScale n rho = 4096 * (K : ℝ) / m by rfl]
    have h1 : 1 ≤ (K : ℝ) := by exact_mod_cast (hK.trans' (by norm_num))
    calc
      4096 * (K : ℝ) / m + 1 / m = (4096 * (K : ℝ) + 1) / m := by ring
      _ ≤ 4097 * (K : ℝ) / m := by
        apply (div_le_div_iff_of_pos_right hm).2
        nlinarith
      _ ≤ 32776 * (K : ℝ) / n := by
        calc
          _ = (4097 * (K : ℝ) / n) * ((n : ℝ) / m) := by
            field_simp [hm.ne', hnR.ne']
          _ ≤ (4097 * (K : ℝ) / n) * 8 :=
            mul_le_mul_of_nonneg_left hnm (by positivity)
          _ = _ := by ring
  have hscale0 : 0 ≤ lightScale n rho + 1 / m := by
    exact add_nonneg (lightScale_pos n rho hn).le (div_nonneg (by norm_num) hm.le)
  calc
    _ ≤ 24 * M ^ 2 *
        (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
        Real.exp ((K : ℝ) / 4096) * Real.exp (2 * K) *
        (lightScale n rho + 1 / m) := by
      simpa only [K, m] using lightConditionalAudit_le_raw M rho P t hn hmean hvariance ht
    _ ≤ 24 * M ^ 2 * (((K : ℝ) * 2 ^ (4 * K)) ^ 2) *
        Real.exp ((K : ℝ) / 4096) * Real.exp (2 * K) *
        (32776 * (K : ℝ) / n) := by
      gcongr
    _ ≤ 1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 3 / n := by
      have hconst : (24 : ℝ) * 32776 ≤ 1000000 := by norm_num
      rw [show (((K : ℝ) * 2 ^ (4 * K)) ^ 2) =
        (K : ℝ) ^ 2 * 2 ^ (8 * K) by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega]
      calc
        _ = (24 * 32776) * M ^ 2 * (K : ℝ) ^ 3 / n *
            ((2 : ℝ) ^ (8 * K) * Real.exp ((K : ℝ) / 4096) *
              Real.exp (2 * K)) := by ring
        _ ≤ 1000000 * M ^ 2 * (K : ℝ) ^ 3 / n * auditConstant ^ K := by
          gcongr
        _ = _ := by ring

/-- Concrete equation (44) budget assembled from the light second moment,
heavy conditional variance, and classifier mixing terms. -/
lemma upperVarianceAuditBudget_le {n : ℕ} (M rho : ℝ) (P : Law n) (t : ℝ)
    (hn : 0 < n) (hoverlap : FixedOverlap P) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    lightConditionalAudit n rho P t + 115 * M ^ 2 / blockMean n +
        8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k)) ≤
      2000000 * M ^ 2 * auditConstant ^ degree n rho *
        (degree n rho : ℝ) ^ 4 / n := by
  let K := degree n rho
  let m := blockMean n
  have hK : 2 ≤ K := by simp [K, degree]
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hm : 0 < m := blockMean_pos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 1 ≤ auditConstant ^ K := by
    apply one_le_pow₀
    rw [auditConstant, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  have hK3K4 : (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((K : ℝ) ^ 2), sq_nonneg ((K : ℝ) ^ 2 - K)]
  have hlight := lightConditionalAudit_le M rho P t hn hmean hvariance ht
  have hcross := sum_cellMass_sq_classifier_mixing_le rho P hn
  have hnm := sampleSize_div_blockMean_le_eight n hn
  have hrest : 115 * M ^ 2 / m +
      8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
        classificationProbability n rho P k *
          (1 - classificationProbability n rho P k)) ≤
      1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 4 / n := by
    have hcross' : 8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
        classificationProbability n rho P k *
          (1 - classificationProbability n rho P k)) ≤
        8 * M ^ 2 * (4104 * (K : ℝ) / m) := by
      gcongr
    calc
      _ ≤ 115 * M ^ 2 / m + 8 * M ^ 2 * (4104 * (K : ℝ) / m) :=
        add_le_add le_rfl hcross'
      _ = M ^ 2 * (115 + 32832 * (K : ℝ)) / m := by ring
      _ = (M ^ 2 * (115 + 32832 * (K : ℝ)) / n) * ((n : ℝ) / m) := by
        field_simp [hm.ne', hnR.ne']
      _ ≤ (M ^ 2 * (115 + 32832 * (K : ℝ)) / n) * 8 := by
        apply mul_le_mul_of_nonneg_left hnm
        positivity
      _ ≤ 1000000 * M ^ 2 * 1 * (K : ℝ) ^ 4 / n := by
        rw [show M ^ 2 * (115 + 32832 * (K : ℝ)) / n * 8 =
          (8 * M ^ 2 * (115 + 32832 * (K : ℝ))) / n by ring]
        apply (div_le_div_iff_of_pos_right hnR).2
        have hpoly : 8 * (115 + 32832 * (K : ℝ)) ≤
            1000000 * (K : ℝ) ^ 4 := by
          nlinarith [sq_nonneg ((K : ℝ) ^ 2),
            sq_nonneg ((K : ℝ) ^ 2 - K)]
        convert mul_le_mul_of_nonneg_left hpoly (sq_nonneg M) using 1 <;> ring
      _ ≤ 1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 4 / n := by
        gcongr
  calc
    _ = lightConditionalAudit n rho P t +
        (115 * M ^ 2 / m + 8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k))) := by
      dsimp only [m]
      ring
    _ ≤ 1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 3 / n +
        (115 * M ^ 2 / m + 8 * M ^ 2 * (∑ k : Fin n, P.cellMass k ^ 2 *
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k))) := by
      exact add_le_add (by simpa only [K] using hlight) le_rfl
    _ ≤ 1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 4 / n +
        1000000 * M ^ 2 * auditConstant ^ K * (K : ℝ) ^ 4 / n := by
      apply add_le_add
      · gcongr
      · exact hrest
    _ = _ := by ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

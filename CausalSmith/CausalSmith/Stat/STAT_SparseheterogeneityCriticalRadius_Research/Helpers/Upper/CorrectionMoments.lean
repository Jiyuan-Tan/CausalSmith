module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FixedCountMoments
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightVariance
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ProductPoissonCentered

/-! Moment transport for the light and heavy cell corrections. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- The squared light correction under the two independent arm outcome
samples is exactly the light count audit integrand. -/
lemma lightCorrection_second_moment_cell {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      (Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          lightFactorialCoefficient n rho p.1.count p.2.count) ^ 2
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hinner (N0 : ℕ) := lightAuditIntegrand_integrable_inner M rho P k t rate1
    N0 hn hp hmean hvariance ht
  have houter := lightAuditIntegrand_integrable_outer M rho P k t rate0 rate1
    hn hp hmean hvariance ht
  have h := poisson_centeredNumerator_second_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1 (factorialCorrectionSquare n rho)
    (factorialCorrectionSquare_nonneg n rho) hinner houter
  simpa only [mul_pow,
    factorialCorrectionSquare_eq_lightFactorialCoefficient_sq] using h

lemma heavyConditionalSecond_decomposition {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) (N0 N1 : ℕ) (hn : 0 < n) :
    conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2 =
      heavyOutcomeNoiseSecond P k N0 N1 +
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 /
          blockMean n ^ 2 * guardedTotalCount N0 N1 ^ 2 := by
  rw [conditionalNumeratorSecond_decompose_noise]
  rw [heavySignalCoefficient_eq_guarded t
    (DiscreteAteHeterogeneityFrontier.cellEffect P k) N0 N1 hn]

lemma heavyAuditIntegrand_integrable_inner {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (b : ℝ≥0) (N0 : ℕ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun N1 : ℕ => conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2) (poissonMeasure b) := by
  rw [show (fun N1 : ℕ => conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2) = fun N1 =>
        heavyOutcomeNoiseSecond P k N0 N1 +
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 /
            blockMean n ^ 2 * guardedTotalCount N0 N1 ^ 2 by
    funext N1
    exact heavyConditionalSecond_decomposition P k t N0 N1 hn]
  exact (heavyOutcomeNoiseSecond_integrable_inner M P k b N0 hn hp hvariance).add
    (by
      have h := (guardedTotalCount_center_sq_integrable_inner b N0 0).const_mul
        ((DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 /
          blockMean n ^ 2)
      simpa using h)

lemma heavyAuditIntegrand_integrable_outer {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (a b : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2
      ∂poissonMeasure b) (poissonMeasure a) := by
  let c := (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 /
    blockMean n ^ 2
  have hfun : (fun N0 : ℕ => ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2
        ∂poissonMeasure b) = fun N0 =>
      (∫ N1 : ℕ, heavyOutcomeNoiseSecond P k N0 N1 ∂poissonMeasure b) +
        ∫ N1 : ℕ, c * guardedTotalCount N0 N1 ^ 2 ∂poissonMeasure b := by
    funext N0
    rw [show (fun N1 : ℕ => conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2) = fun N1 =>
          heavyOutcomeNoiseSecond P k N0 N1 +
            c * guardedTotalCount N0 N1 ^ 2 by
      funext N1
      exact heavyConditionalSecond_decomposition P k t N0 N1 hn]
    rw [integral_add
      (heavyOutcomeNoiseSecond_integrable_inner M P k b N0 hn hp hvariance)
      (by
        have h := (guardedTotalCount_center_sq_integrable_inner b N0 0).const_mul c
        simpa only [sub_zero] using h)]
  rw [hfun]
  exact (heavyOutcomeNoiseSecond_integrable_outer M P k a b hn hp hvariance).add
    (by
      have h := (guardedTotalCount_center_sq_integrable_outer a b 0).const_mul c
      simpa only [sub_zero, integral_const_mul] using h)

/-- The squared heavy correction under the two independent arm outcome
samples is exactly the heavy count audit integrand. -/
lemma heavyCorrection_second_moment_cell {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      (Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          heavyCoefficient n p.1.count p.2.count) ^ 2
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hinner (N0 : ℕ) := heavyAuditIntegrand_integrable_inner M P k t rate1
    N0 hn hp hvariance
  have houter := heavyAuditIntegrand_integrable_outer M P k t rate0 rate1
    hn hp hvariance
  have h := poisson_centeredNumerator_second_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1 (fun N0 N1 => heavyCoefficient n N0 N1 ^ 2)
    (fun _ _ => sq_nonneg _) hinner houter
  simpa only [mul_pow] using h

lemma crossAuditIntegrand_integrable_inner {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (b : ℝ≥0) (N0 : ℕ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    Integrable (fun N1 : ℕ => conditionalNumeratorSecond P k t N0 N1 *
      (lightFactorialCoefficient n rho N0 N1 -
        heavyCoefficient n N0 N1) ^ 2) (poissonMeasure b) := by
  have hL := lightAuditIntegrand_integrable_inner M rho P k t b N0
    hn hp hmean hvariance ht
  have hH := heavyAuditIntegrand_integrable_inner M P k t b N0 hn hp hvariance
  have henv := (hL.const_mul 2).add (hH.const_mul 2)
  apply henv.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N1
  have hc := conditionalNumeratorSecond_nonneg P k t N0 N1
  have hLsq := factorialCorrectionSquare_eq_lightFactorialCoefficient_sq
    n rho N0 N1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (sq_nonneg _))]
  change conditionalNumeratorSecond P k t N0 N1 *
      (lightFactorialCoefficient n rho N0 N1 - heavyCoefficient n N0 N1) ^ 2 ≤
    2 * (conditionalNumeratorSecond P k t N0 N1 *
      factorialCorrectionSquare n rho N0 N1) +
    2 * (conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2)
  rw [hLsq]
  nlinarith [sq_nonneg (lightFactorialCoefficient n rho N0 N1 +
    heavyCoefficient n N0 N1)]

lemma crossAuditIntegrand_integrable_outer {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (a b : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 *
        (lightFactorialCoefficient n rho N0 N1 -
          heavyCoefficient n N0 N1) ^ 2 ∂poissonMeasure b)
      (poissonMeasure a) := by
  have hL := lightAuditIntegrand_integrable_outer M rho P k t a b
    hn hp hmean hvariance ht
  have hH := heavyAuditIntegrand_integrable_outer M P k t a b hn hp hvariance
  apply ((hL.const_mul 2).add (hH.const_mul 2)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N0
  have hcross := crossAuditIntegrand_integrable_inner M rho P k t b N0
    hn hp hmean hvariance ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun N1 =>
    mul_nonneg (conditionalNumeratorSecond_nonneg P k t N0 N1) (sq_nonneg _))]
  change (∫ N1 : ℕ, conditionalNumeratorSecond P k t N0 N1 *
      (lightFactorialCoefficient n rho N0 N1 - heavyCoefficient n N0 N1) ^ 2
      ∂poissonMeasure b) ≤
    2 * (∫ N1 : ℕ, conditionalNumeratorSecond P k t N0 N1 *
      factorialCorrectionSquare n rho N0 N1 ∂poissonMeasure b) +
    2 * (∫ N1 : ℕ, conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2 ∂poissonMeasure b)
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add
      ((lightAuditIntegrand_integrable_inner M rho P k t b N0
        hn hp hmean hvariance ht).const_mul 2)
      ((heavyAuditIntegrand_integrable_inner M P k t b N0 hn hp hvariance).const_mul 2)]
  apply integral_mono hcross
    (((lightAuditIntegrand_integrable_inner M rho P k t b N0
      hn hp hmean hvariance ht).const_mul 2).add
      ((heavyAuditIntegrand_integrable_inner M P k t b N0 hn hp hvariance).const_mul 2))
  intro N1
  have hc := conditionalNumeratorSecond_nonneg P k t N0 N1
  change conditionalNumeratorSecond P k t N0 N1 *
      (lightFactorialCoefficient n rho N0 N1 - heavyCoefficient n N0 N1) ^ 2 ≤
    2 * (conditionalNumeratorSecond P k t N0 N1 *
      factorialCorrectionSquare n rho N0 N1) +
    2 * (conditionalNumeratorSecond P k t N0 N1 *
      heavyCoefficient n N0 N1 ^ 2)
  rw [factorialCorrectionSquare_eq_lightFactorialCoefficient_sq]
  nlinarith [sq_nonneg (lightFactorialCoefficient n rho N0 N1 +
    heavyCoefficient n N0 N1)]

/-- The squared light-minus-heavy correction has exactly the cross audit
second moment. -/
-- keep: exact cellwise cross-correction second moment for independent auditing
lemma crossCorrection_second_moment_cell {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      (Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          (lightFactorialCoefficient n rho p.1.count p.2.count -
            heavyCoefficient n p.1.count p.2.count)) ^ 2
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 *
        (lightFactorialCoefficient n rho N0 N1 -
          heavyCoefficient n N0 N1) ^ 2
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hinner (N0 : ℕ) := crossAuditIntegrand_integrable_inner M rho P k t rate1
    N0 hn hp hmean hvariance ht
  have houter := crossAuditIntegrand_integrable_outer M rho P k t rate0 rate1
    hn hp hmean hvariance ht
  have h := poisson_centeredNumerator_second_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1
      (fun N0 N1 => (lightFactorialCoefficient n rho N0 N1 -
        heavyCoefficient n N0 N1) ^ 2)
    (fun _ _ => sq_nonneg _) hinner houter
  simpa only [mul_pow] using h

/-- Exact first moment of the light correction on one positive-mass cell. -/
lemma lightCorrection_first_moment_cell {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          lightFactorialCoefficient n rho p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          lightFactorialCoefficient n rho N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hsqInner (N0 : ℕ) : Integrable (fun N1 =>
      conditionalNumeratorSecond P k t N0 N1 *
        lightFactorialCoefficient n rho N0 N1 ^ 2) (poissonMeasure rate1) := by
    simpa only [factorialCorrectionSquare_eq_lightFactorialCoefficient_sq] using
      lightAuditIntegrand_integrable_inner M rho P k t rate1 N0
        hn hp hmean hvariance ht
  have hsqOuter : Integrable (fun N0 => ∫ N1,
      conditionalNumeratorSecond P k t N0 N1 *
        lightFactorialCoefficient n rho N0 N1 ^ 2 ∂poissonMeasure rate1)
      (poissonMeasure rate0) := by
    simpa only [factorialCorrectionSquare_eq_lightFactorialCoefficient_sq] using
      lightAuditIntegrand_integrable_outer M rho P k t rate0 rate1
        hn hp hmean hvariance ht
  obtain ⟨hinner, houter⟩ := countMean_integrable_of_second P k t rate0 rate1
    (lightFactorialCoefficient n rho) hsqInner hsqOuter
  exact poisson_centeredNumerator_first_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1 (lightFactorialCoefficient n rho)
      hsqInner hsqOuter hinner houter

/-- Exact first moment of the heavy correction on one positive-mass cell. -/
lemma heavyCorrection_first_moment_cell {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          heavyCoefficient n p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          heavyCoefficient n N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hsqInner (N0 : ℕ) := heavyAuditIntegrand_integrable_inner M P k t rate1
    N0 hn hp hvariance
  have hsqOuter := heavyAuditIntegrand_integrable_outer M P k t rate0 rate1
    hn hp hvariance
  obtain ⟨hinner, houter⟩ := countMean_integrable_of_second P k t rate0 rate1
    (heavyCoefficient n) hsqInner hsqOuter
  exact poisson_centeredNumerator_first_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1 (heavyCoefficient n)
      hsqInner hsqOuter hinner houter

-- keep: exact cellwise cross-correction first moment paired with its second-moment theorem
lemma crossCorrection_first_moment_cell {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          (lightFactorialCoefficient n rho p.1.count p.2.count -
            heavyCoefficient n p.1.count p.2.count)
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
          (lightFactorialCoefficient n rho N0 N1 - heavyCoefficient n N0 N1)
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  have hsqInner (N0 : ℕ) := crossAuditIntegrand_integrable_inner M rho P k t
    rate1 N0 hn hp hmean hvariance ht
  have hsqOuter := crossAuditIntegrand_integrable_outer M rho P k t rate0 rate1
    hn hp hmean hvariance ht
  obtain ⟨hinner, houter⟩ := countMean_integrable_of_second P k t rate0 rate1
    (fun N0 N1 => lightFactorialCoefficient n rho N0 N1 -
      heavyCoefficient n N0 N1) hsqInner hsqOuter
  exact poisson_centeredNumerator_first_weighted_of_count_integrable
    P k t hp hvariance rate0 rate1
      (fun N0 N1 => lightFactorialCoefficient n rho N0 N1 -
        heavyCoefficient n N0 N1)
      hsqInner hsqOuter hinner houter

lemma lightWeightedCount_eq_FK {n : ℕ} (rho : ℝ) (N0 N1 : ℕ) (hn : 0 < n) :
    (N0 : ℝ) * (N1 : ℝ) * lightFactorialCoefficient n rho N0 N1 =
      (N0 : ℝ) * (N1 : ℝ) *
        (FK (degree n rho) (blockMean n * lightScale n rho) N0 +
          FK (degree n rho) (blockMean n * lightScale n rho) N1) /
            (lightScale n rho * blockMean n ^ 2) := by
  by_cases h0 : N0 = 0
  · subst N0; simp
  by_cases h1 : N1 = 0
  · subst N1; simp
  rw [lightFactorialCoefficient_eq_FK rho N0 N1 hn h0 h1]
  ring

/-- Product-Poisson expectation of the count-weighted light coefficient. -/
lemma lightWeightedCount_integral {n : ℕ} (rho : ℝ) (rate0 rate1 : ℝ≥0)
    (hn : 0 < n) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
      (N0 : ℝ) * (N1 : ℝ) * lightFactorialCoefficient n rho N0 N1
      ∂poissonMeasure rate1 ∂poissonMeasure rate0) =
      ((rate0 : ℝ) * (rate1 : ℝ) /
        (lightScale n rho * blockMean n ^ 2)) *
          (GK (degree n rho)
              ((rate0 : ℝ) / (blockMean n * lightScale n rho)) +
            GK (degree n rho)
              ((rate1 : ℝ) / (blockMean n * lightScale n rho))) := by
  let K := degree n rho
  let R := blockMean n * lightScale n rho
  let D := lightScale n rho * blockMean n ^ 2
  have hR : R ≠ 0 := by
    dsimp only [R]
    exact mul_ne_zero (blockMean_pos n hn).ne' (lightScale_pos n rho hn).ne'
  have hinner (N0 : ℕ) :
      (∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
        lightFactorialCoefficient n rho N0 N1 ∂poissonMeasure rate1) =
      ((N0 : ℝ) * FK K R N0 * (rate1 : ℝ) +
        (N0 : ℝ) * ((rate1 : ℝ) * GK K ((rate1 : ℝ) / R))) / D := by
    rw [show (fun N1 : ℕ => (N0 : ℝ) * (N1 : ℝ) *
        lightFactorialCoefficient n rho N0 N1) = fun N1 : ℕ =>
      (((N0 : ℝ) * FK K R N0) * (N1 : ℝ) +
        (N0 : ℝ) * ((N1 : ℝ) * FK K R N1)) / D by
      funext N1
      rw [lightWeightedCount_eq_FK rho N0 N1 hn]
      dsimp only [K, R, D]
      ring]
    rw [integral_div, integral_add
      ((poisson_natCast_memLp_two rate1).integrable (by norm_num) |>.const_mul _)
      ((poisson_mul_FK_integrable K R rate1).const_mul _),
      integral_const_mul, integral_const_mul, poisson_count_first_moment,
      poisson_mul_FK_mean K R rate1 hR]
  simp_rw [hinner]
  rw [show (fun N0 : ℕ =>
      ((N0 : ℝ) * FK K R N0 * (rate1 : ℝ) +
        (N0 : ℝ) * ((rate1 : ℝ) * GK K ((rate1 : ℝ) / R))) / D) =
      fun N0 : ℕ => ((rate1 : ℝ) / D) * ((N0 : ℝ) * FK K R N0) +
        (((rate1 : ℝ) * GK K ((rate1 : ℝ) / R)) / D) * (N0 : ℝ) by
    funext N0; ring]
  rw [integral_add
    ((poisson_mul_FK_integrable K R rate0).const_mul _)
    (((poisson_natCast_memLp_two rate0).integrable (by norm_num)).const_mul _),
    integral_const_mul, integral_const_mul,
    poisson_mul_FK_mean K R rate0 hR, poisson_count_first_moment]
  dsimp only [K, R, D]
  ring

lemma lightWeightedCount_integral_armMass {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
      (N0 : ℝ) * (N1 : ℝ) * lightFactorialCoefficient n rho N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) =
      lightAuditWeight n rho P k := by
  have hm : 0 < blockMean n := blockMean_pos n hn
  have hB : 0 < lightScale n rho := lightScale_pos n rho hn
  have ha0 : 0 ≤ armMass P false k := by
    dsimp only [armMass]
    exact mul_nonneg (P.cellMass_range k).1 (sub_nonneg.mpr (P.propensity_range k).2)
  have ha1 : 0 ≤ armMass P true k := by
    dsimp only [armMass]
    exact mul_nonneg (P.cellMass_range k).1 (P.propensity_range k).1
  rw [lightWeightedCount_integral rho _ _ hn,
    Real.coe_toNNReal _ (mul_nonneg hm.le ha0),
    Real.coe_toNNReal _ (mul_nonneg hm.le ha1)]
  unfold lightAuditWeight
  dsimp only
  field_simp [hm.ne', hB.ne']

lemma heavyWeightedCount_integral_armMass {n : ℕ} (P : Law n) (k : Fin n)
    (hn : 0 < n) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
      (N0 : ℝ) * (N1 : ℝ) * heavyCoefficient n N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))) =
      heavyAuditWeight n P k := by
  let a := Real.toNNReal (blockMean n * armMass P false k)
  let b := Real.toNNReal (blockMean n * armMass P true k)
  have hm : 0 < blockMean n := blockMean_pos n hn
  have ha0 : 0 ≤ armMass P false k := by
    dsimp only [armMass]
    exact mul_nonneg (P.cellMass_range k).1 (sub_nonneg.mpr (P.propensity_range k).2)
  have ha1 : 0 ≤ armMass P true k := by
    dsimp only [armMass]
    exact mul_nonneg (P.cellMass_range k).1 (P.propensity_range k).1
  simp_rw [heavyWeightedCount_eq_guarded _ _ hn]
  simp_rw [integral_div]
  rw [guardedTotalCount_integral a b]
  dsimp only [a, b]
  rw [Real.coe_toNNReal _ (mul_nonneg hm.le ha0),
    Real.coe_toNNReal _ (mul_nonneg hm.le ha1)]
  unfold heavyAuditWeight armMass
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [hm.ne']
  ring

lemma lightCorrection_first_moment_eq_weight {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          lightFactorialCoefficient n rho p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k)
          (Real.toNNReal (blockMean n * armMass P false k))).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k)
          (Real.toNNReal (blockMean n * armMass P true k))))) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        lightAuditWeight n rho P k := by
  rw [lightCorrection_first_moment_cell M rho P k t _ _ hn hp
    hmean hvariance ht]
  rw [show (fun N0 : ℕ => ∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        lightFactorialCoefficient n rho N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))) =
      fun N0 : ℕ => (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        (∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
          lightFactorialCoefficient n rho N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))) by
    funext N0
    rw [← integral_const_mul]
    congr 1
    funext N1
    ring]
  rw [integral_const_mul, lightWeightedCount_integral_armMass rho P k hn]

lemma heavyCorrection_first_moment_eq_weight {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hvariance : VarianceEnvelope M P) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 *
          heavyCoefficient n p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k)
          (Real.toNNReal (blockMean n * armMass P false k))).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k)
          (Real.toNNReal (blockMean n * armMass P true k))))) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        heavyAuditWeight n P k := by
  rw [heavyCorrection_first_moment_cell M P k t _ _ hn hp hvariance]
  rw [show (fun N0 : ℕ => ∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        heavyCoefficient n N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))) =
      fun N0 : ℕ => (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) *
        (∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) * heavyCoefficient n N0 N1
          ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))) by
    funext N0
    rw [← integral_const_mul]
    congr 1
    funext N1
    ring]
  rw [integral_const_mul, heavyWeightedCount_integral_armMass P k hn]

/-- The ideal independent outcome-sample law for one cell. -/
noncomputable def cellOutcomePoissonLaw {n : ℕ} (P : Law n) (k : Fin n) :
    Measure (FiniteSample ℝ × FiniteSample ℝ) :=
  (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
      (P.outcome_isProbability false k)
      (Real.toNNReal (blockMean n * armMass P false k))).prod
    (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
      (P.outcome_isProbability true k)
      (Real.toNNReal (blockMean n * armMass P true k)))

noncomputable def idealLightCorrection {n : ℕ} (P : Law n) (k : Fin n)
    (t rho : ℝ) (p : FiniteSample ℝ × FiniteSample ℝ) : ℝ :=
  Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
    (centeredNumeratorKernel P k t) p.1 p.2 *
      lightFactorialCoefficient n rho p.1.count p.2.count

noncomputable def idealHeavyCorrection {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) (p : FiniteSample ℝ × FiniteSample ℝ) : ℝ :=
  Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
    (centeredNumeratorKernel P k t) p.1 p.2 *
      heavyCoefficient n p.1.count p.2.count

lemma measurable_idealLightCorrection {n : ℕ} (P : Law n) (k : Fin n)
    (t rho : ℝ) : Measurable (idealLightCorrection P k t rho) := by
  unfold idealLightCorrection
  apply Measurable.mul
  · exact Causalean.Mathlib.Probability.Poisson.PairSecondMoment.measurable_pairSum
      (centeredNumeratorKernel P k t)
      ((measurable_snd.sub measurable_fst).sub measurable_const)
  · exact (measurable_of_countable (Function.uncurry
      (lightFactorialCoefficient n rho))).comp
      ((measurable_finiteSample_count.comp measurable_fst).prodMk
        (measurable_finiteSample_count.comp measurable_snd))

lemma measurable_idealHeavyCorrection {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) : Measurable (idealHeavyCorrection P k t) := by
  unfold idealHeavyCorrection
  apply Measurable.mul
  · exact Causalean.Mathlib.Probability.Poisson.PairSecondMoment.measurable_pairSum
      (centeredNumeratorKernel P k t)
      ((measurable_snd.sub measurable_fst).sub measurable_const)
  · exact (measurable_of_countable (Function.uncurry
      (heavyCoefficient n))).comp
      ((measurable_finiteSample_count.comp measurable_fst).prodMk
        (measurable_finiteSample_count.comp measurable_snd))

/-- Square integrability of the ideal light correction. -/
lemma idealLightCorrection_sq_integrable {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    Integrable (fun p => idealLightCorrection P k t rho p ^ 2)
      (cellOutcomePoissonLaw P k) := by
  have hinner (N0 : ℕ) := lightAuditIntegrand_integrable_inner M rho P k t
    (Real.toNNReal (blockMean n * armMass P true k)) N0
    hn hp hmean hvariance ht
  have houter := lightAuditIntegrand_integrable_outer M rho P k t
    (Real.toNNReal (blockMean n * armMass P false k))
    (Real.toNNReal (blockMean n * armMass P true k))
    hn hp hmean hvariance ht
  have h := integrable_poisson_centeredNumerator_second_weighted P k t hp
    hvariance (Real.toNNReal (blockMean n * armMass P false k))
    (Real.toNNReal (blockMean n * armMass P true k))
    (factorialCorrectionSquare n rho) (factorialCorrectionSquare_nonneg n rho)
    hinner houter
  simpa only [idealLightCorrection, cellOutcomePoissonLaw, mul_pow,
    factorialCorrectionSquare_eq_lightFactorialCoefficient_sq] using h

/-- Square integrability of the ideal heavy correction. -/
lemma idealHeavyCorrection_sq_integrable {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hvariance : VarianceEnvelope M P) :
    Integrable (fun p => idealHeavyCorrection P k t p ^ 2)
      (cellOutcomePoissonLaw P k) := by
  have hinner (N0 : ℕ) := heavyAuditIntegrand_integrable_inner M P k t
    (Real.toNNReal (blockMean n * armMass P true k)) N0 hn hp hvariance
  have houter := heavyAuditIntegrand_integrable_outer M P k t
    (Real.toNNReal (blockMean n * armMass P false k))
    (Real.toNNReal (blockMean n * armMass P true k)) hn hp hvariance
  have h := integrable_poisson_centeredNumerator_second_weighted P k t hp
    hvariance (Real.toNNReal (blockMean n * armMass P false k))
    (Real.toNNReal (blockMean n * armMass P true k))
    (fun N0 N1 => heavyCoefficient n N0 N1 ^ 2)
    (fun _ _ => sq_nonneg _) hinner houter
  simpa only [idealHeavyCorrection, cellOutcomePoissonLaw, mul_pow] using h

lemma idealLightCorrection_integrable {n : ℕ} (M rho : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    Integrable (idealLightCorrection P k t rho) (cellOutcomePoissonLaw P k) := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  have hsq := idealLightCorrection_sq_integrable M rho P k t hn hp hmean
    hvariance ht
  have hmajor := hsq.add (integrable_const (1 : ℝ))
  apply hmajor.mono' (measurable_idealLightCorrection P k t rho).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  change |idealLightCorrection P k t rho p| ≤
    idealLightCorrection P k t rho p ^ 2 + 1
  have hs := sq_nonneg (|idealLightCorrection P k t rho p| - 1)
  have habs := sq_abs (idealLightCorrection P k t rho p)
  nlinarith

lemma idealHeavyCorrection_integrable {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hvariance : VarianceEnvelope M P) :
    Integrable (idealHeavyCorrection P k t) (cellOutcomePoissonLaw P k) := by
  letI : IsProbabilityMeasure (cellOutcomePoissonLaw P k) := by
    unfold cellOutcomePoissonLaw
    infer_instance
  have hsq := idealHeavyCorrection_sq_integrable M P k t hn hp hvariance
  have hmajor := hsq.add (integrable_const (1 : ℝ))
  apply hmajor.mono' (measurable_idealHeavyCorrection P k t).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  change |idealHeavyCorrection P k t p| ≤
    idealHeavyCorrection P k t p ^ 2 + 1
  have hs := sq_nonneg (|idealHeavyCorrection P k t p| - 1)
  have habs := sq_abs (idealHeavyCorrection P k t p)
  nlinarith

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

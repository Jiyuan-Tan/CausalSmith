module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyMissingSum
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyOutcomeNoise
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyMissingMoment
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightFactorialSquare
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ProductPoissonCentered
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ClassifierTail
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.Count

/-! The factorial second-moment and classification-variance proof chain. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

noncomputable def heavyCenteredEffectSecond {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) (N0 N1 : ℕ) : ℝ :=
  ((guardedTotalCount N0 N1 / blockMean n - P.cellMass k) *
    (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)) ^ 2

noncomputable def heavyCellConditionalVariance {n : ℕ} (P : Law n)
    (k : Fin n) (t : ℝ) : ℝ :=
  (∫ N0 : ℕ, ∫ N1 : ℕ, heavyOutcomeNoiseSecond P k N0 N1
      ∂poissonMeasure
        (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure
        (Real.toNNReal (blockMean n * armMass P false k))) +
  (∫ N0 : ℕ, ∫ N1 : ℕ, heavyCenteredEffectSecond P k t N0 N1
      ∂poissonMeasure
        (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure
        (Real.toNNReal (blockMean n * armMass P false k)))

lemma cellEffect_sub_pilot_abs_le {n : ℕ} {M : ℝ} (P : Law n)
    (k : Fin n) (t : ℝ) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (ht : AdmissiblePilotValue M t) :
    |DiscreteAteHeterogeneityFrontier.cellEffect P k - t| ≤ 2 * M := by
  have hcell : |DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤ M := by
    unfold DiscreteAteHeterogeneityFrontier.cellEffect
    calc
      _ ≤ |P.outcomeMean true k| + |P.outcomeMean false k| := abs_sub _ _
      _ ≤ M / 2 + M / 2 := add_le_add (hmean true k hp) (hmean false k hp)
      _ = M := by ring
  have htAbs : |t| ≤ M := by
    rw [abs_le]
    exact ht
  calc
    _ ≤ |DiscreteAteHeterogeneityFrontier.cellEffect P k| + |t| := abs_sub _ _
    _ ≤ M + M := add_le_add hcell htAbs
    _ = 2 * M := by ring

lemma heavyCenteredEffectSecond_integral_le {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hoverlap : FixedOverlap P) (hmean : MeanEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, heavyCenteredEffectSecond P k t N0 N1
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P false k))) ≤
      8 * M ^ 2 * (P.cellMass k / blockMean n +
        2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
          Real.exp (-blockMean n * P.cellMass k / 4)) := by
  let a : ℝ≥0 := Real.toNNReal (blockMean n * armMass P false k)
  let b : ℝ≥0 := Real.toNNReal (blockMean n * armMass P true k)
  let m : ℝ := blockMean n
  let p : ℝ := P.cellMass k
  let d : ℝ := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hm : 0 < m := blockMean_pos n hn
  have hp0 : 0 ≤ p := P.cellMass_range k |>.1
  have hpi := P.propensity_range k
  have ha0 : 0 ≤ m * armMass P false k := by
    simp only [armMass, Bool.false_eq_true, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 (sub_nonneg.mpr hpi.2))
  have hb0 : 0 ≤ m * armMass P true k := by
    simp only [armMass, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 hpi.1)
  have ha : (a : ℝ) = m * armMass P false k := Real.coe_toNNReal _ ha0
  have hb : (b : ℝ) = m * armMass P true k := Real.coe_toNNReal _ hb0
  have hab : (a : ℝ) + (b : ℝ) = m * p := by
    rw [ha, hb]
    simp only [m, p, armMass, Bool.false_eq_true, ↓reduceIte]
    ring
  have hdAbs : |d| ≤ 2 * M :=
    cellEffect_sub_pilot_abs_le P k t hp hmean ht
  have hM0 : 0 ≤ M := by
    have hd0 : 0 ≤ |d| := abs_nonneg d
    linarith
  have hdSq : d ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith [abs_nonneg d, sq_abs d]
  have hcount := guardedTotalCount_center_sq_integral_le a b
  have hmiss := missingCountSquareEnvelope_arm_scaled_le P k hn hoverlap
  have hmiss' : 1 / m ^ 2 *
      (∫ N0 : ℕ, ∫ N1 : ℕ, missingCountSquareEnvelope N0 N1
        ∂poissonMeasure b ∂poissonMeasure a) ≤
      2 * (p ^ 2 + p / m) * Real.exp (-m * p / 4) := by
    simpa only [a, b, m, p] using hmiss
  have hscale : 0 ≤ d ^ 2 / m ^ 2 := by positivity
  have hQ : 0 ≤ (p ^ 2 + p / m) * Real.exp (-m * p / 4) := by
    positivity
  have hrewrite (N0 N1 : ℕ) :
      heavyCenteredEffectSecond P k t N0 N1 =
        (d ^ 2 / m ^ 2) * (guardedTotalCount N0 N1 - (m * p)) ^ 2 := by
    change ((guardedTotalCount N0 N1 / m - p) * d) ^ 2 = _
    field_simp [ne_of_gt hm]
  simp_rw [hrewrite]
  change (∫ N0 : ℕ, ∫ N1 : ℕ,
      (d ^ 2 / m ^ 2) * (guardedTotalCount N0 N1 - m * p) ^ 2
      ∂poissonMeasure b ∂poissonMeasure a) ≤ _
  simp_rw [integral_const_mul]
  calc
    _ ≤ (d ^ 2 / m ^ 2) *
        (2 * (m * p) + 2 *
          (Real.exp (-(a : ℝ)) * ((b : ℝ) ^ 2 + b) +
           Real.exp (-(b : ℝ)) * ((a : ℝ) ^ 2 + a))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      rw [← hab]
      exact hcount
    _ = 2 * d ^ 2 * (p / m) +
        2 * d ^ 2 * (1 / m ^ 2 *
          (Real.exp (-(a : ℝ)) * ((b : ℝ) ^ 2 + b) +
           Real.exp (-(b : ℝ)) * ((a : ℝ) ^ 2 + a))) := by
      field_simp
    _ ≤ 8 * M ^ 2 * (p / m) +
        16 * M ^ 2 * ((p ^ 2 + p / m) * Real.exp (-m * p / 4)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by nlinarith [hdSq]) (by positivity)
      · calc
          _ ≤ 2 * d ^ 2 *
              (2 * (p ^ 2 + p / m) * Real.exp (-m * p / 4)) := by
            rw [← missingCountSquareEnvelope_integral a b]
            exact mul_le_mul_of_nonneg_left hmiss' (by positivity)
          _ ≤ 16 * M ^ 2 *
              ((p ^ 2 + p / m) * Real.exp (-m * p / 4)) := by
            calc
              _ = 4 * d ^ 2 *
                  ((p ^ 2 + p / m) * Real.exp (-m * p / 4)) := by ring
              _ ≤ 16 * M ^ 2 *
                  ((p ^ 2 + p / m) * Real.exp (-m * p / 4)) :=
                mul_le_mul_of_nonneg_right (by nlinarith [hdSq]) hQ
    _ = _ := by ring

/-- Equation (39), with explicit constants, for one occupied cell. -/
lemma heavyCellConditionalVariance_le {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hoverlap : FixedOverlap P) (hmean : MeanEnvelope M P)
    (hvariance : VarianceEnvelope M P) (ht : AdmissiblePilotValue M t) :
    heavyCellConditionalVariance P k t ≤
      35 * M ^ 2 * P.cellMass k / blockMean n +
        16 * M ^ 2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
          Real.exp (-blockMean n * P.cellMass k / 4) := by
  unfold heavyCellConditionalVariance
  have hnoise := heavyOutcomeNoise_integral_le M P k hn hp hoverlap hvariance
  have heffect := heavyCenteredEffectSecond_integral_le M P k t hn hp
    hoverlap hmean ht
  calc
    _ ≤ 27 * M ^ 2 * P.cellMass k / blockMean n +
        8 * M ^ 2 * (P.cellMass k / blockMean n +
          2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
            Real.exp (-blockMean n * P.cellMass k / 4)) := add_le_add hnoise heffect
    _ = _ := by ring

lemma heavyCellConditionalVariance_eq_zero_of_cellMass_eq_zero {n : ℕ}
    (P : Law n) (k : Fin n) (t : ℝ) (hp : P.cellMass k = 0) :
    heavyCellConditionalVariance P k t = 0 := by
  have hrate (u : Bool) :
      Real.toNNReal (blockMean n * armMass P u k) = 0 := by
    simp [armMass, hp]
  unfold heavyCellConditionalVariance
  rw [hrate false, hrate true, poissonMeasure_zero_eq_dirac,
    integral_dirac, integral_dirac, integral_dirac, integral_dirac]
  rw [heavyOutcomeNoiseSecond_zero_zero]
  simp [heavyCenteredEffectSecond, hp]

/-- The global heavy-cell consequence of (39) and (41). -/
lemma sum_heavyCellConditionalVariance_le {n : ℕ} (M : ℝ) (P : Law n)
    (t : ℝ) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∑ k : Fin n, heavyCellConditionalVariance P k t) ≤
      115 * M ^ 2 / blockMean n := by
  have hcell (k : Fin n) : heavyCellConditionalVariance P k t ≤
      35 * M ^ 2 * P.cellMass k / blockMean n +
        16 * M ^ 2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
          Real.exp (-blockMean n * P.cellMass k / 4) := by
    rcases eq_or_lt_of_le (P.cellMass_range k).1 with hp | hp
    · have hzero : P.cellMass k = 0 := hp.symm
      rw [heavyCellConditionalVariance_eq_zero_of_cellMass_eq_zero P k t hzero]
      simp [hzero]
    · exact heavyCellConditionalVariance_le M P k t hn hp hoverlap hmean
        hvariance ht
  have hmissing := sum_heavy_missing_expression_le P hn
  calc
    _ ≤ ∑ k : Fin n, (35 * M ^ 2 * P.cellMass k / blockMean n +
        16 * M ^ 2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
          Real.exp (-blockMean n * P.cellMass k / 4)) :=
      Finset.sum_le_sum (fun k _ => hcell k)
    _ = 35 * M ^ 2 / blockMean n +
        16 * M ^ 2 * (∑ k : Fin n, (P.cellMass k ^ 2 +
          P.cellMass k / blockMean n) *
            Real.exp (-blockMean n * P.cellMass k / 4)) := by
      rw [Finset.sum_add_distrib]
      rw [show (∑ k : Fin n, 35 * M ^ 2 * P.cellMass k / blockMean n) =
          (35 * M ^ 2 / blockMean n) * ∑ k : Fin n, P.cellMass k by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
      rw [show (∑ k : Fin n,
          16 * M ^ 2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
            Real.exp (-blockMean n * P.cellMass k / 4)) =
          16 * M ^ 2 * (∑ k : Fin n, (P.cellMass k ^ 2 +
            P.cellMass k / blockMean n) *
              Real.exp (-blockMean n * P.cellMass k / 4)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
      rw [DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
      ring
    _ ≤ 35 * M ^ 2 / blockMean n + 16 * M ^ 2 * (5 / blockMean n) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmissing (by positivity))
    _ = _ := by ring

noncomputable def classifierMixtureVariance
    (alpha lightVariance heavyVariance lightMean heavyMean : ℝ) : ℝ :=
  alpha * lightVariance + (1 - alpha) * heavyVariance +
    alpha * (1 - alpha) * (lightMean - heavyMean) ^ 2

-- keep: reusable upper envelope for the classifier mixture variance
lemma classifierMixtureVariance_le {alpha lightVariance heavyVariance
    lightMean heavyMean : ℝ} (ha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    classifierMixtureVariance alpha lightVariance heavyVariance lightMean heavyMean ≤
      alpha * lightVariance + (1 - alpha) * heavyVariance +
        2 * alpha * (1 - alpha) * (lightMean ^ 2 + heavyMean ^ 2) := by
  unfold classifierMixtureVariance
  have hmix : 0 ≤ alpha * (1 - alpha) :=
    mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have hs : (lightMean - heavyMean) ^ 2 ≤
      2 * (lightMean ^ 2 + heavyMean ^ 2) := by
    nlinarith [sq_nonneg (lightMean + heavyMean)]
  have hx := mul_le_mul_of_nonneg_left hs hmix
  nlinarith

lemma heavyCellConditionalVariance_nonneg {n : ℕ} (P : Law n)
    (k : Fin n) (t : ℝ) : 0 ≤ heavyCellConditionalVariance P k t := by
  unfold heavyCellConditionalVariance
  exact add_nonneg
    (integral_nonneg fun _ => integral_nonneg (heavyOutcomeNoiseSecond_nonneg P k _))
    (integral_nonneg fun _ => integral_nonneg fun _ => by
      unfold heavyCenteredEffectSecond
      positivity)

/-- The heavy component in the classifier mixture is no larger than the
global bound from (39)--(41). -/
lemma sum_classifierWeighted_heavyVariance_le {n : ℕ} (M rho : ℝ)
    (P : Law n) (t : ℝ) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    (∑ k : Fin n, (1 - classificationProbability n rho P k) *
      heavyCellConditionalVariance P k t) ≤
      115 * M ^ 2 / blockMean n := by
  calc
    _ ≤ ∑ k : Fin n, heavyCellConditionalVariance P k t := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
      exact mul_le_of_le_one_left (heavyCellConditionalVariance_nonneg P k t)
        (sub_le_self 1 ha0)
    _ ≤ _ := sum_heavyCellConditionalVariance_le M P t hn hoverlap hmean
      hvariance ht

/-- Equation (44) assembly: once the light and classifier-mean terms have the
bound supplied by (37) and (43), the heavy term contributes only `115 M²/m`. -/
-- keep: paper equation (44) assembly theorem for light, heavy, and classifier terms
lemma classifierMixtureVariance_sum_le_of_light_cross {n : ℕ}
    (M rho R : ℝ) (P : Law n) (t : ℝ)
    (lightVariance : Fin n → ℝ) (lightMean : Fin n → ℝ)
    (heavyMean : Fin n → ℝ)
    (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t)
    (hlightCross :
      Finset.univ.sum (fun k : Fin n =>
        classificationProbability n rho P k * lightVariance k +
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k) *
              (lightMean k - heavyMean k) ^ 2) ≤ R) :
    Finset.univ.sum (fun k : Fin n => classifierMixtureVariance
      (classificationProbability n rho P k) (lightVariance k)
      (heavyCellConditionalVariance P k t) (lightMean k) (heavyMean k)) ≤
      R + 115 * M ^ 2 / blockMean n := by
  rw [show Finset.univ.sum (fun k : Fin n => classifierMixtureVariance
      (classificationProbability n rho P k) (lightVariance k)
      (heavyCellConditionalVariance P k t) (lightMean k) (heavyMean k)) =
      Finset.univ.sum (fun k : Fin n =>
        classificationProbability n rho P k * lightVariance k +
          classificationProbability n rho P k *
            (1 - classificationProbability n rho P k) *
              (lightMean k - heavyMean k) ^ 2) +
      Finset.univ.sum (fun k : Fin n =>
        (1 - classificationProbability n rho P k) *
          heavyCellConditionalVariance P k t) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold classifierMixtureVariance
    ring]
  exact add_le_add hlightCross
    (sum_classifierWeighted_heavyVariance_le M rho P t hn hoverlap hmean
      hvariance ht)

lemma mass_mul_classifier_exp_le {m p : ℝ} (hm : 0 < m) (hp : 0 ≤ p) :
    p * Real.exp (-m * p / 8) ≤ 8 / m := by
  let y := m * p / 8
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hcore := Real.mul_exp_neg_le_exp_neg_one y
  have hexp1 : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hscale : 0 ≤ 8 / m := by positivity
  calc
    p * Real.exp (-m * p / 8) = (8 / m) * (y * Real.exp (-y)) := by
      dsimp [y]
      field_simp
    _ ≤ (8 / m) * Real.exp (-1) := mul_le_mul_of_nonneg_left hcore hscale
    _ ≤ (8 / m) * 1 := mul_le_mul_of_nonneg_left hexp1 hscale
    _ = 8 / m := by ring

/-- Equation (43), with an explicit constant obtained by splitting at the
declared light scale. -/
lemma sum_cellMass_sq_classifier_mixing_le {n : ℕ} (rho : ℝ) (P : Law n)
    (hn : 0 < n) :
    (∑ k : Fin n, P.cellMass k ^ 2 * classificationProbability n rho P k *
      (1 - classificationProbability n rho P k)) ≤
      4104 * (degree n rho : ℝ) / blockMean n := by
  let B := lightScale n rho
  let K := degree n rho
  let m := blockMean n
  have hm : 0 < m := blockMean_pos n hn
  have hB0 : 0 ≤ B := (lightScale_pos n rho hn).le
  have hK : (1 : ℝ) ≤ K := by
    exact_mod_cast (show 1 ≤ K by simp [K, degree])
  have hpoint (k : Fin n) :
      P.cellMass k ^ 2 * classificationProbability n rho P k *
          (1 - classificationProbability n rho P k) ≤
        (B + 8 / m) * P.cellMass k := by
    let p := P.cellMass k
    let alpha := classificationProbability n rho P k
    have hp0 : 0 ≤ p := P.cellMass_range k |>.1
    obtain ⟨ha0, ha1⟩ := classificationProbability_mem_Icc rho P k
    have hmix0 : 0 ≤ alpha * (1 - alpha) :=
      mul_nonneg ha0 (sub_nonneg.mpr ha1)
    have hmix1 : alpha * (1 - alpha) ≤ 1 := by
      calc
        _ ≤ alpha * 1 := mul_le_mul_of_nonneg_left (sub_le_self 1 ha0) ha0
        _ ≤ 1 := by simpa using ha1
    by_cases hpB : p ≤ B
    · calc
        p ^ 2 * alpha * (1 - alpha) = p ^ 2 * (alpha * (1 - alpha)) := by ring
        _ ≤ p ^ 2 := by
          simpa using mul_le_mul_of_nonneg_left hmix1 (sq_nonneg p)
        _ ≤ B * p := by nlinarith
        _ ≤ (B + 8 / m) * p := by
          apply mul_le_mul_of_nonneg_right _ hp0
          exact le_add_of_nonneg_right (div_nonneg (by norm_num) hm.le)
    · have hpB' : B < p := lt_of_not_ge hpB
      have halpha := heavy_classification_error_bound rho P k hn hpB'
      have hexp0 : 0 ≤ Real.exp (-m * p / 8) := Real.exp_nonneg _
      have hpexp := mass_mul_classifier_exp_le hm hp0
      calc
        p ^ 2 * alpha * (1 - alpha) ≤ p ^ 2 * alpha := by
          have : 1 - alpha ≤ 1 := sub_le_self 1 ha0
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left this ha0) (sq_nonneg p)
        _ ≤ p ^ 2 * Real.exp (-m * p / 8) :=
          mul_le_mul_of_nonneg_left halpha (sq_nonneg p)
        _ = p * (p * Real.exp (-m * p / 8)) := by ring
        _ ≤ p * (8 / m) := mul_le_mul_of_nonneg_left hpexp hp0
        _ ≤ (B + 8 / m) * p := by
          rw [mul_comm p, add_mul]
          exact le_add_of_nonneg_left (mul_nonneg hB0 hp0)
  calc
    _ ≤ ∑ k : Fin n, (B + 8 / m) * P.cellMass k :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = B + 8 / m := by
      rw [← Finset.mul_sum,
        DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one, mul_one]
    _ = (4096 * (K : ℝ) + 8) / m := by
      rw [show B = 4096 * (K : ℝ) / m by rfl]
      ring
    _ ≤ 4104 * (K : ℝ) / m := by
      apply (div_le_div_iff_of_pos_right hm).2
      nlinarith

/-- Equation (33): on positive count fibres, the conditional numerator second
moment uses only the two conditional variances and the squared conditional mean. -/
lemma conditionalNumeratorSecond_le_six {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (t : ℝ) (N0 N1 : ℕ) (hp : 0 < P.cellMass k)
    (hmean : MeanEnvelope M P) (hvariance : VarianceEnvelope M P)
    (ht : AdmissiblePilotValue M t) :
    conditionalNumeratorSecond P k t N0 N1 ≤
      6 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 := by
  have hM0 : 0 ≤ M := by
    have h := hmean true k hp
    have ha := abs_nonneg (P.outcomeMean true k)
    linarith
  have hV0 := (hvariance false k hp).2
  have hV1 := (hvariance true k hp).2
  have hdAbs := cellEffect_sub_pilot_abs_le P k t hp hmean ht
  have hdSq :
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith [abs_nonneg (DiscreteAteHeterogeneityFrontier.cellEffect P k - t),
      sq_abs (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)]
  by_cases h0 : N0 = 0
  · subst N0
    simp [conditionalNumeratorSecond]
  by_cases h1 : N1 = 0
  · subst N1
    simp [conditionalNumeratorSecond]
  have h0one : (1 : ℝ) ≤ N0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have h1one : (1 : ℝ) ≤ N1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
  have hterm1 : (N0 : ℝ) ^ 2 * (N1 : ℝ) *
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) ≤
      M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 := by
    calc
      _ ≤ (N0 : ℝ) ^ 2 * (N1 : ℝ) * M ^ 2 := by gcongr <;> positivity
      _ ≤ _ := by
        have hs : (N1 : ℝ) ≤ (N1 : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg (N0 : ℝ))
          (mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hs))]
  have hterm0 : (N1 : ℝ) ^ 2 * (N0 : ℝ) *
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) ≤
      M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 := by
    calc
      _ ≤ (N1 : ℝ) ^ 2 * (N0 : ℝ) * M ^ 2 := by gcongr <;> positivity
      _ ≤ _ := by
        have hs : (N0 : ℝ) ≤ (N0 : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg (N1 : ℝ))
          (mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hs))]
  have heffect : (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 ≤
      4 * M ^ 2 * (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 := by
    calc
      _ ≤ ((N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2) * (4 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hdSq
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  unfold conditionalNumeratorSecond
  norm_num only [Nat.cast_mul]
  nlinarith

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

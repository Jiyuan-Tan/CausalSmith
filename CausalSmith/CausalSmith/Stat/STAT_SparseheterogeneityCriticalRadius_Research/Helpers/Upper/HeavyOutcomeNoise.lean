module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyPoissonKernel

/-! Outcome-noise part of the heavy conditional variance. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal

@[no_expose]
noncomputable def heavyOutcomeNoiseSecond {n : ℕ} (P : Law n) (k : Fin n)
    (N0 N1 : ℕ) : ℝ :=
  (((N0 : ℝ) ^ 2 * N1 *
      ∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
    ((N1 : ℝ) ^ 2 * N0 *
      ∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k)) *
    heavyCoefficient n N0 N1 ^ 2

lemma heavyOutcomeNoiseSecond_nonneg {n : ℕ} (P : Law n) (k : Fin n)
    (N0 N1 : ℕ) : 0 ≤ heavyOutcomeNoiseSecond P k N0 N1 := by
  have hV0 : 0 ≤ ∫ y, (y - P.outcomeMean false k) ^ 2
      ∂P.outcomeLaw false k := integral_nonneg fun _ => sq_nonneg _
  have hV1 : 0 ≤ ∫ y, (y - P.outcomeMean true k) ^ 2
      ∂P.outcomeLaw true k := integral_nonneg fun _ => sq_nonneg _
  unfold heavyOutcomeNoiseSecond
  positivity

lemma heavyOutcomeNoiseSecond_zero_zero {n : ℕ} (P : Law n) (k : Fin n) :
    heavyOutcomeNoiseSecond P k 0 0 = 0 := by
  simp [heavyOutcomeNoiseSecond]

lemma conditionalNumeratorSecond_decompose_noise {n : ℕ} (P : Law n)
    (k : Fin n) (t : ℝ) (N0 N1 : ℕ) :
    conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2 =
      heavyOutcomeNoiseSecond P k N0 N1 +
        ((N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2) *
            heavyCoefficient n N0 N1 ^ 2 := by
  unfold conditionalNumeratorSecond heavyOutcomeNoiseSecond
  ring

lemma heavyOutcomeNoiseSecond_le {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (N0 N1 : ℕ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    heavyOutcomeNoiseSecond P k N0 N1 ≤
      M ^ 2 / blockMean n ^ 2 * heavyNoiseCountKernel N0 N1 := by
  by_cases hz : N0 = 0 ∨ N1 = 0
  · rw [heavyNoiseCountKernel_eq_zero_of N0 N1 hz]
    simp [heavyOutcomeNoiseSecond, heavyCoefficient, hz]
  · have h0 : N0 ≠ 0 := (not_or.mp hz).1
    have h1 : N1 ≠ 0 := (not_or.mp hz).2
    have h0p : (0 : ℝ) < N0 := by exact_mod_cast Nat.pos_of_ne_zero h0
    have h1p : (0 : ℝ) < N1 := by exact_mod_cast Nat.pos_of_ne_zero h1
    have hm : blockMean n ≠ 0 := ne_of_gt (blockMean_pos n hn)
    have hV0 := (hvariance false k hp).2
    have hV1 := (hvariance true k hp).2
    have hd0 : (∫ y, (y - P.outcomeMean false k) ^ 2
        ∂P.outcomeLaw false k) / N0 ≤ M ^ 2 / N0 :=
      div_le_div_of_nonneg_right hV0 h0p.le
    have hd1 : (∫ y, (y - P.outcomeMean true k) ^ 2
        ∂P.outcomeLaw true k) / N1 ≤ M ^ 2 / N1 :=
      div_le_div_of_nonneg_right hV1 h1p.le
    rw [heavyOutcomeNoiseSecond, heavyCoefficient, if_neg (by simp [h0, h1]),
      heavyNoiseCountKernel_of_ne N0 N1 hz]
    norm_num only [Nat.cast_add, Nat.cast_mul]
    have hfac : 0 ≤ ((N0 : ℝ) + N1) ^ 2 / blockMean n ^ 2 := by positivity
    calc
      _ = (((N0 : ℝ) + N1) ^ 2 / blockMean n ^ 2) *
          ((∫ y, (y - P.outcomeMean true k) ^ 2
              ∂P.outcomeLaw true k) / N1 +
           (∫ y, (y - P.outcomeMean false k) ^ 2
              ∂P.outcomeLaw false k) / N0) := by
        field_simp
      _ ≤ (((N0 : ℝ) + N1) ^ 2 / blockMean n ^ 2) *
          (M ^ 2 / N1 + M ^ 2 / N0) :=
        mul_le_mul_of_nonneg_left (add_le_add hd1 hd0) hfac
      _ = _ := by field_simp; ring

lemma heavyOutcomeNoiseSecond_integrable_inner {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (b : ℝ≥0) (N0 : ℕ) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun N1 : ℕ => heavyOutcomeNoiseSecond P k N0 N1)
      (poissonMeasure b) := by
  let c := M ^ 2 / blockMean n ^ 2
  apply ((heavyNoiseCountKernel_integrable_inner b N0).const_mul c).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N1
  rw [Real.norm_eq_abs, abs_of_nonneg (heavyOutcomeNoiseSecond_nonneg P k N0 N1)]
  exact heavyOutcomeNoiseSecond_le M P k N0 N1 hn hp hvariance

lemma heavyOutcomeNoiseSecond_integrable_outer {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (a b : ℝ≥0) (hn : 0 < n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      heavyOutcomeNoiseSecond P k N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
  let c := M ^ 2 / blockMean n ^ 2
  have hkout : Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
    apply (heavyNoiseSeparableEnvelope_integrable_outer a b).mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg (heavyNoiseCountKernel_nonneg N0))]
    exact heavyNoiseCountKernel_inner_integral_le b N0
  apply (hkout.const_mul c).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N0
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg
    (heavyOutcomeNoiseSecond_nonneg P k N0))]
  calc
    _ ≤ ∫ N1 : ℕ, c * heavyNoiseCountKernel N0 N1 ∂poissonMeasure b :=
      integral_mono (heavyOutcomeNoiseSecond_integrable_inner M P k b N0 hn hp hvariance)
        ((heavyNoiseCountKernel_integrable_inner b N0).const_mul c)
        (fun N1 => heavyOutcomeNoiseSecond_le M P k N0 N1 hn hp hvariance)
    _ = _ := by rw [integral_const_mul]

/-- The conditional outcome-noise contribution in (39), obtained by combining
the variance envelope with equation (40). -/
lemma heavyOutcomeNoise_integral_le {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n) (hp : 0 < P.cellMass k)
    (hoverlap : FixedOverlap P) (hvariance : VarianceEnvelope M P) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, heavyOutcomeNoiseSecond P k N0 N1
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P false k))) ≤
      27 * M ^ 2 * P.cellMass k / blockMean n := by
  let a := Real.toNNReal (blockMean n * armMass P false k)
  let b := Real.toNNReal (blockMean n * armMass P true k)
  let c := M ^ 2 / blockMean n ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hkin (N0 : ℕ) := heavyNoiseCountKernel_integrable_inner b N0
  have hnin (N0 : ℕ) : Integrable
      (fun N1 : ℕ => heavyOutcomeNoiseSecond P k N0 N1)
      (poissonMeasure b) := by
    apply (hkin N0).const_mul c |>.mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N1
    rw [Real.norm_eq_abs, abs_of_nonneg (heavyOutcomeNoiseSecond_nonneg P k N0 N1)]
    exact heavyOutcomeNoiseSecond_le M P k N0 N1 hn hp hvariance
  have hinle (N0 : ℕ) :
      (∫ N1 : ℕ, heavyOutcomeNoiseSecond P k N0 N1 ∂poissonMeasure b) ≤
        ∫ N1 : ℕ, c * heavyNoiseCountKernel N0 N1 ∂poissonMeasure b :=
    integral_mono (hnin N0) ((hkin N0).const_mul c)
      (fun N1 => heavyOutcomeNoiseSecond_le M P k N0 N1 hn hp hvariance)
  have hkout : Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
    have he := heavyNoiseSeparableEnvelope_integrable_outer a b
    apply he.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg (heavyNoiseCountKernel_nonneg N0))]
    exact heavyNoiseCountKernel_inner_integral_le b N0
  have hnout : Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, heavyOutcomeNoiseSecond P k N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
    apply hkout.const_mul c |>.mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg
      (heavyOutcomeNoiseSecond_nonneg P k N0))]
    calc
      _ ≤ ∫ N1 : ℕ, c * heavyNoiseCountKernel N0 N1 ∂poissonMeasure b :=
        hinle N0
      _ = c * ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b := by
        rw [integral_const_mul]
  calc
    _ ≤ ∫ N0 : ℕ, c *
          (∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b)
        ∂poissonMeasure a := by
      apply integral_mono hnout (hkout.const_mul c)
      intro N0
      calc
        _ ≤ ∫ N1 : ℕ, c * heavyNoiseCountKernel N0 N1
              ∂poissonMeasure b := hinle N0
        _ = _ := by rw [integral_const_mul]
    _ = c * (∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1
          ∂poissonMeasure b ∂poissonMeasure a) := by rw [integral_const_mul]
    _ ≤ _ := heavyNoiseCountKernel_arm_scaled_le M P k hn hoverlap

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

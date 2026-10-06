module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyNoiseRate

/-! The product-Poisson count kernel in the heavy correction. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- The guarded count factor in the noise part of the heavy correction. -/
@[no_expose]
noncomputable def heavyNoiseCountKernel (N0 N1 : ℕ) : ℝ :=
  if N0 = 0 ∨ N1 = 0 then 0 else
    ((N0 + N1 : ℕ) : ℝ) ^ 2 *
      (1 / (N0 : ℝ) + 1 / (N1 : ℝ))

lemma heavyNoiseCountKernel_eq_zero_of (N0 N1 : ℕ)
    (h : N0 = 0 ∨ N1 = 0) : heavyNoiseCountKernel N0 N1 = 0 := by
  rw [heavyNoiseCountKernel, if_pos h]

lemma heavyNoiseCountKernel_of_ne (N0 N1 : ℕ)
    (h : ¬ (N0 = 0 ∨ N1 = 0)) :
    heavyNoiseCountKernel N0 N1 = ((N0 + N1 : ℕ) : ℝ) ^ 2 *
      (1 / (N0 : ℝ) + 1 / (N1 : ℝ)) := by
  rw [heavyNoiseCountKernel, if_neg h]

/-- A separable envelope whose product-Poisson integral uses only first,
second, and guarded reciprocal moments. -/
@[no_expose]
noncomputable def heavyNoiseSeparableEnvelope (N0 N1 : ℕ) : ℝ :=
  3 * ((N0 : ℝ) + N1) +
    (N1 : ℝ) ^ 2 * guardedNatReciprocal N0 +
    (N0 : ℝ) ^ 2 * guardedNatReciprocal N1

lemma heavyNoiseCountKernel_nonneg (N0 N1 : ℕ) :
    0 ≤ heavyNoiseCountKernel N0 N1 := by
  by_cases h : N0 = 0 ∨ N1 = 0
  · simp [heavyNoiseCountKernel, h]
  · rw [heavyNoiseCountKernel, if_neg h]
    have h0 : (0 : ℝ) < N0 := by exact_mod_cast Nat.pos_of_ne_zero (not_or.mp h).1
    have h1 : (0 : ℝ) < N1 := by exact_mod_cast Nat.pos_of_ne_zero (not_or.mp h).2
    positivity

lemma heavyNoiseSeparableEnvelope_nonneg (N0 N1 : ℕ) :
    0 ≤ heavyNoiseSeparableEnvelope N0 N1 := by
  unfold heavyNoiseSeparableEnvelope
  have hg0 : 0 ≤ guardedNatReciprocal N0 := by
    by_cases h : N0 = 0
    · subst N0; simp
    · rw [guardedNatReciprocal_of_ne h]
      positivity
  have hg1 : 0 ≤ guardedNatReciprocal N1 := by
    by_cases h : N1 = 0
    · subst N1; simp
    · rw [guardedNatReciprocal_of_ne h]
      positivity
  positivity

lemma heavyNoiseCountKernel_le_envelope (N0 N1 : ℕ) :
    heavyNoiseCountKernel N0 N1 ≤ heavyNoiseSeparableEnvelope N0 N1 := by
  by_cases h : N0 = 0 ∨ N1 = 0
  · rw [heavyNoiseCountKernel, if_pos h]
    exact heavyNoiseSeparableEnvelope_nonneg N0 N1
  · have h0 : N0 ≠ 0 := (not_or.mp h).1
    have h1 : N1 ≠ 0 := (not_or.mp h).2
    rw [heavyNoiseCountKernel, if_neg h]
    rw [heavyNoiseSeparableEnvelope, guardedNatReciprocal_of_ne h0,
      guardedNatReciprocal_of_ne h1]
    norm_num only [Nat.cast_add]
    have h0r : (N0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have h1r : (N1 : ℝ) ≠ 0 := by exact_mod_cast h1
    field_simp
    ring_nf
    exact le_rfl

/-- Exact deterministic separation of the heavy conditional numerator on
positive count fibres. -/
-- keep: exact heavy-branch factorization used to inspect count and noise contributions
lemma conditionalNumeratorSecond_mul_heavyCoefficient_sq
    {n : ℕ} (P : Law n) (k : Fin n) (t : ℝ) (N0 N1 : ℕ)
    (hn : 0 < n) (h0 : N0 ≠ 0) (h1 : N1 ≠ 0) :
    conditionalNumeratorSecond P k t N0 N1 * heavyCoefficient n N0 N1 ^ 2 =
      (((N0 + N1 : ℕ) : ℝ) ^ 2 / blockMean n ^ 2) *
        ((∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) / N1 +
         (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) / N0 +
         (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2) := by
  have hm : blockMean n ≠ 0 := ne_of_gt (blockMean_pos n hn)
  have h0r : (N0 : ℝ) ≠ 0 := by exact_mod_cast h0
  have h1r : (N1 : ℝ) ≠ 0 := by exact_mod_cast h1
  rw [heavyCoefficient, if_neg (by simp [h0, h1])]
  unfold conditionalNumeratorSecond
  norm_num only [Nat.cast_add, Nat.cast_mul]
  field_simp

lemma heavyNoiseSeparableEnvelope_inner_integral (a b : ℝ≥0) (N0 : ℕ) :
    (∫ N1 : ℕ, heavyNoiseSeparableEnvelope N0 N1 ∂poissonMeasure b) =
      3 * ((N0 : ℝ) + (b : ℝ)) +
        ((b : ℝ) ^ 2 + b) * guardedNatReciprocal N0 +
        (N0 : ℝ) ^ 2 *
          (∫ N1 : ℕ, guardedNatReciprocal N1 ∂poissonMeasure b) := by
  let μ := poissonMeasure b
  have hcount : Integrable (fun N1 : ℕ => (N1 : ℝ)) μ :=
    (poisson_natCast_memLp_two b).integrable (by norm_num)
  have hsq : Integrable (fun N1 : ℕ => (N1 : ℝ) ^ 2) μ :=
    integrable_poisson_count_sq b
  have hrecip : Integrable guardedNatReciprocal μ :=
    guardedNatReciprocal_integrable b
  have hc : Integrable (fun _ : ℕ => 3 * (N0 : ℝ)) μ :=
    integrable_const _
  have h3count : Integrable (fun N1 : ℕ => 3 * (N1 : ℝ)) μ :=
    hcount.const_mul 3
  have hsqg : Integrable
      (fun N1 : ℕ => guardedNatReciprocal N0 * (N1 : ℝ) ^ 2) μ :=
    hsq.const_mul _
  have hsqrecip : Integrable
      (fun N1 : ℕ => (N0 : ℝ) ^ 2 * guardedNatReciprocal N1) μ :=
    hrecip.const_mul _
  let f0 : ℕ → ℝ := fun _ => 3 * (N0 : ℝ)
  let f1 : ℕ → ℝ := fun N1 => 3 * (N1 : ℝ)
  let f2 : ℕ → ℝ := fun N1 =>
    guardedNatReciprocal N0 * (N1 : ℝ) ^ 2
  let f3 : ℕ → ℝ := fun N1 =>
    (N0 : ℝ) ^ 2 * guardedNatReciprocal N1
  have hfun : (fun N1 : ℕ => heavyNoiseSeparableEnvelope N0 N1) =
      fun N1 => ((f0 N1 + f1 N1) + f2 N1) + f3 N1 := by
      funext N1
      simp only [f0, f1, f2, f3, heavyNoiseSeparableEnvelope]
      ring
  have hs01 : (∫ N1, f0 N1 + f1 N1 ∂μ) =
      (∫ N1, f0 N1 ∂μ) + ∫ N1, f1 N1 ∂μ := by
    simpa only [f0, f1] using integral_add hc h3count
  have hs012 : (∫ N1, (f0 N1 + f1 N1) + f2 N1 ∂μ) =
      (∫ N1, f0 N1 + f1 N1 ∂μ) + ∫ N1, f2 N1 ∂μ := by
    apply integral_add
    · have hx := hc.add h3count
      change Integrable (fun N1 : ℕ => 3 * (N0 : ℝ) + 3 * (N1 : ℝ)) μ at hx
      simpa only [f0, f1] using hx
    · simpa only [f2] using hsqg
  have hs0123 : (∫ N1, ((f0 N1 + f1 N1) + f2 N1) + f3 N1 ∂μ) =
      (∫ N1, (f0 N1 + f1 N1) + f2 N1 ∂μ) +
        ∫ N1, f3 N1 ∂μ := by
    apply integral_add
    · exact (by
        apply Integrable.add
        · have hx := hc.add h3count
          change Integrable
            (fun N1 : ℕ => 3 * (N0 : ℝ) + 3 * (N1 : ℝ)) μ at hx
          simpa only [f0, f1] using hx
        · simpa only [f2] using hsqg)
    · simpa only [f3] using hsqrecip
  have hv0 : (∫ N1 : ℕ, f0 N1 ∂μ) = 3 * (N0 : ℝ) := by
    simp [f0]
  have hv1 : (∫ N1 : ℕ, f1 N1 ∂μ) = 3 * (b : ℝ) := by
    rw [show (∫ N1 : ℕ, f1 N1 ∂μ) =
      3 * ∫ N1 : ℕ, (N1 : ℝ) ∂μ by
        simp [f1, integral_const_mul]]
    rw [show (∫ N1 : ℕ, (N1 : ℝ) ∂μ) = (b : ℝ) by
      simpa [μ] using poisson_count_first_moment b]
  have hv2 : (∫ N1 : ℕ, f2 N1 ∂μ) =
      guardedNatReciprocal N0 * ((b : ℝ) ^ 2 + b) := by
    rw [show (∫ N1 : ℕ, f2 N1 ∂μ) = guardedNatReciprocal N0 *
        ∫ N1 : ℕ, (N1 : ℝ) ^ 2 ∂μ by
      simp [f2, integral_const_mul]]
    rw [show (∫ N1 : ℕ, (N1 : ℝ) ^ 2 ∂μ) =
        (b : ℝ) ^ 2 + b by
      simpa [μ] using poisson_count_second_moment b]
  have hv3 : (∫ N1 : ℕ, f3 N1 ∂μ) =
      (N0 : ℝ) ^ 2 *
        (∫ N1 : ℕ, guardedNatReciprocal N1 ∂poissonMeasure b) := by
    simp [f3, μ, integral_const_mul]
  rw [hfun]
  calc
    _ = (∫ N1, (f0 N1 + f1 N1) + f2 N1 ∂μ) + ∫ N1, f3 N1 ∂μ :=
      hs0123
    _ = ((∫ N1, f0 N1 + f1 N1 ∂μ) + ∫ N1, f2 N1 ∂μ) +
        ∫ N1, f3 N1 ∂μ := by rw [hs012]
    _ = (((∫ N1, f0 N1 ∂μ) + ∫ N1, f1 N1 ∂μ) +
        ∫ N1, f2 N1 ∂μ) + ∫ N1, f3 N1 ∂μ := by rw [hs01]
    _ = _ := by rw [hv0, hv1, hv2, hv3]; ring

/-- Exact product-Poisson factorization of the separable envelope. -/
lemma heavyNoiseSeparableEnvelope_integral (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseSeparableEnvelope N0 N1
        ∂poissonMeasure b ∂poissonMeasure a) =
      3 * ((a : ℝ) + b) +
        ((b : ℝ) ^ 2 + b) *
          (∫ N0 : ℕ, guardedNatReciprocal N0 ∂poissonMeasure a) +
        ((a : ℝ) ^ 2 + a) *
          (∫ N1 : ℕ, guardedNatReciprocal N1 ∂poissonMeasure b) := by
  simp_rw [heavyNoiseSeparableEnvelope_inner_integral a b]
  let μ : Measure ℕ := poissonMeasure a
  let rB : ℝ := ∫ N1 : ℕ, guardedNatReciprocal N1 ∂poissonMeasure b
  let f0 : ℕ → ℝ := fun N0 => 3 * ((N0 : ℝ) + (b : ℝ))
  let f1 : ℕ → ℝ := fun N0 =>
    ((b : ℝ) ^ 2 + b) * guardedNatReciprocal N0
  let f2 : ℕ → ℝ := fun N0 => (N0 : ℝ) ^ 2 * rB
  have hcount : Integrable (fun N0 : ℕ => (N0 : ℝ)) μ :=
    (poisson_natCast_memLp_two a).integrable (by norm_num)
  have hsq : Integrable (fun N0 : ℕ => (N0 : ℝ) ^ 2) μ :=
    integrable_poisson_count_sq a
  have hrecip : Integrable guardedNatReciprocal μ :=
    guardedNatReciprocal_integrable a
  have hfirst : Integrable f0 μ := by
    dsimp only [f0]
    exact (hcount.add (integrable_const _)).const_mul 3
  have hsecond : Integrable f1 μ := by
    dsimp only [f1]
    exact hrecip.const_mul _
  have hthird : Integrable f2 μ := by
    dsimp only [f2]
    exact hsq.mul_const _
  have hs01 : (∫ N0, f0 N0 + f1 N0 ∂μ) =
      (∫ N0, f0 N0 ∂μ) + ∫ N0, f1 N0 ∂μ :=
    integral_add hfirst hsecond
  have hs012 : (∫ N0, (f0 N0 + f1 N0) + f2 N0 ∂μ) =
      (∫ N0, f0 N0 + f1 N0 ∂μ) + ∫ N0, f2 N0 ∂μ :=
    integral_add (hfirst.add hsecond) hthird
  have hv0 : (∫ N0, f0 N0 ∂μ) = 3 * ((a : ℝ) + b) := by
    rw [show f0 = fun N0 : ℕ => 3 * (N0 : ℝ) + 3 * (b : ℝ) by
      funext N0; simp only [f0]; ring]
    rw [integral_add (hcount.const_mul 3) (integrable_const _),
      integral_const_mul, integral_const]
    rw [show (∫ N0 : ℕ, (N0 : ℝ) ∂μ) = (a : ℝ) by
      simpa [μ] using poisson_count_first_moment a]
    simp [μ]
    ring
  have hv1 : (∫ N0, f1 N0 ∂μ) =
      ((b : ℝ) ^ 2 + b) *
        (∫ N0 : ℕ, guardedNatReciprocal N0 ∂poissonMeasure a) := by
    simp [f1, μ, integral_const_mul]
  have hv2 : (∫ N0, f2 N0 ∂μ) = ((a : ℝ) ^ 2 + a) * rB := by
    rw [show (∫ N0, f2 N0 ∂μ) =
        (∫ N0 : ℕ, (N0 : ℝ) ^ 2 ∂μ) * rB by
      simp [f2, integral_mul_const]]
    rw [show (∫ N0 : ℕ, (N0 : ℝ) ^ 2 ∂μ) =
        (a : ℝ) ^ 2 + a by
      simpa [μ] using poisson_count_second_moment a]
  change (∫ N0, (f0 N0 + f1 N0) + f2 N0 ∂μ) = _
  calc
    _ = (∫ N0, f0 N0 + f1 N0 ∂μ) + ∫ N0, f2 N0 ∂μ := hs012
    _ = ((∫ N0, f0 N0 ∂μ) + ∫ N0, f1 N0 ∂μ) +
        ∫ N0, f2 N0 ∂μ := by rw [hs01]
    _ = _ := by rw [hv0, hv1, hv2]

lemma heavyNoiseSeparableEnvelope_integrable_inner (b : ℝ≥0) (N0 : ℕ) :
    Integrable (fun N1 : ℕ => heavyNoiseSeparableEnvelope N0 N1)
      (poissonMeasure b) := by
  have hcount : Integrable (fun N1 : ℕ => (N1 : ℝ)) (poissonMeasure b) :=
    (poisson_natCast_memLp_two b).integrable (by norm_num)
  have hsq : Integrable (fun N1 : ℕ => (N1 : ℝ) ^ 2) (poissonMeasure b) :=
    integrable_poisson_count_sq b
  have hrecip := guardedNatReciprocal_integrable b
  rw [show (fun N1 : ℕ => heavyNoiseSeparableEnvelope N0 N1) =
      fun (N1 : ℕ) => ((3 * (N0 : ℝ) + 3 * (N1 : ℝ)) +
        guardedNatReciprocal N0 * (N1 : ℝ) ^ 2) +
        (N0 : ℝ) ^ 2 * guardedNatReciprocal N1 by
      funext N1
      unfold heavyNoiseSeparableEnvelope
      ring]
  exact (((integrable_const _).add (hcount.const_mul 3)).add
    (hsq.const_mul _)).add (hrecip.const_mul _)

lemma heavyNoiseCountKernel_integrable_inner (b : ℝ≥0) (N0 : ℕ) :
    Integrable (fun N1 : ℕ => heavyNoiseCountKernel N0 N1)
      (poissonMeasure b) := by
  apply (heavyNoiseSeparableEnvelope_integrable_inner b N0).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N1
  rw [Real.norm_eq_abs, abs_of_nonneg (heavyNoiseCountKernel_nonneg N0 N1)]
  exact heavyNoiseCountKernel_le_envelope N0 N1

lemma heavyNoiseCountKernel_inner_integral_le (b : ℝ≥0) (N0 : ℕ) :
    (∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b) ≤
      ∫ N1 : ℕ, heavyNoiseSeparableEnvelope N0 N1 ∂poissonMeasure b := by
  exact integral_mono (heavyNoiseCountKernel_integrable_inner b N0)
    (heavyNoiseSeparableEnvelope_integrable_inner b N0)
    (heavyNoiseCountKernel_le_envelope N0)

lemma heavyNoiseSeparableEnvelope_integrable_outer (a b : ℝ≥0) :
    Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, heavyNoiseSeparableEnvelope N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
  simp_rw [heavyNoiseSeparableEnvelope_inner_integral a b]
  have hcount : Integrable (fun N0 : ℕ => (N0 : ℝ)) (poissonMeasure a) :=
    (poisson_natCast_memLp_two a).integrable (by norm_num)
  have hsq : Integrable (fun N0 : ℕ => (N0 : ℝ) ^ 2) (poissonMeasure a) :=
    integrable_poisson_count_sq a
  have hrecip := guardedNatReciprocal_integrable a
  exact ((hcount.add (integrable_const _)).const_mul 3 |>.add
    (hrecip.const_mul _)).add (hsq.mul_const _)

/-- Product-Poisson form of equation (40), before specialization to the arm
rates.  The right side is exactly the scalar rate expression controlled by
`heavy_noise_rate_envelope`. -/
lemma heavyNoiseCountKernel_integral_le_rate (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1
        ∂poissonMeasure b ∂poissonMeasure a) ≤
      3 * ((a : ℝ) + b) +
        ((b : ℝ) ^ 2 + b) * min (a : ℝ) (2 / (a : ℝ)) +
        ((a : ℝ) ^ 2 + a) * min (b : ℝ) (2 / (b : ℝ)) := by
  have houterEnv := heavyNoiseSeparableEnvelope_integrable_outer a b
  have hinnerNonneg (N0 : ℕ) :
      0 ≤ ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b :=
    integral_nonneg (heavyNoiseCountKernel_nonneg N0)
  have houterKernel : Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
    apply houterEnv.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    rw [Real.norm_eq_abs, abs_of_nonneg (hinnerNonneg N0)]
    exact heavyNoiseCountKernel_inner_integral_le b N0
  calc
    _ ≤ ∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseSeparableEnvelope N0 N1
          ∂poissonMeasure b ∂poissonMeasure a :=
      integral_mono houterKernel houterEnv
        (heavyNoiseCountKernel_inner_integral_le b)
    _ = 3 * ((a : ℝ) + b) +
        ((b : ℝ) ^ 2 + b) *
          (∫ N0 : ℕ, guardedNatReciprocal N0 ∂poissonMeasure a) +
        ((a : ℝ) ^ 2 + a) *
          (∫ N1 : ℕ, guardedNatReciprocal N1 ∂poissonMeasure b) :=
      heavyNoiseSeparableEnvelope_integral a b
    _ ≤ _ := by
      have ha := poisson_guarded_reciprocal_le_min a
      have hb := poisson_guarded_reciprocal_le_min b
      have hac : 0 ≤ (a : ℝ) ^ 2 + a := by positivity
      have hbc : 0 ≤ (b : ℝ) ^ 2 + b := by positivity
      nlinarith [mul_nonneg hbc (sub_nonneg.mpr ha),
        mul_nonneg hac (sub_nonneg.mpr hb)]

/-- Equation (40) for the actual false/true audit arm counts, at the count
kernel scale. -/
lemma heavyNoiseCountKernel_arm_integral_le {n : ℕ} (P : Law n) (k : Fin n)
    (hn : 0 < n) (hoverlap : FixedOverlap P) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P true k))
        ∂poissonMeasure
          (Real.toNNReal (blockMean n * armMass P false k))) ≤
      27 * blockMean n * P.cellMass k := by
  let a : ℝ≥0 := Real.toNNReal (blockMean n * armMass P false k)
  let b : ℝ≥0 := Real.toNNReal (blockMean n * armMass P true k)
  have hm : 0 < blockMean n := blockMean_pos n hn
  have hp0 := (P.cellMass_range k).1
  have hpi := P.propensity_range k
  have ha0 : 0 ≤ blockMean n * armMass P false k := by
    simp only [armMass, Bool.false_eq_true, ↓reduceIte]
    have hcontrol : 0 ≤ 1 - P.propensity k := sub_nonneg.mpr hpi.2
    exact mul_nonneg hm.le (mul_nonneg hp0 hcontrol)
  have hb0 : 0 ≤ blockMean n * armMass P true k := by
    simp only [armMass, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 hpi.1)
  have ha : (a : ℝ) = blockMean n * armMass P false k := by
    exact Real.coe_toNNReal _ ha0
  have hb : (b : ℝ) = blockMean n * armMass P true k := by
    exact Real.coe_toNNReal _ hb0
  calc
    _ ≤ 3 * ((a : ℝ) + b) +
        ((b : ℝ) ^ 2 + b) * min (a : ℝ) (2 / (a : ℝ)) +
        ((a : ℝ) ^ 2 + a) * min (b : ℝ) (2 / (b : ℝ)) :=
      heavyNoiseCountKernel_integral_le_rate a b
    _ ≤ 27 * (blockMean n * P.cellMass k) := by
      rw [ha, hb]
      exact heavy_noise_arm_rate_envelope P k hn hoverlap
    _ = _ := by ring

/-- Equation (40), including its `M²/m²` normalization. -/
lemma heavyNoiseCountKernel_arm_scaled_le {n : ℕ} (M : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P) :
    M ^ 2 / blockMean n ^ 2 *
        (∫ N0 : ℕ, ∫ N1 : ℕ, heavyNoiseCountKernel N0 N1
          ∂poissonMeasure
            (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure
            (Real.toNNReal (blockMean n * armMass P false k))) ≤
      27 * M ^ 2 * P.cellMass k / blockMean n := by
  have hm : 0 < blockMean n := blockMean_pos n hn
  have hscale : 0 ≤ M ^ 2 / blockMean n ^ 2 := by positivity
  calc
    _ ≤ M ^ 2 / blockMean n ^ 2 *
        (27 * blockMean n * P.cellMass k) :=
      mul_le_mul_of_nonneg_left
        (heavyNoiseCountKernel_arm_integral_le P k hn hoverlap) hscale
    _ = _ := by field_simp

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

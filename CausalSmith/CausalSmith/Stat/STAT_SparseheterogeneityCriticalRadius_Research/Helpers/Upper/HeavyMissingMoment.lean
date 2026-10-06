module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyMissingSum
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyOutcomeNoise

/-! Exact Poisson zero-atom moments used for the missing-arm part of (39). -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

lemma poisson_zero_atom_integral (r : ℝ≥0) (c : ℝ) :
    (∫ z : ℕ, if z = 0 then c else 0 ∂poissonMeasure r) =
      c * Real.exp (-(r : ℝ)) := by
  rw [show (fun z : ℕ => if z = 0 then c else 0) =
      ({0} : Set ℕ).indicator (fun _ => c) by
    funext z
    simp [Set.indicator_apply]]
  rw [integral_indicator (MeasurableSet.singleton 0), setIntegral_const]
  have h := congrArg ENNReal.toReal (poissonMeasure_singleton r 0)
  simp at h
  change (poissonMeasure r {0}).toReal * c = _
  rw [h, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  ring

@[no_expose]
noncomputable def missingCountSquareEnvelope (N0 N1 : ℕ) : ℝ :=
  (if N0 = 0 then (N1 : ℝ) ^ 2 else 0) +
    (if N1 = 0 then (N0 : ℝ) ^ 2 else 0)

@[no_expose]
noncomputable def guardedTotalCount (N0 N1 : ℕ) : ℝ :=
  if N0 = 0 ∨ N1 = 0 then 0 else ((N0 + N1 : ℕ) : ℝ)

@[simp] lemma guardedTotalCount_zero_zero : guardedTotalCount 0 0 = 0 := by
  simp [guardedTotalCount]

lemma heavySignalCoefficient_eq_guarded {n : ℕ} (t d : ℝ) (N0 N1 : ℕ)
    (hn : 0 < n) :
    ((N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 * (d - t) ^ 2) *
        heavyCoefficient n N0 N1 ^ 2 =
      (d - t) ^ 2 / blockMean n ^ 2 * guardedTotalCount N0 N1 ^ 2 := by
  by_cases hz : N0 = 0 ∨ N1 = 0
  · rw [heavyCoefficient, if_pos hz, guardedTotalCount, if_pos hz]
    simp
  · have hm : blockMean n ≠ 0 := ne_of_gt (blockMean_pos n hn)
    have h0r : (N0 : ℝ) ≠ 0 := by
      exact_mod_cast (not_or.mp hz).1
    have h1r : (N1 : ℝ) ≠ 0 := by
      exact_mod_cast (not_or.mp hz).2
    rw [heavyCoefficient, if_neg hz, guardedTotalCount, if_neg hz]
    norm_num only [Nat.cast_add, Nat.cast_mul]
    field_simp

lemma heavyWeightedCount_eq_guarded {n : ℕ} (N0 N1 : ℕ) (hn : 0 < n) :
    (N0 : ℝ) * (N1 : ℝ) * heavyCoefficient n N0 N1 =
      guardedTotalCount N0 N1 / blockMean n := by
  by_cases hz : N0 = 0 ∨ N1 = 0
  · rw [heavyCoefficient, if_pos hz, guardedTotalCount, if_pos hz]
    simp
  · have hm : blockMean n ≠ 0 := (blockMean_pos n hn).ne'
    have h0r : (N0 : ℝ) ≠ 0 := by exact_mod_cast (not_or.mp hz).1
    have h1r : (N1 : ℝ) ≠ 0 := by exact_mod_cast (not_or.mp hz).2
    rw [heavyCoefficient, if_neg hz, guardedTotalCount, if_neg hz]
    norm_num only [Nat.cast_add, Nat.cast_mul]
    field_simp

lemma guardedTotalCount_inner_integral (b : ℝ≥0) (N0 : ℕ) :
    (∫ N1 : ℕ, guardedTotalCount N0 N1 ∂poissonMeasure b) =
      if N0 = 0 then 0 else
        (N0 : ℝ) + (b : ℝ) - (N0 : ℝ) * Real.exp (-(b : ℝ)) := by
  by_cases h0 : N0 = 0
  · subst N0
    simp [guardedTotalCount]
  · have hcount : Integrable (fun N1 : ℕ => (N0 : ℝ) + N1)
        (poissonMeasure b) :=
      (integrable_const _).add ((poisson_natCast_memLp_two b).integrable (by norm_num))
    have hzero : Integrable (fun N1 : ℕ => if N1 = 0 then (N0 : ℝ) else 0)
        (poissonMeasure b) := by
      apply (integrable_const (N0 : ℝ)).mono'
        (measurable_of_countable _).aestronglyMeasurable
      filter_upwards with N1
      split <;> simp
    rw [show (fun N1 : ℕ => guardedTotalCount N0 N1) = fun N1 : ℕ =>
        ((N0 : ℝ) + (N1 : ℝ)) - (if N1 = 0 then (N0 : ℝ) else 0) by
      funext N1
      by_cases h1 : N1 = 0
      · simp [guardedTotalCount, h1]
      · simp [guardedTotalCount, h0, h1]]
    rw [integral_sub hcount hzero, integral_add (integrable_const _)
      ((poisson_natCast_memLp_two b).integrable (by norm_num)),
      poisson_count_first_moment, poisson_zero_atom_integral]
    simp [h0]

lemma guardedTotalCount_integral (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, guardedTotalCount N0 N1
      ∂poissonMeasure b ∂poissonMeasure a) =
      (a : ℝ) * (1 - Real.exp (-(b : ℝ))) +
        (b : ℝ) * (1 - Real.exp (-(a : ℝ))) := by
  simp_rw [guardedTotalCount_inner_integral]
  let c := 1 - Real.exp (-(b : ℝ))
  have hcount := (poisson_natCast_memLp_two a).integrable (by norm_num)
  rw [show (fun N0 : ℕ => if N0 = 0 then 0 else
      (N0 : ℝ) + (b : ℝ) - (N0 : ℝ) * Real.exp (-(b : ℝ))) =
      fun N0 : ℕ => c * (N0 : ℝ) + (b : ℝ) -
        (if N0 = 0 then (b : ℝ) else 0) by
    funext N0
    dsimp only [c]
    split <;> simp_all <;> ring]
  let f : ℕ → ℝ := fun N0 => c * (N0 : ℝ) + (b : ℝ)
  let z : ℕ → ℝ := fun N0 => if N0 = 0 then (b : ℝ) else 0
  have hf : Integrable f (poissonMeasure a) :=
    (hcount.const_mul c).add (integrable_const _)
  have hz : Integrable z (poissonMeasure a) := by
    apply (integrable_const (b : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    dsimp only [z]
    split <;> simp
  change (∫ N0 : ℕ, f N0 - z N0 ∂poissonMeasure a) = _
  rw [integral_sub hf hz]
  change (∫ N0 : ℕ, c * (N0 : ℝ) + (b : ℝ) ∂poissonMeasure a) -
    (∫ N0 : ℕ, if N0 = 0 then (b : ℝ) else 0 ∂poissonMeasure a) = _
  rw [integral_add (hcount.const_mul c) (integrable_const _),
    integral_const_mul, poisson_count_first_moment, poisson_zero_atom_integral]
  simp only [integral_const, smul_eq_mul, measureReal_def,
    IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_mul]
  dsimp only [c]
  ring

/-- Deterministic comparison underlying the missing-arm variance argument. -/
lemma guardedTotalCount_center_sq_le (N0 N1 : ℕ) (s : ℝ) :
    (guardedTotalCount N0 N1 - s) ^ 2 ≤
      2 * (((N0 + N1 : ℕ) : ℝ) - s) ^ 2 +
        2 * missingCountSquareEnvelope N0 N1 := by
  by_cases h0 : N0 = 0
  · subst N0
    simp [guardedTotalCount, missingCountSquareEnvelope]
    nlinarith [sq_nonneg (2 * (N1 : ℝ) - s)]
  by_cases h1 : N1 = 0
  · subst N1
    simp [guardedTotalCount, missingCountSquareEnvelope, h0]
    nlinarith [sq_nonneg (2 * (N0 : ℝ) - s)]
  · rw [guardedTotalCount, if_neg (by simp [h0, h1])]
    simp [missingCountSquareEnvelope, h0, h1]
    nlinarith [sq_nonneg (((N0 + N1 : ℕ) : ℝ) - s)]

lemma missingCountSquareEnvelope_nonneg (N0 N1 : ℕ) :
    0 ≤ missingCountSquareEnvelope N0 N1 := by
  unfold missingCountSquareEnvelope
  positivity

/-- Exact product-Poisson second moment on the two missing-arm events. -/
lemma missingCountSquareEnvelope_integral (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ, missingCountSquareEnvelope N0 N1
        ∂poissonMeasure b ∂poissonMeasure a) =
      Real.exp (-(a : ℝ)) * ((b : ℝ) ^ 2 + b) +
        Real.exp (-(b : ℝ)) * ((a : ℝ) ^ 2 + a) := by
  have hsqB := integrable_poisson_count_sq b
  have hsqA := integrable_poisson_count_sq a
  have hinner (N0 : ℕ) :
      (∫ N1 : ℕ, missingCountSquareEnvelope N0 N1 ∂poissonMeasure b) =
        (if N0 = 0 then ((b : ℝ) ^ 2 + b) else 0) +
          (N0 : ℝ) ^ 2 * Real.exp (-(b : ℝ)) := by
    unfold missingCountSquareEnvelope
    have hf : Integrable
        (fun N1 : ℕ => if N0 = 0 then (N1 : ℝ) ^ 2 else 0)
        (poissonMeasure b) := by
      by_cases h0 : N0 = 0
      · simpa [h0] using hsqB
      · simp [h0]
    have hg : Integrable
        (fun N1 : ℕ => if N1 = 0 then (N0 : ℝ) ^ 2 else 0)
        (poissonMeasure b) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
        ((N0 : ℝ) ^ 2)
      filter_upwards with N1
      by_cases h1 : N1 = 0 <;> simp [h1]
    rw [integral_add hf hg, poisson_zero_atom_integral]
    by_cases h0 : N0 = 0
    · subst N0
      simp only [if_pos rfl, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul, add_zero]
      exact poisson_count_second_moment b
    · simp [h0]
  simp_rw [hinner]
  have hzero : (∫ N0 : ℕ,
      if N0 = 0 then ((b : ℝ) ^ 2 + b) else 0 ∂poissonMeasure a) =
      ((b : ℝ) ^ 2 + b) * Real.exp (-(a : ℝ)) :=
    poisson_zero_atom_integral a _
  have hscaled : (∫ N0 : ℕ,
      (N0 : ℝ) ^ 2 * Real.exp (-(b : ℝ)) ∂poissonMeasure a) =
      ((a : ℝ) ^ 2 + a) * Real.exp (-(b : ℝ)) := by
    rw [integral_mul_const, poisson_count_second_moment]
  rw [integral_add]
  · rw [hzero, hscaled]
    ring
  · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
        (((b : ℝ) ^ 2 + b))
    filter_upwards with N0
    by_cases h0 : N0 = 0
    · simp [h0]
      rw [abs_of_nonneg (by positivity : 0 ≤ (b : ℝ) ^ 2 + b)]
    · simp [h0]
      positivity
  · exact hsqA.mul_const _

lemma missingCountSquareEnvelope_rate_le {a b s : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hsum : a + b = s)
    (haL : s / 4 ≤ a) (hbL : s / 4 ≤ b) :
    Real.exp (-a) * (b ^ 2 + b) + Real.exp (-b) * (a ^ 2 + a) ≤
      2 * (s ^ 2 + s) * Real.exp (-s / 4) := by
  have hs0 : 0 ≤ s := by linarith
  have haU : a ≤ s := by linarith
  have hbU : b ≤ s := by linarith
  have hea : Real.exp (-a) ≤ Real.exp (-s / 4) :=
    Real.exp_le_exp.mpr (by linarith)
  have heb : Real.exp (-b) ≤ Real.exp (-s / 4) :=
    Real.exp_le_exp.mpr (by linarith)
  have hac : a ^ 2 + a ≤ s ^ 2 + s := by nlinarith
  have hbc : b ^ 2 + b ≤ s ^ 2 + s := by nlinarith
  have hcoef : 0 ≤ s ^ 2 + s := by positivity
  calc
    _ ≤ Real.exp (-s / 4) * (b ^ 2 + b) +
        Real.exp (-s / 4) * (a ^ 2 + a) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hea (by positivity))
        (mul_le_mul_of_nonneg_right heb (by positivity))
    _ ≤ Real.exp (-s / 4) * (s ^ 2 + s) +
        Real.exp (-s / 4) * (s ^ 2 + s) := by
      gcongr <;> positivity
    _ = _ := by ring

/-- Missing-arm second moment in (39), with the audit normalization. -/
lemma missingCountSquareEnvelope_arm_scaled_le {n : ℕ} (P : Law n)
    (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P) :
    1 / blockMean n ^ 2 *
        (∫ N0 : ℕ, ∫ N1 : ℕ, missingCountSquareEnvelope N0 N1
          ∂poissonMeasure
            (Real.toNNReal (blockMean n * armMass P true k))
          ∂poissonMeasure
            (Real.toNNReal (blockMean n * armMass P false k))) ≤
      2 * (P.cellMass k ^ 2 + P.cellMass k / blockMean n) *
        Real.exp (-blockMean n * P.cellMass k / 4) := by
  let a : ℝ≥0 := Real.toNNReal (blockMean n * armMass P false k)
  let b : ℝ≥0 := Real.toNNReal (blockMean n * armMass P true k)
  let s := blockMean n * P.cellMass k
  have hm := blockMean_pos n hn
  have hp0 := (P.cellMass_range k).1
  have hpi := P.propensity_range k
  have ha0 : 0 ≤ blockMean n * armMass P false k := by
    simp only [armMass, Bool.false_eq_true, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 (sub_nonneg.mpr hpi.2))
  have hb0 : 0 ≤ blockMean n * armMass P true k := by
    simp only [armMass, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 hpi.1)
  have ha : (a : ℝ) = blockMean n * armMass P false k := Real.coe_toNNReal _ ha0
  have hb : (b : ℝ) = blockMean n * armMass P true k := Real.coe_toNNReal _ hb0
  have hsum : (a : ℝ) + b = s := by
    rw [ha, hb]
    simp only [s, armMass, Bool.false_eq_true, ↓reduceIte]
    ring
  by_cases hp : P.cellMass k = 0
  · simp [s, armMass, hp, a, b, missingCountSquareEnvelope_integral]
  · have hp' : 0 < P.cellMass k := lt_of_le_of_ne hp0 (Ne.symm hp)
    obtain ⟨hpiL, hpiU⟩ := hoverlap k hp'
    have haL : s / 4 ≤ (a : ℝ) := by
      rw [ha]
      simp only [s, armMass, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    have hbL : s / 4 ≤ (b : ℝ) := by
      rw [hb]
      simp only [s, armMass, ↓reduceIte]
      nlinarith
    rw [missingCountSquareEnvelope_integral]
    have hr := missingCountSquareEnvelope_rate_le
      (show 0 ≤ (a : ℝ) by positivity) (show 0 ≤ (b : ℝ) by positivity)
      hsum haL hbL
    have hscale : 0 ≤ 1 / blockMean n ^ 2 := by positivity
    calc
      _ ≤ 1 / blockMean n ^ 2 *
          (2 * (s ^ 2 + s) * Real.exp (-s / 4)) :=
        mul_le_mul_of_nonneg_left hr hscale
      _ = _ := by dsimp [s]; field_simp

lemma guardedTotalCount_center_sq_integrable_inner (b : ℝ≥0) (N0 : ℕ) (s : ℝ) :
    Integrable (fun N1 : ℕ => (guardedTotalCount N0 N1 - s) ^ 2)
      (poissonMeasure b) := by
  let g : ℕ → ℝ := fun N1 =>
    2 * (N1 : ℝ) ^ 2 + 2 * ((N0 : ℝ) - s) ^ 2 + s ^ 2
  have hg : Integrable g (poissonMeasure b) := by
    dsimp only [g]
    exact (((integrable_poisson_count_sq b).const_mul 2).add
      (integrable_const _)).add (integrable_const _)
  apply hg.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp only [g]
  by_cases h : N0 = 0 ∨ N1 = 0
  · rw [guardedTotalCount, if_pos h]
    nlinarith [sq_nonneg (N1 : ℝ), sq_nonneg ((N0 : ℝ) - s)]
  · rw [guardedTotalCount, if_neg h]
    norm_num only [Nat.cast_add]
    nlinarith [sq_nonneg ((N1 : ℝ) - ((N0 : ℝ) - s))]

lemma missingCountSquareEnvelope_integrable_inner (b : ℝ≥0) (N0 : ℕ) :
    Integrable (fun N1 : ℕ => missingCountSquareEnvelope N0 N1)
      (poissonMeasure b) := by
  let g : ℕ → ℝ := fun N1 => (N1 : ℝ) ^ 2 + (N0 : ℝ) ^ 2
  have hg : Integrable g (poissonMeasure b) :=
    (integrable_poisson_count_sq b).add (integrable_const _)
  apply hg.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N1
  rw [Real.norm_eq_abs, abs_of_nonneg (missingCountSquareEnvelope_nonneg N0 N1)]
  dsimp only [g]
  unfold missingCountSquareEnvelope
  split_ifs <;> nlinarith [sq_nonneg (N0 : ℝ), sq_nonneg (N1 : ℝ)]

lemma guardedTotalCount_center_sq_inner_integral_le (b : ℝ≥0) (N0 : ℕ) (s : ℝ) :
    (∫ N1 : ℕ, (guardedTotalCount N0 N1 - s) ^ 2 ∂poissonMeasure b) ≤
      2 * ((b : ℝ) ^ 2 + b) + 2 * ((N0 : ℝ) - s) ^ 2 + s ^ 2 := by
  let g : ℕ → ℝ := fun N1 =>
    2 * (N1 : ℝ) ^ 2 + 2 * ((N0 : ℝ) - s) ^ 2 + s ^ 2
  have hg : Integrable g (poissonMeasure b) := by
    dsimp only [g]
    exact (((integrable_poisson_count_sq b).const_mul 2).add
      (integrable_const _)).add (integrable_const _)
  calc
    _ ≤ ∫ N1 : ℕ, g N1 ∂poissonMeasure b := by
      apply integral_mono (guardedTotalCount_center_sq_integrable_inner b N0 s) hg
      intro N1
      dsimp only [g]
      by_cases h : N0 = 0 ∨ N1 = 0
      · rw [guardedTotalCount, if_pos h]
        nlinarith [sq_nonneg (N1 : ℝ), sq_nonneg ((N0 : ℝ) - s)]
      · rw [guardedTotalCount, if_neg h]
        norm_num only [Nat.cast_add]
        nlinarith [sq_nonneg ((N1 : ℝ) - ((N0 : ℝ) - s))]
    _ = _ := by
      dsimp only [g]
      rw [integral_add, integral_add, integral_const_mul,
        poisson_count_second_moment]
      · simp
      · exact (integrable_poisson_count_sq b).const_mul 2
      · exact integrable_const _
      · exact ((integrable_poisson_count_sq b).const_mul 2).add
          (integrable_const _)
      · exact integrable_const _

lemma guardedTotalCount_center_sq_integrable_outer (a b : ℝ≥0) (s : ℝ) :
    Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, (guardedTotalCount N0 N1 - s) ^ 2 ∂poissonMeasure b)
      (poissonMeasure a) := by
  let g : ℕ → ℝ := fun N0 =>
    2 * ((b : ℝ) ^ 2 + b) + 2 * ((N0 : ℝ) - s) ^ 2 + s ^ 2
  have hcenter : Integrable (fun N0 : ℕ => ((N0 : ℝ) - s) ^ 2)
      (poissonMeasure a) := by
    rw [show (fun N0 : ℕ => ((N0 : ℝ) - s) ^ 2) =
        fun (N0 : ℕ) => (N0 : ℝ) ^ 2 + (-2 * s) * (N0 : ℝ) + s ^ 2 by
      funext N0; ring]
    exact ((integrable_poisson_count_sq a).add
      ((poisson_natCast_memLp_two a).integrable (by norm_num) |>.const_mul _)).add
      (integrable_const _)
  have hg : Integrable g (poissonMeasure a) := by
    dsimp only [g]
    exact ((integrable_const _).add (hcenter.const_mul 2)).add (integrable_const _)
  apply hg.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N0
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  exact guardedTotalCount_center_sq_inner_integral_le b N0 s

lemma missingCountSquareEnvelope_integrable_outer (a b : ℝ≥0) :
    Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ, missingCountSquareEnvelope N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
  let g : ℕ → ℝ := fun N0 =>
    ((b : ℝ) ^ 2 + b) + (N0 : ℝ) ^ 2
  have hg : Integrable g (poissonMeasure a) :=
    (integrable_const _).add (integrable_poisson_count_sq a)
  apply hg.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N0
  rw [Real.norm_eq_abs, abs_of_nonneg
    (integral_nonneg (missingCountSquareEnvelope_nonneg N0))]
  calc
    _ ≤ ∫ N1 : ℕ, ((N1 : ℝ) ^ 2 + (N0 : ℝ) ^ 2)
        ∂poissonMeasure b := by
      apply integral_mono (missingCountSquareEnvelope_integrable_inner b N0)
        ((integrable_poisson_count_sq b).add (integrable_const _))
      intro N1
      change missingCountSquareEnvelope N0 N1 ≤
        (N1 : ℝ) ^ 2 + (N0 : ℝ) ^ 2
      unfold missingCountSquareEnvelope
      split_ifs <;> nlinarith [sq_nonneg (N0 : ℝ), sq_nonneg (N1 : ℝ)]
    _ = g N0 := by
      dsimp only [g]
      rw [integral_add (integrable_poisson_count_sq b) (integrable_const _),
        poisson_count_second_moment]
      simp

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperAggregation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Absorbing the logarithmic factors in upper-risk aggregation

The polynomial decay in roadmap equations (31) and (33) absorbs both the
second and fourth powers of the logarithmic alphabet scale. These estimates
are uniform over all nonempty alphabets, without imposing a relation to n. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators


-- @node: logAlphabet_pow_mul_decay_le
/-- Any positive polynomial decay absorbs a fixed positive integer power of L_d. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hk,hδ), the [stated conclusion](goal) holds. -/
lemma logAlphabet_pow_mul_decay_le {d : ℕ} (hd : 1 ≤ d)
    (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
    logAlphabet d ^ k * (d : ℝ) ^ (-δ) ≤
      ((Real.exp 1) ^ (δ / k) / (δ / k)) ^ k := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have he : 0 < δ / k := div_pos hδ hk0
  have h := Real.log_le_rpow_div (x := Real.exp 1 * d) (by positivity) he
  have hpow := pow_le_pow_left₀ (logAlphabet_pos hd).le h k
  change logAlphabet d ^ k ≤ ((Real.exp 1 * d) ^ (δ / k) / (δ / k)) ^ k at hpow
  have hid : ((Real.exp 1 * d) ^ (δ / k) / (δ / k)) ^ k =
      ((Real.exp 1) ^ (δ / k) / (δ / k)) ^ k * (d : ℝ) ^ δ := by
    rw [Real.mul_rpow (Real.exp_pos _).le hd0.le]
    rw [mul_div_right_comm, mul_pow, ← Real.rpow_mul_natCast hd0.le]
    congr 2
    field_simp
  rw [hid] at hpow
  have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd0.le (-δ))
  have hcancel : (d : ℝ) ^ δ * (d : ℝ) ^ (-δ) = 1 := by
    rw [← Real.rpow_add hd0, add_neg_cancel, Real.rpow_zero]
  simpa only [mul_assoc, hcancel, mul_one] using hm


-- @node: logAlphabet_second_fourth_decay_bounded
/-- The two logarithmic ratios in (31) and (33) have one universal envelope for each fixed positive decay exponent. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hδ), the [stated conclusion](goal) holds. -/
lemma logAlphabet_second_fourth_decay_bounded (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 1 ≤ d →
      (logAlphabet d ^ 2 + 8 * logAlphabet d ^ 4) * (d : ℝ) ^ (-δ) ≤ A := by
  let A₂ := ((Real.exp 1) ^ (δ / 2) / (δ / 2)) ^ (2 : ℕ)
  let A₄ := ((Real.exp 1) ^ (δ / 4) / (δ / 4)) ^ (4 : ℕ)
  refine ⟨A₂ + 8 * A₄, by dsimp [A₂, A₄]; positivity, ?_⟩
  intro d hd
  have h₂ := logAlphabet_pow_mul_decay_le hd 2 (by norm_num) δ hδ
  have h₄ := logAlphabet_pow_mul_decay_le hd 4 (by norm_num) δ hδ
  dsimp [A₂, A₄]
  nlinarith


-- @node: activeBranch_pilot_scale_le
/-- On the active branch, the summed pilot second-moment scale is controlled by the logarithmic envelope that appears in (31) and (33). Here a = m ε. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ha,hL,hactive), the [stated conclusion](goal) holds. -/
lemma activeBranch_pilot_scale_le (d a L : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hactive : d ≤ 8 * a * L) :
    L / a + d * L ^ 2 / a ^ 2 ≤ (L ^ 2 + 8 * L ^ 4) / (a * L) := by
  calc
    _ ≤ L / a + (8 * a * L) * L ^ 2 / a ^ 2 := by gcongr
    _ = _ := by field_simp


-- @node: clippingScale_integral_sum_sq_le
/-- Equation (33)'s Cauchy–Schwarz step for the integrated random clipping scales. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hS,hS₂), the [stated conclusion](goal) holds. -/
lemma clippingScale_integral_sum_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Fin d → Ω → ℝ) (hS : ∀ x, Integrable (S x) μ)
    (hS₂ : ∀ x, Integrable (fun z => (S x z) ^ 2) μ) :
    (∑ x : Fin d, ∫ z, S x z ∂μ) ^ 2 ≤
      (d : ℝ) * ∑ x : Fin d, ∫ z, (S x z) ^ 2 ∂μ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun x => ∫ z, S x z ∂μ)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  apply h.trans
  gcongr with x
  have hmem : MemLp (S x) 2 μ :=
    (memLp_two_iff_integrable_sq (hS x).aestronglyMeasurable).2 (hS₂ x)
  have hv := ProbabilityTheory.variance_eq_sub hmem
  have hn := ProbabilityTheory.variance_nonneg (X := S x) (μ := μ)
  simp only [Pi.pow_apply] at hv
  linarith


-- @node: activeBranch_pilot_moment_sum_rate_le
/-- Equations (31) and (33): the pilot moment sum, multiplied by any fixed sublinear alphabet power, is at most a universal constant times R = d/(m ε L). The premise is the cellwise pilot estimate (19), rather than a risk bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hδ), the [stated conclusion](goal) holds. -/
lemma activeBranch_pilot_moment_sum_rate_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ {d : ℕ}, 1 ≤ d → ∀ (P : DiscreteLaw d)
      (v : Fin d → ℝ) (C a : ℝ), 0 ≤ C → 0 < a →
      (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, v x ≤ C * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (d : ℝ) ^ (1 - δ) * (∑ x : Fin d, v x) ≤
        C * A * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨A, hA, hlog⟩ := logAlphabet_second_fourth_decay_bounded δ hδ
  refine ⟨A, hA, ?_⟩
  intro d hd P v C a hC ha hactive hv
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hL := logAlphabet_pos hd
  have hsum := clippingScale_secondMoment_sum_le P v C (logAlphabet d) a 1 (by
    intro x
    simpa using hv x)
  simp only [mul_one, one_pow] at hsum
  have hid : (d : ℝ) ^ (1 - δ) = (d : ℝ) * (d : ℝ) ^ (-δ) := by
    rw [sub_eq_add_neg, Real.rpow_add hd0, Real.rpow_one]
  calc
    _ ≤ (d : ℝ) ^ (1 - δ) *
        (C * (logAlphabet d / a + (d : ℝ) * logAlphabet d ^ 2 / a ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hd0.le _)
    _ ≤ (d : ℝ) ^ (1 - δ) *
        (C * ((logAlphabet d ^ 2 + 8 * logAlphabet d ^ 4) / (a * logAlphabet d))) := by
      gcongr
      exact activeBranch_pilot_scale_le d a (logAlphabet d) ha hL hactive
    _ = C * ((logAlphabet d ^ 2 + 8 * logAlphabet d ^ 4) * (d : ℝ) ^ (-δ)) *
        ((d : ℝ) / (a * logAlphabet d)) := by rw [hid]; ring
    _ ≤ C * A * ((d : ℝ) / (a * logAlphabet d)) := by
      gcongr
      exact hlog d hd


-- @node: activeBranch_clipping_bias_rate_le
/-- Equation (33), including its final absorption into R, for actual integrated clipping scales. The second-moment premise is exactly the pilot estimate (19). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma activeBranch_clipping_bias_rate_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (S : Fin d → Ω → ℝ) (C a : ℝ),
      0 ≤ C → 0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun z => (S x z) ^ 2) μ) →
      (∀ x, (∫ z, (S x z) ^ 2 ∂μ) ≤
        C * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (d : ℝ) ^ (-(3 / 8 : ℝ)) * (∑ x : Fin d, ∫ z, S x z ∂μ) ^ 2 ≤
        C * A * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨A, hA, hrate⟩ := activeBranch_pilot_moment_sum_rate_le (3 / 8) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro Ω _ μ _ d hd P S C a hC ha hactive hS hS₂ hv
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  calc
    _ ≤ (d : ℝ) ^ (-(3 / 8 : ℝ)) *
        ((d : ℝ) * ∑ x : Fin d, ∫ z, (S x z) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (clippingScale_integral_sum_sq_le μ S hS hS₂)
        (Real.rpow_nonneg hd0.le _)
    _ = (d : ℝ) ^ (1 - (3 / 8 : ℝ)) *
        (∑ x : Fin d, ∫ z, (S x z) ^ 2 ∂μ) := by
      rw [sub_eq_add_neg, Real.rpow_add hd0, Real.rpow_one]
      ring
    _ ≤ _ := hrate hd P (fun x => ∫ z, (S x z) ^ 2 ∂μ) C a hC ha hactive hv


-- @node: activeBranch_variance_scale_rate_le
/-- Equation (31) with the variance inflation d^(1/16) used by the factorial lift. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma activeBranch_variance_scale_rate_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {d : ℕ}, 1 ≤ d → ∀ (P : DiscreteLaw d)
      (v : Fin d → ℝ) (C a : ℝ), 0 ≤ C → 0 < a →
      (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, v x ≤ C * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (d : ℝ) ^ (1 / 16 : ℝ) * (∑ x : Fin d, v x) ≤
        C * A * ((d : ℝ) / (a * logAlphabet d)) := by
  convert activeBranch_pilot_moment_sum_rate_le (15 / 16) (by norm_num) using 1
  norm_num

end CausalSmith.Stat.OptvalueVanishingoverlapRate

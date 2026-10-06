module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevCoefficients
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrectionsBase

/-!
# Pointwise light-correction second-moment bounds

Descending factorials and the coefficient budget bound the light correction
by a count-power envelope. The square envelope holds almost surely for the
actual fourth-stream statistic, providing the integrand bound for equation (8).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open scoped BigOperators

-- @node: lightCorrection_abs_le_coeff_sum
/-- A centered success count bounded by its containing count yields a
coefficient-sum bound for the light correction. Given [the specified input `n`](hyp:n), [the specified input `C`](hyp:C), [the specified input `U`](hyp:U), [the specified input `hC`](hyp:hC), [the specified input `hU0`](hyp:hU0), [the specified input `hUC`](hyp:hUC), [the stated mathematical conclusion holds](goal). -/
lemma lightCorrection_abs_le_coeff_sum (n : ℕ) {C U : ℝ}
    (hC : 0 ≤ C) (hU0 : 0 ≤ U) (hUC : U ≤ C) :
    |lightCorrection n C U| ≤
      C / 2 *
        (∑ t ∈ Finset.range (polyDegree n - 1),
          (|correctionCoeff n (t + 1)| *
            |shiftedFalling C (t + 1)|)) := by
  have hcenter : |U - C / 2| ≤ C / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |lightCorrection n C U| ≤
        ∑ t ∈ Finset.range (polyDegree n - 1),
          |correctionCoeff n (t + 1) * (U - C / 2) *
            shiftedFalling C (t + 1)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (polyDegree n - 1),
        C / 2 * (|correctionCoeff n (t + 1)| *
          |shiftedFalling C (t + 1)|) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul, abs_mul]
      calc
        _ = |U - C / 2| * (|correctionCoeff n (t + 1)| *
            |shiftedFalling C (t + 1)|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcenter
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

-- @node: lightCorrection_sq_le_coeff_sum_sq
/-- Squaring the coefficient-sum bound controls a single light correction's
second-moment integrand. Given [the specified input `n`](hyp:n), [the specified input `C`](hyp:C), [the specified input `U`](hyp:U), [the specified input `hC`](hyp:hC), [the specified input `hU0`](hyp:hU0), [the specified input `hUC`](hyp:hUC), [the stated mathematical conclusion holds](goal). -/
lemma lightCorrection_sq_le_coeff_sum_sq (n : ℕ) {C U : ℝ}
    (hC : 0 ≤ C) (hU0 : 0 ≤ U) (hUC : U ≤ C) :
    (lightCorrection n C U) ^ 2 ≤
      (C / 2 *
        (∑ t ∈ Finset.range (polyDegree n - 1),
          (|correctionCoeff n (t + 1)| *
            |shiftedFalling C (t + 1)|))) ^ 2 := by
  have habs := lightCorrection_abs_le_coeff_sum n hC hU0 hUC
  exact sq_le_sq.mpr (habs.trans (le_abs_self _))

/-- A centered success count times the shifted product is at most half the
count's descending factorial, including the zero-count case. Given [the specified input `k`](hyp:k), [the specified input `v`](hyp:v), [the specified input `hv`](hyp:hv), [the specified input `U`](hyp:U), [the specified input `hU0`](hyp:hU0), [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). Given [the specified input `hUk`](hyp:hUk). -/
-- @node: upper_centered_shiftedFalling_abs_le
lemma upper_centered_shiftedFalling_abs_le (k v : ℕ) (hv : 1 ≤ v)
    {U : ℝ} (hU0 : 0 ≤ U) (hUk : U ≤ (k : ℝ)) :
    |(U - (k : ℝ) / 2) * shiftedFalling (k : ℝ) v| ≤
      (k.descFactorial v : ℝ) / 2 := by
  have hc : |U - (k : ℝ) / 2| ≤ (k : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    _ = |U - (k : ℝ) / 2| * |shiftedFalling (k : ℝ) v| := abs_mul _ _
    _ ≤ ((k : ℝ) / 2) * |shiftedFalling (k : ℝ) v| :=
      mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = |(k : ℝ) * shiftedFalling (k : ℝ) v| / 2 := by
      rw [abs_mul]
      simp only [abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
      ring
    _ = (k.descFactorial v : ℝ) / 2 := by
      rw [upper_shiftedFalling_descFactorial k v hv,
        abs_of_nonneg (Nat.cast_nonneg _)]

/-- The light correction is bounded by half its absolute-coefficient-weighted
sum of descending factorials. Given [the specified input `n`](hyp:n), [the specified input `k`](hyp:k), [the specified input `U`](hyp:U), [the specified input `hU0`](hyp:hU0), [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). Given [the specified input `hUk`](hyp:hUk). -/
-- @node: upper_lightCorrection_abs_le_factorial_sum
lemma upper_lightCorrection_abs_le_factorial_sum (n k : ℕ)
    {U : ℝ} (hU0 : 0 ≤ U) (hUk : U ≤ (k : ℝ)) :
    |lightCorrection n (k : ℝ) U| ≤
      (∑ t ∈ Finset.range (polyDegree n - 1),
        |correctionCoeff n (t + 1)| * (k.descFactorial (t + 1) : ℝ)) / 2 := by
  unfold lightCorrection
  calc
    _ ≤ ∑ t ∈ Finset.range (polyDegree n - 1),
        |correctionCoeff n (t + 1) * (U - (k : ℝ) / 2) *
          shiftedFalling (k : ℝ) (t + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (polyDegree n - 1),
        |correctionCoeff n (t + 1)| * (k.descFactorial (t + 1) : ℝ) / 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [mul_assoc, abs_mul]
      have hb := upper_centered_shiftedFalling_abs_le k (t + 1)
        (by omega) hU0 hUk
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [Finset.sum_div]

/-- Bounding descending factorials by powers gives the count-power envelope
used before taking Poisson moments in equation (8). Given [the specified input `n`](hyp:n), [the specified input `k`](hyp:k), [the specified input `U`](hyp:U), [the specified input `hU0`](hyp:hU0), [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). Given [the specified input `hUk`](hyp:hUk). -/
-- @node: upper_lightCorrection_abs_le_power_sum
lemma upper_lightCorrection_abs_le_power_sum (n k : ℕ)
    {U : ℝ} (hU0 : 0 ≤ U) (hUk : U ≤ (k : ℝ)) :
    |lightCorrection n (k : ℝ) U| ≤
      (∑ t ∈ Finset.range (polyDegree n - 1),
        |correctionCoeff n (t + 1)| * (k : ℝ) ^ (t + 1)) / 2 := by
  apply (upper_lightCorrection_abs_le_factorial_sum n k hU0 hUk).trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact_mod_cast Nat.descFactorial_le_pow k (t + 1)

/-- Powers below a fixed degree are bounded by the larger of one and the
highest power of a nonnegative ratio. Given [the specified input `r`](hyp:r), [the specified input `hr`](hyp:hr), [the specified input `v`](hyp:v), [the specified input `K`](hyp:K), [the specified input `hv`](hyp:hv), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_power_ratio_envelope
lemma upper_power_ratio_envelope {r : ℝ} (hr : 0 ≤ r) {v K : ℕ} (hv : v ≤ K) :
    r ^ v ≤ max 1 (r ^ K) := by
  by_cases hr1 : r ≤ 1
  · exact (pow_le_one₀ hr hr1).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ (le_of_not_ge hr1) hv).trans (le_max_right _ _)

/-- The coefficient budget turns the light correction into a single
count-to-threshold power envelope with exponential degree factor. Given [the specified input `n`](hyp:n), [the specified input `k`](hyp:k), [the specified input `U`](hyp:U), [the specified input `hU0`](hyp:hU0), [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). Given [the specified input `hUk`](hyp:hUk). -/
-- @node: upper_lightCorrection_abs_le_degree_envelope
lemma upper_lightCorrection_abs_le_degree_envelope (n k : ℕ)
    {U : ℝ} (hU0 : 0 ≤ U) (hUk : U ≤ (k : ℝ)) :
    |lightCorrection n (k : ℝ) U| ≤
      (8 : ℝ) ^ polyDegree n / 2 *
        max 1 (((k : ℝ) / polyThreshold n) ^ polyDegree n) := by
  have hB : 0 < polyThreshold n := by
    have he : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have he1 := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hL : 0 < ell n := Real.log_pos (by simpa [ell] using he)
    unfold polyThreshold
    positivity
  let M := max 1 (((k : ℝ) / polyThreshold n) ^ polyDegree n)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hs : (∑ t ∈ Finset.range (polyDegree n - 1),
      |correctionCoeff n (t + 1)| * (k : ℝ) ^ (t + 1)) ≤
      (∑ t ∈ Finset.range (polyDegree n - 1),
        |correctionCoeff n (t + 1)| * polyThreshold n ^ (t + 1)) * M := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    have htK : t + 1 ≤ polyDegree n := by
      have := Finset.mem_range.mp ht
      omega
    have hp := upper_power_ratio_envelope
      (div_nonneg (Nat.cast_nonneg k) hB.le) htK
    calc
      _ = (|correctionCoeff n (t + 1)| * polyThreshold n ^ (t + 1)) *
          (((k : ℝ) / polyThreshold n) ^ (t + 1)) := by
        rw [div_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hb := mul_le_mul_of_nonneg_right (correctionCoeff_weighted_sum_le n) hM
  calc
    _ ≤ _ := upper_lightCorrection_abs_le_power_sum n k hU0 hUk
    _ ≤ ((8 : ℝ) ^ polyDegree n * M) / 2 := by linarith [hs.trans hb]
    _ = _ := by dsimp [M]; ring


/-- Squaring the count-power envelope produces the exponential-degree and
power-growth factors of the light second-moment bound. Given [the specified input `n`](hyp:n), [the specified input `k`](hyp:k), [the specified input `U`](hyp:U), [the specified input `hU0`](hyp:hU0), [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). Given [the specified input `hUk`](hyp:hUk). -/
-- @node: upper_lightCorrection_sq_le_degree_envelope
lemma upper_lightCorrection_sq_le_degree_envelope (n k : ℕ)
    {U : ℝ} (hU0 : 0 ≤ U) (hUk : U ≤ (k : ℝ)) :
    (lightCorrection n (k : ℝ) U) ^ 2 ≤
      (64 : ℝ) ^ polyDegree n / 4 *
        max 1 (((k : ℝ) / polyThreshold n) ^ (2 * polyDegree n)) := by
  have hb := upper_lightCorrection_abs_le_degree_envelope n k hU0 hUk
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hs
  have hm : (max 1 (((k : ℝ) / polyThreshold n) ^ polyDegree n)) ^ 2 =
      max 1 (((k : ℝ) / polyThreshold n) ^ (2 * polyDegree n)) := by
    let r := ((k : ℝ) / polyThreshold n) ^ polyDegree n
    have hr : 0 ≤ r := by
      dsimp [r]
      apply pow_nonneg
      apply div_nonneg (Nat.cast_nonneg k)
      have he : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
        have he1 := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hL : 0 < ell n := Real.log_pos (by simpa [ell] using he)
      unfold polyThreshold
      positivity
    rw [show 2 * polyDegree n = polyDegree n * 2 by omega, pow_mul]
    change (max 1 r) ^ 2 = max 1 (r ^ 2)
    by_cases h : 1 ≤ r
    · rw [max_eq_right h, max_eq_right (by nlinarith)]
    · rw [max_eq_left (le_of_not_ge h), max_eq_left (by nlinarith)]
      norm_num
  have hc : ((8 : ℝ) ^ polyDegree n / 2) ^ 2 =
      (64 : ℝ) ^ polyDegree n / 4 := by
    rw [div_pow, ← pow_mul, Nat.mul_comm (polyDegree n) 2, pow_mul]
    norm_num
  simpa only [mul_pow, hm, hc] using hs

/-- Almost surely the arrived count is a natural number and the success count
lies between zero and that count. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_count_support_ae
lemma upper_stream_count_support_ae {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    ∀ᵐ streams ∂fourStreamLaw n P, ∃ k : ℕ,
      streamC d streams x a s = (k : ℝ) ∧
      0 ≤ streamU d streams x a s ∧
      streamU d streams x a s ≤ (k : ℝ) := by
  classical
  filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
  let z := streams 3
  let C := Finset.univ.filter (fun i : Fin z.count =>
    inCell (z.points i) x a s ∧ (z.points i).R = true)
  let U := Finset.univ.filter (fun i : Fin z.count =>
    inCell (z.points i) x a s ∧ (z.points i).R = true ∧ (z.points i).RY = true)
  have hC : streamC d streams x a s = (C.card : ℝ) :=
    upper_finiteStreamCount_eq_eventCount z _
  have hU : streamU d streams x a s = (U.card : ℝ) := by
    rw [hs]
    exact upper_finiteStreamCount_eq_eventCount z _
  refine ⟨C.card, hC, ?_, ?_⟩
  · rw [hU]
    positivity
  · rw [hU]
    exact_mod_cast (Finset.card_le_card (show U ⊆ C from by
      intro i hi
      simp only [U, C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hi.1, hi.2.1⟩))

/-- The actual light-stream statistic obeys the count-power square envelope
almost surely under the ideal experiment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_sq_le_degree_envelope_ae
lemma upper_streamH_sq_le_degree_envelope_ae {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    ∀ᵐ streams ∂fourStreamLaw n P,
      (streamH n d streams x a s) ^ 2 ≤
        (64 : ℝ) ^ polyDegree n / 4 *
          max 1 ((streamC d streams x a s / polyThreshold n) ^
            (2 * polyDegree n)) := by
  filter_upwards [upper_stream_count_support_ae (n := n) P x a s] with streams hs
  obtain ⟨k, hk, hU0, hUk⟩ := hs
  simpa only [streamH, hk] using
    upper_lightCorrection_sq_le_degree_envelope n k hU0 hUk

end CausalSmith.Stat.MarNearcompleteFrontier

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Variation

/-!
# Reciprocal frequency weights and weighted variation

The sign parameter is either `1` or `-1`. Bounds are asserted only on the
frequency window that can meet the zero-extended Jackson coefficients and
their second differences.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open scoped BigOperators

/-- The [shifted reciprocal square](goal) of [order N](hyp:N) with [orientation σ](hyp:σ) at [an
integer frequency j](hyp:j) is [one divided by the square of 4N + σ j](step:1), read as zero when
the denominator vanishes; the orientation is meant to be plus or minus one. -/
noncomputable def reciprocalSquare (N : ℕ) (σ : ℝ) (j : ℤ) : ℝ :=
  1 / (4 * (N : ℝ) + σ * (j : ℝ)) ^ 2

/-- The [reciprocal-weighted Jackson coefficient](goal) of [order N](hyp:N) with [orientation
σ](hyp:σ) at [an integer frequency j](hyp:j) is [the normalized Jackson coefficient at j times the
shifted reciprocal square at j](step:1). -/
noncomputable def weightedCoeff (N : ℕ) (σ : ℝ) (j : ℤ) : ℝ :=
  normalizedCoeff N j * reciprocalSquare N σ j

private theorem reciprocalSquare_window (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (j : ℤ) (hj : |j| ≤ (2 * N : ℕ)) :
    (N : ℝ) ≤ 4 * (N : ℝ) + σ * (j : ℝ) ∧
    (N : ℝ) ≤ 4 * (N : ℝ) + σ * ((j + 1 : ℤ) : ℝ) ∧
    (N : ℝ) ≤ 4 * (N : ℝ) + σ * ((j + 2 : ℤ) : ℝ) := by
  have hjloZ : -((2 * N : ℕ) : ℤ) ≤ j := (abs_le.mp hj).1
  have hjhiZ : j ≤ ((2 * N : ℕ) : ℤ) := (abs_le.mp hj).2
  have hjlo : -(2 * (N : ℝ)) ≤ (j : ℝ) := by exact_mod_cast hjloZ
  have hjhi : (j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hjhiZ
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rcases hσ with hσ | hσ
  · rw [hσ]
    push_cast
    constructor
    · nlinarith
    constructor <;> nlinarith
  · rw [hσ]
    push_cast
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- For [an order N](hyp:N) that is [at least two](hyp:hN), [an orientation σ](hyp:σ) [equal to
plus or minus one](hyp:hσ), and [an integer frequency j](hyp:j) [of absolute value at most
2N](hyp:hj), [the shifted reciprocal square is at most 1 / N² in absolute value](goal). -/
theorem reciprocalSquare_bound (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (j : ℤ) (hj : |j| ≤ (2 * N : ℕ)) :
    |reciprocalSquare N σ j| ≤ 1 / (N : ℝ) ^ 2 := by
  have ha := (reciprocalSquare_window N hN σ hσ j hj).1
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  rw [reciprocalSquare, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- For [an order N](hyp:N) that is [at least two](hyp:hN), [an orientation σ](hyp:σ) [equal to
plus or minus one](hyp:hσ), and [an integer frequency j](hyp:j) [of absolute value at most
2N](hyp:hj), [the forward first difference of the shifted reciprocal square at j is at most 16 / N³
in absolute value](goal). -/
theorem reciprocalSquare_delta_bound (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (j : ℤ) (hj : |j| ≤ (2 * N : ℕ)) :
    |delta (reciprocalSquare N σ) j| ≤ 16 / (N : ℝ) ^ 3 := by
  let a : ℝ := 4 * (N : ℝ) + σ * (j : ℝ)
  let b : ℝ := 4 * (N : ℝ) + σ * ((j + 1 : ℤ) : ℝ)
  obtain ⟨ha, hb, _⟩ := reciprocalSquare_window N hN σ hσ j hj
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have ha0 : 0 < a := lt_of_lt_of_le hn ha
  have hb0 : 0 < b := lt_of_lt_of_le hn hb
  have hrel : b - a = σ := by dsimp [a, b]; push_cast; ring
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hab : |a - b| = 1 := by
    have : a - b = -σ := by linarith
    rw [this, abs_neg, hσabs]
  have hfactor : 1 / b ^ 2 - 1 / a ^ 2 =
      (a - b) * (1 / a * (1 / b ^ 2) + 1 / a ^ 2 * (1 / b)) := by
    field_simp
    ring
  have hq : |delta (reciprocalSquare N σ) j| =
      1 / a * (1 / b ^ 2) + 1 / a ^ 2 * (1 / b) := by
    change |1 / b ^ 2 - 1 / a ^ 2| = _
    rw [hfactor, abs_mul, hab, one_mul, abs_of_nonneg (by positivity)]
  have hia : 1 / a ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hn ha
  have hib : 1 / b ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hn hb
  have hi2a : 1 / a ^ 2 ≤ 1 / (N : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hi2b : 1 / b ^ 2 ≤ 1 / (N : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  rw [hq]
  calc
    1 / a * (1 / b ^ 2) + 1 / a ^ 2 * (1 / b) ≤
        1 / (N : ℝ) * (1 / (N : ℝ) ^ 2) +
        1 / (N : ℝ) ^ 2 * (1 / (N : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul hia hi2b (by positivity) (by positivity)
      · exact mul_le_mul hi2a hib (by positivity) (by positivity)
    _ = 2 / (N : ℝ) ^ 3 := by field_simp; ring
    _ ≤ 16 / (N : ℝ) ^ 3 := by apply div_le_div_of_nonneg_right (by norm_num); positivity

/-- For [an order N](hyp:N) that is [at least two](hyp:hN), [an orientation σ](hyp:σ) [equal to
plus or minus one](hyp:hσ), and [an integer frequency j](hyp:j) [of absolute value at most
2N](hyp:hj), [the forward second difference of the shifted reciprocal square at j is at most 64 /
N⁴ in absolute value](goal). -/
theorem reciprocalSquare_delta2_bound (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (j : ℤ) (hj : |j| ≤ (2 * N : ℕ)) :
    |delta2 (reciprocalSquare N σ) j| ≤ 64 / (N : ℝ) ^ 4 := by
  let a : ℝ := 4 * (N : ℝ) + σ * (j : ℝ)
  let b : ℝ := 4 * (N : ℝ) + σ * ((j + 1 : ℤ) : ℝ)
  let c : ℝ := 4 * (N : ℝ) + σ * ((j + 2 : ℤ) : ℝ)
  obtain ⟨ha, hb, hc⟩ := reciprocalSquare_window N hN σ hσ j hj
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have ha0 : 0 < a := lt_of_lt_of_le hn ha
  have hb0 : 0 < b := lt_of_lt_of_le hn hb
  have hc0 : 0 < c := lt_of_lt_of_le hn hc
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnum : 0 ≤ 3 * b ^ 2 - 1 := by nlinarith
  have hdelta : delta2 (reciprocalSquare N σ) j =
      1 / c ^ 2 - 2 * (1 / b ^ 2) + 1 / a ^ 2 := by
    simp only [delta2, delta, reciprocalSquare]
    have hjj : j + 1 + 1 = j + 2 := by omega
    rw [hjj]
    change (1 / c ^ 2 - 1 / b ^ 2) - (1 / b ^ 2 - 1 / a ^ 2) = _
    ring
  have hid : 1 / c ^ 2 - 2 * (1 / b ^ 2) + 1 / a ^ 2 =
      2 * (3 * b ^ 2 - 1) / (a ^ 2 * b ^ 2 * c ^ 2) := by
    field_simp
    rcases hσ with hσ | hσ
    · subst σ
      dsimp [a, b, c]
      push_cast
      ring
    · subst σ
      dsimp [a, b, c]
      push_cast
      ring
  rw [hdelta, hid, abs_of_nonneg (by positivity)]
  calc
    2 * (3 * b ^ 2 - 1) / (a ^ 2 * b ^ 2 * c ^ 2) ≤
        6 * b ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
      apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ = 6 / (a ^ 2 * c ^ 2) := by field_simp
    _ ≤ 6 / ((N : ℝ) ^ 2 * (N : ℝ) ^ 2) := by gcongr
    _ = 6 / (N : ℝ) ^ 4 := by ring
    _ ≤ 64 / (N : ℝ) ^ 4 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- For [any two real sequences f and q indexed by the integers](hyp:f,q) and [any index j](hyp:j),
[the forward second difference of their product at j equals f at j + 2 times the second difference
of q at j, plus the sum of the first differences of f at j + 1 and at j times the first difference
of q at j, plus q at j + 1 times the second difference of f at j](goal). -/
theorem delta2_mul (f q : ℤ → ℝ) (j : ℤ) :
    delta2 (fun k => f k * q k) j =
      f (j + 2) * delta2 q j +
      (delta f (j + 1) + delta f j) * delta q j +
      q (j + 1) * delta2 f j := by
  simp only [delta2, delta]
  ring

/-- For [any order N](hyp:N), [any orientation σ](hyp:σ), and [an integer frequency j](hyp:j)
[whose absolute value exceeds 2N − 2](hyp:hj), [the reciprocal-weighted Jackson coefficient is
zero](goal), including at frequencies where the reciprocal's denominator vanishes. -/
theorem weightedCoeff_support (N : ℕ) (σ : ℝ) (j : ℤ)
    (hj : ((2 * N - 2 : ℕ) : ℤ) < |j|) : weightedCoeff N σ j = 0 := by
  simp [weightedCoeff, normalizedCoeff_support N j hj]

/-- For [an order N](hyp:N) that is [at least two](hyp:hN) and [an orientation σ](hyp:σ) [equal to
plus or minus one](hyp:hσ), [the sum over all integers of the absolute second differences of the
reciprocal-weighted Jackson coefficients is at most 512 / N³](goal). -/
theorem weightedCoeff_delta2_l1 (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    (∑' j : ℤ, |delta2 (weightedCoeff N σ) j|) ≤ 512 / (N : ℝ) ^ 3 := by
  let S : Finset ℤ := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))
  let f : ℤ → ℝ := normalizedCoeff N
  let q : ℤ → ℝ := reciprocalSquare N σ
  have hzero (j : ℤ) (hj : j ∉ S) (m : ℤ) (hm : 0 ≤ m ∧ m ≤ 2) :
      f (j + m) = 0 := by
    apply normalizedCoeff_support N
    simp only [S, Finset.mem_Icc, not_and_or, not_le] at hj
    rcases hj with hj | hj
    · rw [abs_of_nonpos (by omega : j + m ≤ 0)]
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤ j + m)]
      omega
  have hzero_delta2 (j : ℤ) (hj : j ∉ S) :
      delta2 (weightedCoeff N σ) j = 0 := by
    have h0 : f j = 0 := by simpa using hzero j hj 0 ⟨by omega, by omega⟩
    have h1 := hzero j hj 1 ⟨by omega, by omega⟩
    have h2 := hzero j hj 2 ⟨by omega, by omega⟩
    have hw0 : weightedCoeff N σ j = 0 := by change f j * q j = 0; simp [h0]
    have hw1 : weightedCoeff N σ (j + 1) = 0 := by
      change f (j + 1) * q (j + 1) = 0
      simp [h1]
    have hw2 : weightedCoeff N σ (j + 2) = 0 := by
      change f (j + 2) * q (j + 2) = 0
      simp [h2]
    simp [delta2, delta, hw0, hw1, hw2,
      show j + 1 + 1 = j + 2 by omega]
  have hs : Summable (fun j : ℤ => |delta2 (weightedCoeff N σ) j|) :=
    summable_of_ne_finset_zero (s := S) (by intro j hj; simp [hzero_delta2 j hj])
  have hf0 : Summable (fun j : ℤ => |f (j + 2)|) :=
    summable_of_ne_finset_zero (s := S) (by
      intro j hj
      simp [hzero j hj 2 ⟨by omega, by omega⟩])
  have hf1 : Summable (fun j : ℤ => |delta f (j + 1)|) :=
    summable_of_ne_finset_zero (s := S) (by
      intro j hj
      have h1 := hzero j hj 1 ⟨by omega, by omega⟩
      have h2 := hzero j hj 2 ⟨by omega, by omega⟩
      simp [delta, h1, h2, show j + 1 + 1 = j + 2 by omega])
  have hf2 : Summable (fun j : ℤ => |delta f j|) :=
    summable_of_ne_finset_zero (s := S) (by
      intro j hj
      have h0 : f j = 0 := by simpa using hzero j hj 0 ⟨by omega, by omega⟩
      have h1 := hzero j hj 1 ⟨by omega, by omega⟩
      simp [delta, h0, h1])
  have hf3 : Summable (fun j : ℤ => |delta2 f j|) :=
    summable_of_ne_finset_zero (s := S) (by
      intro j hj
      have h0 : f j = 0 := by simpa using hzero j hj 0 ⟨by omega, by omega⟩
      have h1 := hzero j hj 1 ⟨by omega, by omega⟩
      have h2 := hzero j hj 2 ⟨by omega, by omega⟩
      simp [delta2, delta, h0, h1, h2,
        show j + 1 + 1 = j + 2 by omega])
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have hpoint (j : ℤ) :
      |delta2 (weightedCoeff N σ) j| ≤
        (64 / (N : ℝ) ^ 4) * |f (j + 2)| +
        (16 / (N : ℝ) ^ 3) * |delta f (j + 1)| +
        (16 / (N : ℝ) ^ 3) * |delta f j| +
        (1 / (N : ℝ) ^ 2) * |delta2 f j| := by
    by_cases hj : j ∈ S
    · have hjabs : |j| ≤ ((2 * N : ℕ) : ℤ) := by
        simp only [S, Finset.mem_Icc] at hj
        rcases hj with ⟨hlo, hhi⟩
        exact abs_le.mpr ⟨by omega, by omega⟩
      have hq0 := reciprocalSquare_delta2_bound N hN σ hσ j hjabs
      have hq1 := reciprocalSquare_delta_bound N hN σ hσ j hjabs
      have hq2 : |q (j + 1)| ≤ 1 / (N : ℝ) ^ 2 := by
        have hwin := (reciprocalSquare_window N hN σ hσ j hjabs).2.1
        dsimp [q, reciprocalSquare]
        rw [abs_of_nonneg (by positivity)]
        apply one_div_le_one_div_of_le (by positivity)
        gcongr
      rw [show weightedCoeff N σ = fun k => f k * q k by rfl,
        delta2_mul f q j]
      calc
        |f (j + 2) * delta2 q j +
          (delta f (j + 1) + delta f j) * delta q j +
          q (j + 1) * delta2 f j| ≤
          |f (j + 2)| * |delta2 q j| +
          (|delta f (j + 1)| + |delta f j|) * |delta q j| +
          |q (j + 1)| * |delta2 f j| := by
            calc
              _ ≤ |f (j + 2) * delta2 q j| +
                  |(delta f (j + 1) + delta f j) * delta q j| +
                  |q (j + 1) * delta2 f j| := by
                    simpa only [add_assoc] using
                      (abs_add_three (f (j + 2) * delta2 q j)
                        ((delta f (j + 1) + delta f j) * delta q j)
                        (q (j + 1) * delta2 f j))
              _ ≤ _ := by
                simp only [abs_mul]
                gcongr
                exact abs_add_le _ _
        _ ≤ _ := by
          change |delta2 q j| ≤ _ at hq0
          change |delta q j| ≤ _ at hq1
          nlinarith [mul_le_mul_of_nonneg_left hq0 (abs_nonneg (f (j + 2))),
            mul_le_mul_of_nonneg_left hq1 (abs_nonneg (delta f (j + 1))),
            mul_le_mul_of_nonneg_left hq1 (abs_nonneg (delta f j)),
            mul_le_mul_of_nonneg_left hq2 (abs_nonneg (delta2 f j))]
    · have h0 : f j = 0 := by simpa using hzero j hj 0 ⟨by omega, by omega⟩
      have h1 := hzero j hj 1 ⟨by omega, by omega⟩
      have h2 := hzero j hj 2 ⟨by omega, by omega⟩
      rw [hzero_delta2 j hj]
      simp [delta2, delta, h0, h1, h2,
        show j + 1 + 1 = j + 2 by omega]
  have hrhs : Summable (fun j : ℤ =>
      (64 / (N : ℝ) ^ 4) * |f (j + 2)| +
      (16 / (N : ℝ) ^ 3) * |delta f (j + 1)| +
      (16 / (N : ℝ) ^ 3) * |delta f j| +
      (1 / (N : ℝ) ^ 2) * |delta2 f j|) := by
    exact (((hf0.mul_left _).add (hf1.mul_left _)).add (hf2.mul_left _)).add
      (hf3.mul_left _)
  have hmain := hs.tsum_le_tsum hpoint hrhs
  rw [(((hf0.mul_left _).add (hf1.mul_left _)).add (hf2.mul_left _)).tsum_add
      (hf3.mul_left _),
    ((hf0.mul_left _).add (hf1.mul_left _)).tsum_add (hf2.mul_left _),
    (hf0.mul_left _).tsum_add (hf1.mul_left _)] at hmain
  simp only [tsum_mul_left] at hmain
  have hshift0 : (∑' j : ℤ, |f (j + 2)|) = ∑' j : ℤ, |f j| := by
    simpa [Equiv.addRight] using
      (Equiv.tsum_eq (Equiv.addRight (2 : ℤ)) (fun j : ℤ => |f j|))
  have hshift1 : (∑' j : ℤ, |delta f (j + 1)|) =
      ∑' j : ℤ, |delta f j| := by
    simpa [Equiv.addRight] using
      (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun j : ℤ => |delta f j|))
  rw [hshift0, hshift1] at hmain
  have hNpos : 0 < N := by omega
  have hm0 := normalizedCoeff_l1 N hNpos
  have hm1 := normalizedCoeff_delta_l1 N hNpos
  have hm2 := normalizedCoeff_delta2_l1 N hNpos
  dsimp [f] at hmain
  calc
    (∑' j : ℤ, |delta2 (weightedCoeff N σ) j|) ≤
        (64 / (N : ℝ) ^ 4) * (2 * N) +
        (16 / (N : ℝ) ^ 3) * 4 +
        (16 / (N : ℝ) ^ 3) * 4 +
        (1 / (N : ℝ) ^ 2) * (6 / N) := by
      exact hmain.trans (by gcongr)
    _ ≤ 512 / (N : ℝ) ^ 3 := by
      have : (N : ℝ) ≠ 0 := ne_of_gt hn
      field_simp
      nlinarith [pow_pos hn 3]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson


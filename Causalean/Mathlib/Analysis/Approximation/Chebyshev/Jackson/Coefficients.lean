module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Fejer
public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Finite Fourier coefficients of the order-four Jackson kernel

The zero-extended triangle `triangle N` is convolved with itself on `ℤ`.
The normalization agrees with the Jackson kernel in Causalean, whose integral
over `[-π, π]` is one for positive order.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open MeasureTheory
open scoped BigOperators
open scoped Pointwise

/-- The [triangular sequence](goal) of [order N](hyp:N) at [an integer frequency j](hyp:j) is [N
minus the absolute value of j when that is nonnegative, and zero otherwise](step:1). -/
def triangle (N : ℕ) (j : ℤ) : ℝ := ((N - j.natAbs : ℕ) : ℝ)

/-- The [raw Jackson Fourier coefficient](goal) of [order N](hyp:N) at [an integer frequency
j](hyp:j) is [the discrete convolution of the order-N triangular sequence with itself: the sum over
integers k between −N and N of the triangle at k times the triangle at j − k](step:1). -/
noncomputable def convolution (N : ℕ) (j : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), triangle N k * triangle N (j - k)

/-- The [normalized Jackson coefficient](goal) of [order N](hyp:N) at [an integer frequency
j](hyp:j) is [the raw Jackson Fourier coefficient at j divided by its value at frequency
zero](step:1); at order zero that denominator vanishes and the coefficient is read as zero. -/
noncomputable def normalizedCoeff (N : ℕ) (j : ℤ) : ℝ :=
  convolution N j / convolution N 0

/-- The [scaled Jackson kernel](goal) of [order N](hyp:N) at [an angle u](hyp:u) is [2π times the
normalized Jackson kernel](step:1), so that for positive order it integrates to 2π over a period and its zeroth
Fourier coefficient is one. -/
noncomputable def kernel (N : ℕ) (u : ℝ) : ℝ :=
  2 * Real.pi * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N u

/-- The [cosine Fourier coefficient of the scaled Jackson kernel](goal) of [order N](hyp:N) at [an
integer frequency j](hyp:j) is [one over 2π times the integral over the period from −π to π of the
kernel times the cosine of j times the angle](step:1). -/
noncomputable def kernelCoeff (N : ℕ) (j : ℤ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ u in Set.Icc (-Real.pi) Real.pi, kernel N u * Real.cos ((j : ℝ) * u)

/-- For [an order N](hyp:N) and [an integer frequency j](hyp:j) [whose absolute value is at least
N](hyp:hj), [the triangular sequence is zero](goal). -/
theorem triangle_support (N : ℕ) (j : ℤ) (hj : (N : ℤ) ≤ |j|) :
    triangle N j = 0 := by
  have h : N ≤ j.natAbs := by
    exact_mod_cast (show (N : ℤ) ≤ (j.natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using hj)
  simp [triangle, Nat.sub_eq_zero_of_le h]

/-- For [an order N](hyp:N) and [an integer frequency j](hyp:j) [whose absolute value exceeds 2N −
2](hyp:hj), [the raw Jackson Fourier coefficient is zero](goal). -/
theorem convolution_support (N : ℕ) (j : ℤ)
    (hj : ((2 * N - 2 : ℕ) : ℤ) < |j|) : convolution N j = 0 := by
  unfold convolution
  apply Finset.sum_eq_zero
  intro k hk
  have hbound : (N : ℤ) ≤ |k| ∨ (N : ℤ) ≤ |j - k| := by
    by_cases hN : N = 0
    · left
      simp [hN]
    · have hN' : 1 ≤ N := by omega
      have hlim : (((2 * N - 2 : ℕ) : ℤ)) = 2 * (N : ℤ) - 2 := by omega
      rw [hlim] at hj
      by_cases h : (N : ℤ) ≤ |k|
      · exact Or.inl h
      · right
        have h1 : |j| ≤ |k| + |j - k| := by
          have heq : k + (j - k) = j := by ring
          simpa only [heq] using abs_add_le k (j - k)
        omega
  rcases hbound with h | h
  · simp [triangle_support N k h]
  · simp [triangle_support N (j - k) h]

/-- For [any order N](hyp:N), [the raw Jackson Fourier coefficient at
frequency zero equals (2N³ + N) / 3](goal). -/
theorem convolution_zero (N : ℕ) :
    convolution N 0 = (2 * (N : ℝ) ^ 3 + N) / 3 := by
  have heven : Function.Even (fun k : ℤ => triangle N k * triangle N (0 - k)) := by
    intro k
    simp [triangle, Int.natAbs_neg]
  rw [convolution, Finset.sum_Icc_of_even_eq_range heven N]
  have hterms : ∀ m ∈ Finset.range (N + 1),
      triangle N (m : ℤ) * triangle N (0 - (m : ℤ)) = ((N - m : ℕ) : ℝ) ^ 2 := by
    intro m hm
    have hmN : m ≤ N := by simpa using Finset.mem_range.mp hm
    simp [triangle, Int.natAbs_neg, pow_two]
  rw [Finset.sum_congr rfl hterms]
  simp only [triangle, Int.natAbs_zero, Nat.sub_zero, sub_zero,
    pow_two, two_smul]
  have hflip : (∑ m ∈ Finset.range (N + 1), ((N - m : ℕ) : ℝ) * ((N - m : ℕ) : ℝ)) =
      ∑ m ∈ Finset.range (N + 1), (m : ℝ) ^ 2 := by
    rw [← Finset.sum_flip (n := N) (fun m : ℕ => (m : ℝ) ^ 2)]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hflip]
  have hsq : ∀ n : ℕ, (∑ m ∈ Finset.range (n + 1), (m : ℝ) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [hsq N]
  ring

/-- For [an order N](hyp:N) that is [positive](hyp:hN), [the raw Jackson Fourier coefficient at
frequency zero is strictly positive](goal). -/
theorem convolution_zero_pos (N : ℕ) (hN : 0 < N) :
    0 < convolution N 0 := by
  rw [convolution_zero N]
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the square of the
degree-(N − 1) Chebyshev polynomial of the second kind evaluated at the cosine of u / 2 equals the
finite cosine series, over integer frequencies j from −N to N, with the triangular sequence as
coefficients](goal). -/
theorem triangle_fourier (N : ℕ) (hN : 0 < N) (u : ℝ) :
    ((Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).eval
      (Real.cos (u / 2))) ^ 2 =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        triangle N j * Real.cos ((j : ℝ) * u) := by
  have heven : Function.Even (fun j : ℤ => triangle N j * Real.cos ((j : ℝ) * u)) := by
    intro j
    simp [triangle, Int.natAbs_neg, Real.cos_neg]
  rw [Finset.sum_Icc_of_even_eq_range heven N]
  rw [Finset.sum_range_succ' (fun m : ℕ =>
    triangle N (m : ℤ) * Real.cos (((m : ℤ) : ℝ) * u)) N]
  have hsum : (∑ m ∈ Finset.range N,
      triangle N (((m + 1 : ℕ) : ℤ)) * Real.cos (((((m + 1 : ℕ) : ℤ) : ℝ)) * u)) =
      ∑ m ∈ Finset.range (N - 1),
        ((N - 1 - m : ℕ) : ℝ) * Real.cos ((((m + 1 : ℕ) : ℝ)) * u) := by
    have hNs : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hNs, Finset.sum_range_succ]
    have hend : triangle N ((((N - 1) + 1 : ℕ) : ℤ)) = 0 := by
      rw [← hNs]
      exact triangle_support N N (by simp)
    simp only [← hNs, triangle_support N N (by simp), zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro m hm
    have hmN : m < N := by have := Finset.mem_range.mp hm; omega
    have hmle : m + 1 ≤ N := by omega
    simp only [triangle, Int.natAbs_natCast, Int.cast_natCast]
    rw [show N - (m + 1) = N - 1 - m by omega]
  rw [hsum]
  have h0 : triangle N (0 : ℤ) * Real.cos (((0 : ℤ) : ℝ) * u) = (N : ℝ) := by
    simp [triangle]
  rw [h0]
  have hcheb := Causalean.Mathlib.Analysis.JacksonApproximation.cheb_U_sq_eval (N - 1) u
  simp only [Nat.cast_zero, Int.cast_natCast, Int.cast_zero, zero_mul, Real.cos_zero, mul_one] at *
  rw [h0, two_smul]
  rw [hcheb]
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast (show N - 1 + 1 = N by omega)
  rw [hcast]
  have hsumcast : (∑ m ∈ Finset.range (N - 1),
      ((N - 1 - m : ℕ) : ℝ) * Real.cos (((m + 1 : ℕ) : ℝ) * u)) =
      ∑ m ∈ Finset.range (N - 1),
        (((N - 1 : ℕ) : ℝ) - (m : ℝ)) * Real.cos (((m + 1 : ℕ) : ℝ) * u) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmle : m ≤ N - 1 := by have := Finset.mem_range.mp hm; omega
    rw [Nat.cast_sub hmle]
  rw [hsumcast]
  ring

/-! The next two lemmas separate trigonometric multiplication from the
bounded integer-pair reindexing. The latter must retain the zero-extension
endpoints; `convolution_support` removes them only after reindexing. -/

/-- For [a finite set of integer frequencies](hyp:s) that is [symmetric under negation](hyp:hs),
[real coefficients](hyp:a) that are [even in the frequency](hyp:ha), and [any angle u](hyp:u), [the
square of the cosine series with those frequencies and coefficients equals the double sum over
pairs of frequencies of the product of the two coefficients times the cosine of the sum of the two
frequencies times u](goal). -/
theorem finite_cosine_square_of_even (s : Finset ℤ) (a : ℤ → ℝ)
    (hs : ∀ k : ℤ, k ∈ s ↔ -k ∈ s) (ha : ∀ k : ℤ, a (-k) = a k)
    (u : ℝ) :
    (∑ k ∈ s, a k * Real.cos ((k : ℝ) * u)) ^ 2 =
      ∑ k ∈ s, ∑ l ∈ s,
        a k * a l * Real.cos (((k + l : ℤ) : ℝ) * u) := by
  have hneg : -s = s := by
    ext k
    rw [Finset.mem_neg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hs y).mp hy
    · intro hk
      exact ⟨-k, (hs k).mp hk, by simp⟩
  have hdiff :
      (∑ k ∈ s, ∑ l ∈ s,
        a k * a l * Real.cos (((k - l : ℤ) : ℝ) * u)) =
      ∑ k ∈ s, ∑ l ∈ s,
        a k * a l * Real.cos (((k + l : ℤ) : ℝ) * u) := by
    apply Finset.sum_congr rfl
    intro k hk
    have h := Finset.sum_neg_index s
      (fun l => a k * a l * Real.cos (((k + l : ℤ) : ℝ) * u))
    rw [hneg] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [ha, sub_eq_add_neg]
  have hpoint (k l : ℤ) :
      (a k * Real.cos ((k : ℝ) * u)) * (a l * Real.cos ((l : ℝ) * u)) =
      (a k * a l * Real.cos (((k + l : ℤ) : ℝ) * u) +
       a k * a l * Real.cos (((k - l : ℤ) : ℝ) * u)) / 2 := by
    push_cast
    rw [show ((k : ℝ) + (l : ℝ)) * u = (k : ℝ) * u + (l : ℝ) * u by ring,
      show ((k : ℝ) - (l : ℝ)) * u = (k : ℝ) * u - (l : ℝ) * u by ring]
    rw [Real.cos_add, Real.cos_sub]
    ring
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hpoint, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hdiff]
  ring

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the double sum
over pairs of frequencies between −N and N of the product of two triangular coefficients times the
cosine of the summed frequency times u equals the cosine series over frequencies j between −(2N −
2) and 2N − 2 with the raw Jackson Fourier coefficients](goal). -/
theorem triangle_pair_sum_eq_convolution (N : ℕ) (hN : 0 < N) (u : ℝ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        triangle N k * triangle N l *
          Real.cos (((k + l : ℤ) : ℝ) * u)) =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
        convolution N j * Real.cos ((j : ℝ) * u) := by
  let base : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let wide : Finset ℤ := Finset.Icc (-(2 * N : ℤ)) (2 * N : ℤ)
  let narrow : Finset ℤ :=
    Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  have hshift (k : ℤ) (hk : k ∈ base) :
      (∑ l ∈ base, triangle N k * triangle N l *
        Real.cos (((k + l : ℤ) : ℝ) * u)) =
      ∑ j ∈ wide, triangle N k * triangle N (j - k) *
        Real.cos ((j : ℝ) * u) := by
    have hb : -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ) := Finset.mem_Icc.mp hk
    have hbij :
        (∑ l ∈ base, triangle N k * triangle N l *
          Real.cos (((k + l : ℤ) : ℝ) * u)) =
        ∑ j ∈ Finset.Icc (k - (N : ℤ)) (k + (N : ℤ)),
          triangle N k * triangle N (j - k) *
            Real.cos ((j : ℝ) * u) := by
      apply Finset.sum_bij (fun l _ => k + l)
      · intro l hl
        change l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) at hl
        simp only [Finset.mem_Icc] at hl ⊢
        omega
      · intro l₁ hl₁ l₂ hl₂ heq
        omega
      · intro j hj
        refine ⟨j - k, ?_, by ring⟩
        · change j - k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
          simp only [Finset.mem_Icc] at hj ⊢
          omega
      · intro l hl
        simp only [add_sub_cancel_left]
    rw [hbij]
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      dsimp [wide]
      simp only [Finset.mem_Icc]
      omega
    · intro j hj hjnot
      have hzero : triangle N (j - k) = 0 := by
        apply triangle_support
        simp only [Finset.mem_Icc] at hjnot
        have : j - k ≤ -(N : ℤ) ∨ (N : ℤ) ≤ j - k := by omega
        rcases this with h | h
        · rw [abs_of_nonpos (by omega)]
          omega
        · rw [abs_of_nonneg (by omega)]
          omega
      simp [hzero]
  have hwide :
      (∑ k ∈ base, ∑ l ∈ base,
        triangle N k * triangle N l * Real.cos (((k + l : ℤ) : ℝ) * u)) =
      ∑ j ∈ wide, convolution N j * Real.cos ((j : ℝ) * u) := by
    have hreindex :
        (∑ k ∈ base, ∑ l ∈ base,
          triangle N k * triangle N l * Real.cos (((k + l : ℤ) : ℝ) * u)) =
        ∑ k ∈ base, ∑ j ∈ wide,
          triangle N k * triangle N (j - k) * Real.cos ((j : ℝ) * u) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hshift k hk
    rw [hreindex]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [convolution]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hsubset : narrow ⊆ wide := by
    intro j hj
    change j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ) at hj
    change j ∈ Finset.Icc (-(2 * N : ℤ)) (2 * N : ℤ)
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have htrim :
      (∑ j ∈ wide, convolution N j * Real.cos ((j : ℝ) * u)) =
      ∑ j ∈ narrow, convolution N j * Real.cos ((j : ℝ) * u) := by
    symm
    apply Finset.sum_subset hsubset
    intro j hj hjnot
    have hzero : convolution N j = 0 := by
      apply convolution_support
      change j ∉ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ) at hjnot
      simp only [Finset.mem_Icc] at hjnot
      rcases le_total j 0 with h | h
      · rw [abs_of_nonpos h]
        omega
      · rw [abs_of_nonneg h]
        omega
    simp [hzero]
  exact hwide.trans htrim

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the square of the
triangular cosine series over frequencies between −N and N equals the cosine series over
frequencies j between −(2N − 2) and 2N − 2 with the raw Jackson Fourier coefficients](goal). -/
theorem triangle_fourier_square (N : ℕ) (hN : 0 < N) (u : ℝ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      triangle N k * Real.cos ((k : ℝ) * u)) ^ 2 =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
        convolution N j * Real.cos ((j : ℝ) * u) := by
  calc
    _ = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            triangle N k * triangle N l *
              Real.cos (((k + l : ℤ) : ℝ) * u) := by
        apply finite_cosine_square_of_even
        · intro k
          simp only [Finset.mem_Icc]
          omega
        · intro k
          simp [triangle, Int.natAbs_neg]
    _ = _ := triangle_pair_sum_eq_convolution N hN u

/-- For [two integer frequencies k and j](hyp:k,j), [one over 2π times the integral from −π to π of
the product of the cosines of k u and j u equals one when both frequencies are zero, one half when
they are not both zero but have the same absolute value, and zero otherwise](goal). -/
theorem cosine_mode_orthogonality (k j : ℤ) :
    (1 / (2 * Real.pi)) *
      ∫ u in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((k : ℝ) * u) * Real.cos ((j : ℝ) * u) =
      if k = 0 ∧ j = 0 then 1 else if |k| = |j| then 1 / 2 else 0 := by
  have hcos (m : ℤ) :
      (∫ u in Set.Icc (-Real.pi) Real.pi, Real.cos ((m : ℝ) * u)) =
        if m = 0 then 2 * Real.pi else 0 := by
    by_cases hm : m = 0
    · subst m
      simp [Real.pi_pos.le]
      ring
    · rw [if_neg hm, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
          (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      rw [intervalIntegral.integral_comp_mul_left Real.cos hm0, integral_cos]
      simp
  have hpoint (u : ℝ) :
      Real.cos ((k : ℝ) * u) * Real.cos ((j : ℝ) * u) =
        (Real.cos (((k - j : ℤ) : ℝ) * u) +
          Real.cos (((k + j : ℤ) : ℝ) * u)) / 2 := by
    rw [show (((k - j : ℤ) : ℝ) * u) = (k : ℝ) * u - (j : ℝ) * u by
        push_cast; ring,
      show (((k + j : ℤ) : ℝ) * u) = (k : ℝ) * u + (j : ℝ) * u by
        push_cast; ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_div]
  rw [MeasureTheory.integral_add
    ((show Continuous (fun u : ℝ => Real.cos (((k - j : ℤ) : ℝ) * u)) by
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
    ((show Continuous (fun u : ℝ => Real.cos (((k + j : ℤ) : ℝ) * u)) by
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
  rw [hcos, hcos]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hform :
      (1 / (2 * Real.pi)) *
        (((if k - j = 0 then 2 * Real.pi else 0) +
          (if k + j = 0 then 2 * Real.pi else 0)) / 2) =
      ((if k - j = 0 then (1 : ℝ) else 0) +
        (if k + j = 0 then (1 : ℝ) else 0)) / 2 := by
    split_ifs <;> field_simp <;> ring
  rw [hform]
  by_cases h00 : k = 0 ∧ j = 0
  · rcases h00 with ⟨rfl, rfl⟩
    norm_num
  · simp only [h00, if_false]
    by_cases habs : |k| = |j|
    · rw [if_pos habs]
      have hor : k = j ∨ k = -j := abs_eq_abs.mp habs
      rcases hor with heq | heq
      · have hk : k ≠ 0 := by aesop
        subst j
        simp [show k + k ≠ 0 by omega]
      · have hk : k ≠ 0 := by aesop
        have hj : j = -k := by omega
        subst j
        simp [hk]
    · rw [if_neg habs]
      have hsub : k - j ≠ 0 := by
        intro h
        exact habs (abs_eq_abs.mpr (Or.inl (by omega)))
      have hadd : k + j ≠ 0 := by
        intro h
        exact habs (abs_eq_abs.mpr (Or.inr (by omega)))
      simp [hsub, hadd]

/-- For [any order N](hyp:N) and [any integer frequency j](hyp:j), [the raw Jackson Fourier
coefficient takes the same value at −j as at j](goal). -/
theorem convolution_even (N : ℕ) (j : ℤ) :
    convolution N (-j) = convolution N j := by
  open scoped Pointwise in
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hs : -s = s := by
    ext k
    simp only [s, Finset.mem_neg, Finset.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
      omega
    · intro h
      refine ⟨-k, ?_, by simp⟩
      omega
  change (∑ k ∈ s, triangle N k * triangle N (-j - k)) =
    ∑ k ∈ s, triangle N k * triangle N (j - k)
  conv_lhs => rw [← hs, Finset.sum_neg_index]
  apply Finset.sum_congr rfl
  intro k hk
  have htri (m : ℤ) : triangle N (-m) = triangle N m := by
    simp [triangle, Int.natAbs_neg]
  rw [htri k, show -j - -k = -(j - k) by omega, htri]

/-- For [a finite set of integer frequencies](hyp:s) that is [symmetric under negation](hyp:hs),
[real coefficients](hyp:a) that are [even in the frequency](hyp:ha), and [an integer frequency
j](hyp:j), [one over 2π times the integral from −π to π of the cosine series times the cosine of j
u equals the coefficient at j when j belongs to the frequency set, and zero otherwise](goal). -/
theorem cosine_coefficient_even_finite (s : Finset ℤ) (a : ℤ → ℝ)
    (hs : ∀ k : ℤ, k ∈ s ↔ -k ∈ s)
    (ha : ∀ k : ℤ, a (-k) = a k) (j : ℤ) :
    (1 / (2 * Real.pi)) *
      ∫ u in Set.Icc (-Real.pi) Real.pi,
        (∑ k ∈ s, a k * Real.cos ((k : ℝ) * u)) *
          Real.cos ((j : ℝ) * u) =
      if j ∈ s then a j else 0 := by
  have hint (k : ℤ) :
      IntegrableOn (fun u : ℝ =>
        (a k * Real.cos ((k : ℝ) * u)) * Real.cos ((j : ℝ) * u))
        (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun u : ℝ =>
      (a k * Real.cos ((k : ℝ) * u)) * Real.cos ((j : ℝ) * u)) by
        fun_prop).continuousOn.integrableOn_compact isCompact_Icc
  have hextract :
      (1 / (2 * Real.pi)) *
        ∫ u in Set.Icc (-Real.pi) Real.pi,
          (∑ k ∈ s, a k * Real.cos ((k : ℝ) * u)) *
            Real.cos ((j : ℝ) * u) =
      ∑ k ∈ s, a k *
        (if k = 0 ∧ j = 0 then 1 else if |k| = |j| then 1 / 2 else 0) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum s (fun k _ => hint k)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hfun : (fun u : ℝ => a k * Real.cos ((k : ℝ) * u) *
        Real.cos ((j : ℝ) * u)) =
        (fun u : ℝ => a k * (Real.cos ((k : ℝ) * u) *
        Real.cos ((j : ℝ) * u))) := by funext u; ring
    rw [hfun, integral_const_mul]
    rw [mul_left_comm]
    exact congrArg (a k * ·) (cosine_mode_orthogonality k j)
  rw [hextract]
  by_cases hj : j = 0
  · subst j
    have hterm (k : ℤ) :
        a k * (if k = 0 ∧ (0 : ℤ) = 0 then 1 else if |k| = |(0 : ℤ)| then 1 / 2 else 0) =
        if (0 : ℤ) = k then a k else 0 := by
      by_cases hk : k = 0
      · subst k; simp
      · have hk' : (0 : ℤ) ≠ k := Ne.symm hk
        simp [hk, hk']
    calc
      _ = ∑ k ∈ s, if (0 : ℤ) = k then a k else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ = _ := Finset.sum_ite_eq s 0 a
  · have hterm (k : ℤ) :
        a k * (if k = 0 ∧ j = 0 then 1 else if |k| = |j| then 1 / 2 else 0) =
        (if j = k then a k / 2 else 0) +
          (if -j = k then a k / 2 else 0) := by
      simp only [hj, and_false, if_false]
      by_cases hkj : k = j
      · subst k
        have hneq : -j ≠ j := by omega
        simp [hneq]
        ring
      by_cases hkn : k = -j
      · subst k
        have hneq : j ≠ -j := by omega
        simp [hneq, abs_neg]
        ring
      have habs : |k| ≠ |j| := by
        intro h
        rcases abs_eq_abs.mp h with h | h
        · exact hkj h
        · exact hkn h
      simp [habs, Ne.symm hkj, Ne.symm hkn]
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    have hmem : -j ∈ s ↔ j ∈ s := (hs j).symm
    by_cases hjs : j ∈ s
    · have hnegs : -j ∈ s := hmem.mpr hjs
      simp [hjs, hnegs, ha j]
    · have hnegs : -j ∉ s := by simpa only [hmem] using hjs
      simp [hjs, hnegs]

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the raw Jackson
kernel equals the cosine series over frequencies j between −(2N − 2) and 2N − 2 with the raw
Jackson Fourier coefficients](goal). -/
theorem raw_kernel_fourier (N : ℕ) (hN : 0 < N) (u : ℝ) :
    Causalean.Mathlib.Analysis.JacksonApproximation.jraw N u =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
        convolution N j * Real.cos ((j : ℝ) * u) := by
  rw [Causalean.Mathlib.Analysis.JacksonApproximation.jraw_eq_chebyshev N hN u]
  rw [show ((Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).eval
      (Real.cos (u / 2))) ^ 4 =
      (((Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).eval
      (Real.cos (u / 2))) ^ 2) ^ 2 by ring]
  rw [triangle_fourier N hN u, triangle_fourier_square N hN u]

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the scaled
Jackson kernel equals the cosine series over frequencies j between −(2N − 2) and 2N − 2 with the
normalized Jackson coefficients](goal). -/
theorem kernel_fourier (N : ℕ) (hN : 0 < N) (u : ℝ) :
    kernel N u =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
        normalizedCoeff N j * Real.cos ((j : ℝ) * u) := by
  have hmass : Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass N =
      2 * Real.pi * convolution N 0 := by
    rw [Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass_eq N hN,
      convolution_zero N]
    ring
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hconv : convolution N 0 ≠ 0 := ne_of_gt (convolution_zero_pos N hN)
  simp only [kernel, Causalean.Mathlib.Analysis.JacksonApproximation.jackson,
    hmass, raw_kernel_fourier N hN u, normalizedCoeff]
  calc
    _ = (1 / convolution N 0) *
        (∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
          convolution N j * Real.cos ((j : ℝ) * u)) := by
      field_simp
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any integer frequency j](hyp:j), [the
cosine Fourier coefficient of the scaled Jackson kernel, defined by integration, equals the
normalized Jackson coefficient](goal). -/
theorem kernelCoeff_eq_normalizedCoeff (N : ℕ) (hN : 0 < N) (j : ℤ) :
    kernelCoeff N j = normalizedCoeff N j := by
  let s : Finset ℤ :=
    Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  have hs : ∀ k : ℤ, k ∈ s ↔ -k ∈ s := by
    intro k
    simp only [s, Finset.mem_Icc]
    omega
  have ha : ∀ k : ℤ, normalizedCoeff N (-k) = normalizedCoeff N k := by
    intro k
    simp only [normalizedCoeff, convolution_even]
  have hcoeff := cosine_coefficient_even_finite s (normalizedCoeff N) hs ha j
  unfold kernelCoeff
  simp_rw [kernel_fourier N hN]
  change (1 / (2 * Real.pi)) *
      ∫ u in Set.Icc (-Real.pi) Real.pi,
        (∑ k ∈ s, normalizedCoeff N k * Real.cos ((k : ℝ) * u)) *
          Real.cos ((j : ℝ) * u) = normalizedCoeff N j
  rw [hcoeff]
  by_cases hj : j ∈ s
  · simp [hj]
  · have hfar : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
      have hj' : j ∉ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ))
          ((2 * N - 2 : ℕ) : ℤ) := hj
      simp only [Finset.mem_Icc] at hj'
      rcases le_total j 0 with h | h
      · rw [abs_of_nonpos h]
        omega
      · rw [abs_of_nonneg h]
        omega
    simp [hj, normalizedCoeff, convolution_support N j hfar]

/-- For [an order N](hyp:N) and [an integer frequency j](hyp:j) [whose absolute value exceeds 2N −
2](hyp:hj), [the normalized Jackson coefficient is zero](goal). -/
theorem normalizedCoeff_support (N : ℕ) (j : ℤ)
    (hj : ((2 * N - 2 : ℕ) : ℤ) < |j|) : normalizedCoeff N j = 0 := by
  simp [normalizedCoeff, convolution_support N j hj]

/-- For [an order N](hyp:N) that is [positive](hyp:hN), [the scaled Jackson kernel divided by 2π
integrates to one over the period from −π to π](goal). -/
theorem kernel_normalized_integral (N : ℕ) (hN : 0 < N) :
    (∫ u in Set.Icc (-Real.pi) Real.pi, kernel N u / (2 * Real.pi)) = 1 := by
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  convert Causalean.Mathlib.Analysis.JacksonApproximation.jackson_integral_eq_one N hN using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  simp only [kernel]
  field_simp

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson


module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Probabilists’ Hermite generating series

This module derives the real exponential generating series for Mathlib’s
probabilists’ Hermite polynomials from their explicit coefficients and
absolutely convergent exponential-series convolution.
-/

public section

open Polynomial
open scoped BigOperators

namespace Causalean.Mathlib.Probability


/-- The coefficient of [the specified degree](hyp:k) in a Hermite polynomial
[of that degree plus an even gap](hyp:m), divided by the order factorial,
[equals the signed reciprocal product of the power of two and two factorials](goal).

Start from `coeff_hermite_explicit`. Cancel the binomial factorial ratio and
use the even/odd double-factorial decomposition of `(2*m)!`; handle `m = 0`
explicitly because the natural subtraction in `(2*m-1)!!` saturates at zero.
-/
theorem coeff_hermite_div_factorial (m k : ℕ) :
    ((hermite (2 * m + k)).coeff k : ℝ) / (Nat.factorial (2 * m + k) : ℝ) =
      (-1 : ℝ) ^ m /
        ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.factorial k : ℝ)) := by
  have hdf : Nat.factorial (2 * m) =
      2 ^ m * Nat.factorial m * Nat.doubleFactorial (2 * m - 1) := by
    cases m with
    | zero => simp
    | succ m =>
      have h := Nat.factorial_eq_mul_doubleFactorial (2 * (m + 1) - 1)
      rw [show 2 * (m + 1) - 1 + 1 = 2 * (m + 1) by omega,
        Nat.doubleFactorial_two_mul] at h
      exact h
  have hc := Nat.choose_mul_factorial_mul_factorial
    (show k ≤ 2 * m + k by omega)
  rw [show 2 * m + k - k = 2 * m by omega, hdf] at hc
  have hcR : (Nat.choose (2 * m + k) k : ℝ) * (Nat.factorial k : ℝ) *
      ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (Nat.doubleFactorial (2 * m - 1) : ℝ)) =
      (Nat.factorial (2 * m + k) : ℝ) := by exact_mod_cast hc
  rw [coeff_hermite_explicit]
  push_cast
  rw [← hcR]
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hm : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  have hd : (Nat.doubleFactorial (2 * m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos _))
  have hc0 : (Nat.choose (2 * m + k) k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  field_simp

/-- [A factorial-normalized Hermite evaluation](hyp:n,z)
[equals the finite sum over its even degree gaps](goal).

Expand by coefficients through degree `n`. Odd gaps vanish by
`coeff_hermite_of_odd_add`. Reindex each surviving degree as `n - 2*m` and
apply `coeff_hermite_div_factorial`; the range is exactly `0 ≤ m ≤ n/2`.
-/
theorem hermite_eval_div_factorial (n : ℕ) (z : ℝ) :
    (aeval z (hermite n) : ℝ) / (Nat.factorial n : ℝ) =
      ∑ m ∈ Finset.range (n / 2 + 1),
        (-1 : ℝ) ^ m * z ^ (n - 2 * m) /
          ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.factorial (n - 2 * m) : ℝ)) := by
  classical
  rw [aeval_eq_sum_range, natDegree_hermite, Finset.sum_div]
  simp only [zsmul_eq_mul]
  calc
    ∑ k ∈ Finset.range (n + 1),
        ((hermite n).coeff k : ℝ) * z ^ k / (Nat.factorial n : ℝ) =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even (n + k)),
        ((hermite n).coeff k : ℝ) * z ^ k / (Nat.factorial n : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      have ho : Odd (n + k) := Nat.not_even_iff_odd.mp
        (fun he => hnot (Finset.mem_filter.mpr ⟨hk, he⟩))
      simp [coeff_hermite_of_odd_add ho]
    _ = _ := by
      symm
      refine Finset.sum_bij (fun m _ => n - 2 * m) ?_ ?_ ?_ ?_
      · intro m hm
        have hm' := Finset.mem_range.mp hm
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        exact ⟨n - m, by omega⟩
      · intro m hm l hl heq
        have hm' := Finset.mem_range.mp hm
        have hl' := Finset.mem_range.mp hl
        omega
      · intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hk, ⟨r, hr⟩⟩
        have hk' := Finset.mem_range.mp hk
        refine ⟨(n - k) / 2, Finset.mem_range.mpr (by omega), ?_⟩
        omega
      · intro m hm
        have hm' := Finset.mem_range.mp hm
        have hn : 2 * m + (n - 2 * m) = n := by omega
        have hc := coeff_hermite_div_factorial m (n - 2 * m)
        rw [hn] at hc
        rw [mul_div_assoc, mul_comm _ (z ^ _), mul_div_assoc, hc]
        ring

/-- [A Hermite exponential-series term](hyp:n,z,t)
[is the finite convolution of a linear exponential and an even quadratic exponential](goal).

Use `hermite_eval_div_factorial`. The antidiagonal pairs have first coordinate
`n - 2*m` and second coordinate `2*m`; the other second coordinates contribute
zero. The exponent identity `(n - 2*m) + 2*m = n` justifies combining powers
without dividing by `z` or `t`, so zero inputs remain included.
-/
theorem hermite_term_eq_convolution (n : ℕ) (z t : ℝ) :
    (aeval z (hermite n) : ℝ) * t ^ n / (Nat.factorial n : ℝ) =
      ∑ kl ∈ Finset.antidiagonal n,
        ((z * t) ^ kl.1 / (Nat.factorial kl.1 : ℝ)) *
          (if Even kl.2 then
            (-(t ^ 2 / 2)) ^ (kl.2 / 2) / (Nat.factorial (kl.2 / 2) : ℝ)
          else 0) := by
  classical
  calc
    (aeval z (hermite n) : ℝ) * t ^ n / (Nat.factorial n : ℝ) =
        ((aeval z (hermite n) : ℝ) / (Nat.factorial n : ℝ)) * t ^ n := by ring
    _ = ∑ m ∈ Finset.range (n / 2 + 1),
        ((-1 : ℝ) ^ m * z ^ (n - 2 * m) /
          ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            (Nat.factorial (n - 2 * m) : ℝ))) * t ^ n := by
      rw [hermite_eval_div_factorial, Finset.sum_mul]
    _ = ∑ kl ∈ (Finset.antidiagonal n).filter (fun kl => Even kl.2),
        ((z * t) ^ kl.1 / (Nat.factorial kl.1 : ℝ)) *
          (if Even kl.2 then
            (-(t ^ 2 / 2)) ^ (kl.2 / 2) / (Nat.factorial (kl.2 / 2) : ℝ)
          else 0) := by
      refine Finset.sum_bij (fun m _ => (n - 2 * m, 2 * m)) ?_ ?_ ?_ ?_
      · intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_antidiagonal.mpr (by omega), ⟨m, by omega⟩⟩
      · intro m hm l hl heq
        have he := congrArg Prod.snd heq
        dsimp at he
        omega
      · intro kl hkl
        rcases Finset.mem_filter.mp hkl with ⟨hkl, ⟨m, hm⟩⟩
        have hsum := Finset.mem_antidiagonal.mp hkl
        refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
        apply Prod.ext <;> dsimp <;> omega
      · intro m hm
        have hm' := Finset.mem_range.mp hm
        have ht : t ^ n = t ^ (n - 2 * m) * t ^ (2 * m) := by
          rw [← pow_add]
          congr 1
          omega
        dsimp
        rw [if_pos (show Even (2 * m) from ⟨m, by omega⟩),
          Nat.mul_div_cancel_left _ (Nat.succ_pos 1), mul_pow, neg_pow (t ^ 2 / 2), div_pow,
          ← pow_mul, ht]
        have hk : (Nat.factorial (n - 2 * m) : ℝ) ≠ 0 := by positivity
        have hm0 : (Nat.factorial m : ℝ) ≠ 0 := by positivity
        field_simp
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro kl hkl hnot
      have he : ¬ Even kl.2 := fun he => hnot (Finset.mem_filter.mpr ⟨hkl, he⟩)
      simp [he]



/-- Inserting zeros at the odd indices of [a real exponential series](hyp:u)
[preserves its sum, the exponential of its argument](goal).

Transport `NormedSpace.expSeries_div_hasSum_exp u` through the embedding
`m ↦ 2*m`, extending by zero outside its range. The range is exactly the even
natural numbers, and division by two recovers the original index. Convert
the normed-algebra exponential to `Real.exp` using `Real.exp_eq_exp_ℝ`.
-/
theorem hasSum_even_expSeries (u : ℝ) :
    HasSum (fun n : ℕ => if Even n then u ^ (n / 2) / (Nat.factorial (n / 2) : ℝ)
      else 0) (Real.exp u) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := by
    intro m n h
    change 2 * m = 2 * n at h
    omega
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    have hodd : ¬ Even n := by
      intro heven
      exact hn ⟨n / 2, Nat.two_mul_div_two_of_even heven⟩
    simp only [hodd, if_false]
  · simpa only [Function.comp_def, even_two_mul, if_true,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2), Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp u

/-- The absolute values of [the exponential series with zeros inserted at odd indices](hyp:u)
[form a summable series](goal).

Use the same doubling embedding as `hasSum_even_expSeries`, starting with
`NormedSpace.norm_expSeries_div_summable`. This explicitly justifies the
Cauchy product and regrouping; no conditional-series interchange is used.
-/
theorem summable_norm_even_expSeries (u : ℝ) :
    Summable (fun n : ℕ => ‖if Even n then
      u ^ (n / 2) / (Nat.factorial (n / 2) : ℝ) else 0‖) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := by
    intro m n h
    change 2 * m = 2 * n at h
    omega
  refine (hinj.summable_iff ?_).mp ?_
  · intro n hn
    have hodd : ¬ Even n := by
      intro heven
      exact hn ⟨n / 2, Nat.two_mul_div_two_of_even heven⟩
    simp only [hodd, if_false, norm_zero]
  · simpa only [Function.comp_def, even_two_mul, if_true,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using
      NormedSpace.norm_expSeries_div_summable u

/-- The finite Cauchy convolution of [a linear exponential argument](hyp:a)
and [an even-position exponential argument](hyp:u)
[has sum equal to the exponential of their sum](goal).

Use the norm summability of the ordinary exponential series and
`summable_norm_even_expSeries`. Apply the Mathlib summability and sum formula
for antidiagonals, then retain the resulting `HasSum` via `Summable.hasSum`.
-/
theorem hasSum_expSeries_convolution (a u : ℝ) :
    HasSum (fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n,
      (a ^ kl.1 / (Nat.factorial kl.1 : ℝ)) *
        (if Even kl.2 then u ^ (kl.2 / 2) / (Nat.factorial (kl.2 / 2) : ℝ) else 0))
      (Real.exp (a + u)) := by
  let f : ℕ → ℝ := fun n => a ^ n / (Nat.factorial n : ℝ)
  let g : ℕ → ℝ := fun n => if Even n then
    u ^ (n / 2) / (Nat.factorial (n / 2) : ℝ) else 0
  have hf : HasSum f (Real.exp a) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp a
  have hg : HasSum g (Real.exp u) := hasSum_even_expSeries u
  have hfn : Summable (fun n => ‖f n‖) := NormedSpace.norm_expSeries_div_summable a
  have hgn : Summable (fun n => ‖g n‖) := summable_norm_even_expSeries u
  have hs : Summable (fun n => ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have heq : (∑' n, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) =
      Real.exp (a + u) := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
      hf.tsum_eq, hg.tsum_eq, ← Real.exp_add]
  exact heq ▸ hs.hasSum



/-- The absolute values of [the real Hermite exponential-series terms](hyp:z,t)
[form a summable series](goal). -/
theorem summable_norm_hermite (z t : ℝ) :
    Summable (fun j : ℕ =>
      ‖(aeval z (hermite j) : ℝ) * t ^ j / (Nat.factorial j : ℝ)‖) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (NormedSpace.norm_expSeries_div_summable (z * t))
    (summable_norm_even_expSeries (-(t ^ 2 / 2)))
  exact h.congr (fun n => congrArg (fun x : ℝ => ‖x‖)
    (hermite_term_eq_convolution n z t).symm)

/-- The probabilists' Hermite exponential generating series [at real point
and parameter](hyp:z,t) [has sum equal to the exponential of their product
minus half the parameter squared](goal). -/
theorem hasSum_hermite (z t : ℝ) :
    HasSum (fun j : ℕ =>
      (aeval z (hermite j) : ℝ) * t ^ j / (Nat.factorial j : ℝ))
      (Real.exp (z * t - t ^ 2 / 2)) := by
  have h := hasSum_expSeries_convolution (z * t) (-(t ^ 2 / 2))
  simpa only [sub_eq_add_neg] using
    h.congr_fun (fun n => hermite_term_eq_convolution n z t)


end Causalean.Mathlib.Probability


module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Multiindex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-!
# Degree-two Legendre entries and explicit inverse coefficients

The orthonormal entries on the interval [-1/2,1/2] are 1, sqrt(12)t,
and sqrt(5)(6t²-1/2). These are the degree-zero through degree-two standard
Legendre polynomials at 2t multiplied by sqrt(2k+1). See the primary source
https://dlmf.nist.gov/18.3 and its Rodrigues representation
https://dlmf.nist.gov/18.5#ii. Only these three entries are needed; the default
value outside this degree range is never used by the API.

The inverse formulas are 1 = ell₀(t), h t = h ell₁(t)/sqrt(12), and
(h t)² = h² ell₀(t)/12 + h² ell₂(t)/(6 sqrt(5)). They are derived here
independently, without importing any research module or its forward affine
change-of-basis theorem.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [normalized Legendre entry](goal) of [degree k](hyp:k) at [a point t](hyp:t) is [1 for
degree zero, the square root of 12 times t for degree one, the square root of 5 times (6 t² − 1/2)
for degree two, and zero for every higher degree](step:1). -/
def legendreEntry (k : ℕ) (t : ℝ) : ℝ :=
  if k = 0 then 1 else if k = 1 then Real.sqrt 12 * t
  else if k = 2 then Real.sqrt 5 * (6 * t ^ 2 - 1 / 2) else 0

/-- The [inverse Legendre entry](goal) at [scale h](hyp:h) for [a monomial degree k and a Legendre
degree j](hyp:k,j) is [1 when both degrees are zero, h over the square root of 12 when both are
one, h² / 12 for degrees two and zero, h² over 6 times the square root of 5 when both are two, and
zero otherwise](step:1). -/
def inverseEntry (h : ℝ) (k j : ℕ) : ℝ :=
  if k = 0 ∧ j = 0 then 1
  else if k = 1 ∧ j = 1 then h / Real.sqrt 12
  else if k = 2 ∧ j = 0 then h ^ 2 / 12
  else if k = 2 ∧ j = 2 then h ^ 2 / (6 * Real.sqrt 5) else 0

/-- For [a degree k](hyp:k) [at most two](hyp:hk) and [any real scale h and point t](hyp:h,t), [the
monomial (h t)^k equals the sum over the first three Legendre degrees of the inverse entry times
the normalized Legendre entry at t](goal). -/
theorem monomial_inverse_legendre (k : ℕ) (hk : k ≤ 2) (h t : ℝ) :
    (h * t) ^ k = ∑ j : Fin 3, inverseEntry h k j.val * legendreEntry j.val t := by
  have hs12 : Real.sqrt 12 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs5 : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  interval_cases k <;>
    simp [Fin.sum_univ_succ, inverseEntry, legendreEntry]
  · field_simp
  · field_simp
    ring

/-- For [any scale](hyp:h) and [a monomial degree k and a Legendre degree j](hyp:k,j) with
[j strictly larger than k](hyp:hj), [the inverse Legendre entry is
zero](goal). -/
theorem inverseEntry_above (h : ℝ) (k j : ℕ) (hj : k < j) :
    inverseEntry h k j = 0 := by
  unfold inverseEntry
  split_ifs <;> first | omega | rfl

/-- For [a scale h](hyp:h) that is [positive](hyp:hh) and [a monomial degree k and a Legendre
degree j](hyp:k,j) with [k at most two](hyp:hk), [the inverse Legendre entry is at most h to the
power k in absolute value](goal). -/
theorem inverseEntry_abs_le (h : ℝ) (hh : 0 < h)
    (k j : ℕ) (hk : k ≤ 2) :
    |inverseEntry h k j| ≤ h ^ k := by
  have hs12 : 1 ≤ Real.sqrt 12 := Real.one_le_sqrt.mpr (by norm_num)
  have hs5 : 1 ≤ Real.sqrt 5 := Real.one_le_sqrt.mpr (by norm_num)
  have hs6 : 1 ≤ 6 * Real.sqrt 5 := by linarith
  unfold inverseEntry
  split_ifs with h0 h1 h2 h3
  · rcases h0 with ⟨rfl, rfl⟩
    simp
  · rcases h1 with ⟨rfl, rfl⟩
    simp only [pow_one, abs_div, abs_of_pos hh, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hh.le hs12
  · rcases h2 with ⟨rfl, rfl⟩
    rw [abs_of_nonneg (div_nonneg (sq_nonneg h) (by norm_num))]
    exact div_le_self (sq_nonneg h) (by norm_num)
  · rcases h3 with ⟨rfl, rfl⟩
    rw [abs_of_nonneg (div_nonneg (sq_nonneg h) (by positivity))]
    exact div_le_self (sq_nonneg h) hs6
  · simpa using pow_nonneg hh.le k

/-- For [a degree k](hyp:k) [at most two](hyp:hk) and [a point t](hyp:t) [at most one half in
absolute value](hyp:ht), [the normalized Legendre entry is at most the square root of 5 in absolute
value](goal). -/
theorem legendreEntry_abs_le (k : ℕ) (hk : k ≤ 2) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |legendreEntry k t| ≤ Real.sqrt 5 := by
  have hs5 : 1 ≤ Real.sqrt 5 := Real.one_le_sqrt.mpr (by norm_num)
  have hs12_nonneg := Real.sqrt_nonneg 12
  have hs5_nonneg := Real.sqrt_nonneg 5
  have hs12_sq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have hs5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  interval_cases k
  · simp [legendreEntry, Real.one_le_sqrt]
  · simp only [legendreEntry, show ¬ (1 : ℕ) = 0 by omega, ↓reduceIte,
      abs_mul, abs_of_nonneg hs12_nonneg]
    calc
      Real.sqrt 12 * |t| ≤ Real.sqrt 12 * (1 / 2) :=
        mul_le_mul_of_nonneg_left ht hs12_nonneg
      _ ≤ Real.sqrt 5 := by nlinarith
  · have ht2 : t ^ 2 ≤ 1 / 4 := by
      rcases abs_le.mp ht with ⟨htlo, hthi⟩
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - t)
        (by linarith : 0 ≤ 1 / 2 + t)]
    have hp : |6 * t ^ 2 - 1 / 2| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg t]
    simp only [legendreEntry, show ¬ (2 : ℕ) = 0 by omega,
      show ¬ (2 : ℕ) = 1 by omega, ↓reduceIte, abs_mul, abs_of_nonneg hs5_nonneg]
    simpa using mul_le_mul_of_nonneg_left hp hs5_nonneg

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation


module
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Scalar occupancy inequalities

The empty-cell polynomial for any probability vector with at most n entries
has at least n/4 expected repetitions for n at least two. This module isolates
the analytic inequalities from the finite-product probability calculations.
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open scoped BigOperators

variable {κ : Type*} [Fintype κ]

/-- If [the sample size n is at least two](hyp:n,hn), then [the empty-cell probability under the
uniform law on n cells, (1 − 1/n)ⁿ, is at least one quarter](goal).

This is the scalar bottleneck of the occupancy lower bound; it follows from
monotonicity of (1-1/n)^n for n≥2. -/
lemma uniform_empty_probability_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  -- Induct from the exact value at two. The ratio of consecutive bases is
  -- 1 + 1/(m²-1); Bernoulli bounds its m-th power from below.
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hmp : (m : ℝ) + 1 ≠ 0 := by linarith
    have hd : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    have hb : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_iff₀ (by linarith : (0 : ℝ) < m)]
      linarith
    have hbern := one_add_mul_le_pow
      (a := 1 / ((m : ℝ) ^ 2 - 1)) (by
        have hx : (0 : ℝ) ≤ 1 / ((m : ℝ) ^ 2 - 1) := by positivity
        linarith) m
    have hfac : 1 ≤ (1 + (m : ℝ) / ((m : ℝ) ^ 2 - 1)) *
        (1 - 1 / ((m : ℝ) + 1)) := by
      field_simp
      nlinarith
    have hid : 1 - 1 / ((m : ℝ) + 1) =
        (1 - 1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) ^ 2 - 1)) := by
      field_simp
      ring
    have hstep : (1 - 1 / (m : ℝ)) ^ m ≤
        (1 - 1 / ((m : ℝ) + 1)) ^ (m + 1) := by
      rw [pow_succ, hid, mul_pow]
      have hnew : 0 ≤ 1 - 1 / ((m : ℝ) + 1) := by
        rw [sub_nonneg, div_le_iff₀ (by linarith : (0 : ℝ) < m + 1)]
        linarith
      have hmul := mul_le_mul_of_nonneg_right hbern hnew
      have hprod : 1 ≤ (1 + 1 / ((m : ℝ) ^ 2 - 1)) ^ m *
          ((1 - 1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) ^ 2 - 1))) := by
        rw [← hid]
        exact hfac.trans (by simpa only [div_eq_mul_inv, one_mul] using hmul)
      nlinarith [mul_nonneg (pow_nonneg hb m) (sub_nonneg.mpr hprod)]
    exact ih.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hstep)

/-- For [a sample size n](hyp:n) and [a vector q of cell masses](hyp:q), if [n is at least
two](hyp:hn), [there are at most n cells](hyp:hcard), and [the masses are nonnegative](hyp:hq) and
[sum to one](hyp:hsum), then [n minus the sum over cells of 1 − (1 − q)ⁿ — the expected repeat
count — is at least n/4](goal).

Any nonnegative categorical probability vector on at most n cells has
expected repeat-count polynomial at least n/4 when n is at least two.

Apply Jensen for the convex function t↦(1-t)^n. Alternatively pad to n cells
with zeros, apply convexOn_pow to their complements, then use the preceding
uniform_empty_probability_lower. Empty cell types are ruled out by sum q=1,
not by an extra nonemptiness assumption. -/
lemma occupancy_polynomial_lower (n : ℕ) (q : κ → ℝ)
    (hn : 2 ≤ n) (hcard : Fintype.card κ ≤ n)
    (hq : ∀ k, 0 ≤ q k) (hsum : ∑ k, q k = 1) :
    (n : ℝ) / 4 ≤ (n : ℝ) - ∑ k, (1 - (1 - q k) ^ n) := by
  classical
  -- Sum q = 1 excludes the empty type and also bounds each mass by one.
  have hne : Nonempty κ := by
    by_contra h
    have : IsEmpty κ := not_nonempty_iff.mp h
    simp at hsum
  have hq1 (k : κ) : q k ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ k)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hcR : (Fintype.card κ : ℝ) ≤ n := by exact_mod_cast hcard
  -- Give each actual complement weight 1/n. All n-card κ zero masses have
  -- complement one, so combine them into one extra point of weight
  -- (n-card κ)/n. This is precisely Jensen on the zero-padded vector.
  have hw : (n - (Fintype.card κ : ℝ)) / n +
      ∑ k : κ, (1 / (n : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hj := (convexOn_pow (𝕜 := ℝ) n).map_add_sum_le
    (t := Finset.univ) (w := fun _ : κ => 1 / (n : ℝ))
    (p := fun k => 1 - q k) (v := (n - (Fintype.card κ : ℝ)) / n)
    (q := (1 : ℝ)) (fun _ _ => by positivity) (by simpa using hw)
    (fun k _ => show 0 ≤ 1 - q k from sub_nonneg.mpr (hq1 k))
    (div_nonneg (sub_nonneg.mpr hcR) hnR.le) (by simp)
  have havg : (n - (Fintype.card κ : ℝ)) / n +
      ∑ k : κ, (1 / (n : ℝ)) * (1 - q k) = 1 - 1 / n := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
    ring
  simp only [smul_eq_mul, mul_one, one_pow] at hj
  rw [havg, ← Finset.mul_sum] at hj
  have hbound := (uniform_empty_probability_lower n hn).trans hj
  have hscaled := (mul_le_mul_of_nonneg_left hbound hnR.le)
  have hcancel : (n : ℝ) * ((n - (Fintype.card κ : ℝ)) / n +
      1 / (n : ℝ) * ∑ k, (1 - q k) ^ n) =
      n - (Fintype.card κ : ℝ) + ∑ k, (1 - q k) ^ n := by
    field_simp
  rw [hcancel] at hscaled
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  linarith

end Causalean.Stat.Sample.Stratified.TreatmentRegression

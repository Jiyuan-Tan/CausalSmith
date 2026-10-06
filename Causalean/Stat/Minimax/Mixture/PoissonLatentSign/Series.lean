module
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact-linear cell overlap series envelope

A nonnegative coefficient sequence dominated by an exponential series defines
a strictly positive overlap within the small-radius regime. The exponential
power bound retains the exact first coefficient, including at negative overlap.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- The cell overlap series starts at one and sums all positive-order coefficient terms. -/
def overlapSeries (t : ℕ → ℝ) (z : ℝ) : ℝ :=
  1 + ∑' d : ℕ, t (d + 1) * z ^ (d + 1)

/-- An exponential majorant makes the cell overlap series absolutely convergent at every real
  argument. -/
theorem overlapSeries_summable_abs {t : ℕ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (ht : ∀ d, 1 ≤ d → 0 ≤ t d ∧ t d ≤ b ^ d / (d.factorial : ℝ))
    (z : ℝ) : Summable (fun d : ℕ => |t (d + 1) * z ^ (d + 1)|) := by
  have hs := (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (b * |z|))
  refine hs.of_nonneg_of_le (fun _ => abs_nonneg _) (fun d => ?_)
  rw [abs_mul, abs_of_nonneg (ht (d + 1) (by omega)).1, abs_pow]
  calc
    t (d + 1) * |z| ^ (d + 1) ≤
        (b ^ (d + 1) / ((d + 1).factorial : ℝ)) * |z| ^ (d + 1) :=
      mul_le_mul_of_nonneg_right (ht (d + 1) (by omega)).2 (by positivity)
    _ = (b * |z|) ^ (d + 1) / ((d + 1).factorial : ℝ) := by rw [mul_pow]; ring

/-- After removing the exact linear term, the overlap remainder is bounded in
absolute value by the squared exponential radius when that radius is at most one half. -/
theorem overlapSeries_remainder {t : ℕ → ℝ} {b z : ℝ}
    (hb : 0 ≤ b) (ht : ∀ d, 1 ≤ d → 0 ≤ t d ∧ t d ≤ b ^ d / (d.factorial : ℝ))
    (hr : b * |z| ≤ 1 / 2) :
    |overlapSeries t z - 1 - t 1 * z| ≤ b ^ 2 * z ^ 2 := by
  -- The d≥2 tail is at most r² ∑n r^n/(n+2)! ≤ r² for r≤1/2.
  have hsabs := overlapSeries_summable_abs hb ht z
  have hs : Summable (fun d : ℕ => t (d + 1) * z ^ (d + 1)) := by
    exact (by simpa only [Real.norm_eq_abs] using hsabs :
      Summable (fun d : ℕ => ‖t (d + 1) * z ^ (d + 1)‖)).of_norm
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.add_assoc] at hsplit
  have heq : overlapSeries t z - 1 - t 1 * z =
      ∑' d : ℕ, t (d + 2) * z ^ (d + 2) := by
    unfold overlapSeries
    linarith
  rw [heq]
  have htail : Summable (fun d : ℕ => |t (d + 2) * z ^ (d + 2)|) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).2 hsabs
  have hgeom : Summable (fun d : ℕ => (b * |z|) ^ 2 / 2 * (1 / 2 : ℝ) ^ d) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  have hbound : ∀ d : ℕ, |t (d + 2) * z ^ (d + 2)| ≤
      (b * |z|) ^ 2 / 2 * (1 / 2 : ℝ) ^ d := by
    intro d
    have hf : (2 : ℝ) ≤ ((d + 2).factorial : ℝ) := by
      exact_mod_cast (show 2 ≤ (d + 2).factorial from
        by simpa using Nat.factorial_le (show 2 ≤ d + 2 by omega))
    rw [abs_mul, abs_of_nonneg (ht (d + 2) (by omega)).1, abs_pow]
    calc
      t (d + 2) * |z| ^ (d + 2) ≤
          (b ^ (d + 2) / ((d + 2).factorial : ℝ)) * |z| ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (ht (d + 2) (by omega)).2 (by positivity)
      _ = (b * |z|) ^ (d + 2) / ((d + 2).factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ (b * |z|) ^ (d + 2) / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hf
      _ = (b * |z|) ^ 2 / 2 * (b * |z|) ^ d := by rw [pow_add]; ring
      _ ≤ (b * |z|) ^ 2 / 2 * (1 / 2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr d) (by positivity)
  calc
    |∑' d : ℕ, t (d + 2) * z ^ (d + 2)| ≤
        ∑' d : ℕ, |t (d + 2) * z ^ (d + 2)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f := fun d : ℕ => t (d + 2) * z ^ (d + 2))
        (by simpa only [Real.norm_eq_abs] using htail)
    _ ≤ ∑' d : ℕ, (b * |z|) ^ 2 / 2 * (1 / 2 : ℝ) ^ d :=
      htail.tsum_le_tsum hbound hgeom
    _ = b ^ 2 * z ^ 2 := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
      simp only [mul_pow, sq_abs]
      ring

/-- The cell overlap series is strictly positive when the absolute exponential radius is at most
  one half. -/
theorem overlapSeries_pos {t : ℕ → ℝ} {b z : ℝ}
    (hb : 0 ≤ b) (ht : ∀ d, 1 ≤ d → 0 ≤ t d ∧ t d ≤ b ^ d / (d.factorial : ℝ))
    (hr : b * |z| ≤ 1 / 2) : 0 < overlapSeries t z := by
  -- Use the remainder bound and |t₁z|≤r: K≥1-r-r²≥1/4.
  have ht1 := ht 1 (by omega)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at ht1
  have hlin : |t 1 * z| ≤ b * |z| := by
    rw [abs_mul, abs_of_nonneg ht1.1]
    exact mul_le_mul_of_nonneg_right ht1.2 (abs_nonneg z)
  have hrem := (abs_le.mp (overlapSeries_remainder hb ht hr)).1
  have hlinlow := (abs_le.mp hlin).1
  have hr0 : 0 ≤ b * |z| := mul_nonneg hb (abs_nonneg z)
  have hsq : b ^ 2 * z ^ 2 = (b * |z|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [hsq] at hrem
  nlinarith

/-- Given [a nonnegative exponential radius](hyp:hb), [nonnegative coefficients with
the factorial majorant](hyp:ht), [a small absolute radius](hyp:hr), and [a natural
power](hyp:k), [the overlap power is bounded by an exponential retaining its exact
first coefficient](goal). -/
theorem overlapSeries_pow_le_exp {t : ℕ → ℝ} {b z : ℝ}
    (hb : 0 ≤ b) (ht : ∀ d, 1 ≤ d → 0 ≤ t d ∧ t d ≤ b ^ d / (d.factorial : ℝ))
    (hr : b * |z| ≤ 1 / 2) (k : ℕ) :
    overlapSeries t z ^ k ≤
      Real.exp (((k : ℝ) * t 1) * z + (k : ℝ) * b ^ 2 * z ^ 2) := by
  -- K≤1+t₁z+b²z²≤exp(t₁z+b²z²); use positivity before raising to k.
  have hupper := (abs_le.mp (overlapSeries_remainder hb ht hr)).2
  have hexp := Real.add_one_le_exp (t 1 * z + b ^ 2 * z ^ 2)
  have hle : overlapSeries t z ≤ Real.exp (t 1 * z + b ^ 2 * z ^ 2) := by
    linarith
  calc
    overlapSeries t z ^ k ≤ Real.exp (t 1 * z + b ^ 2 * z ^ 2) ^ k :=
      pow_le_pow_left₀ (le_of_lt (overlapSeries_pos hb ht hr)) hle k
    _ = Real.exp (((k : ℝ) * t 1) * z + (k : ℝ) * b ^ 2 * z ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign

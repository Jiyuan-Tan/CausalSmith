module
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic

/-!
# Finite arithmetic-geometric sums

Closed form and uniform bound for the truncated series ∑_{i<N} (i + 2)·zⁱ over the reals.
Multiplying the partial sum by (1 − z)² gives exactly 2 − z − z^N·(N + 2 − (N + 1)·z), valid for
every real z and every N; for 0 ≤ z < 1 this yields ∑_{i<N} (i + 2)·zⁱ ≤ (2 − z)/(1 − z)², the
value of the infinite series, uniformly in N.

## Main results

* `shiftedArithmeticGeometric_sum_identity` — the exact identity for the partial sum times
  (1 − z)².
* `shiftedArithmeticGeometric_sum_le` — the partial sums are at most (2 − z)/(1 − z)² when
  0 ≤ z < 1.
-/

public section

namespace Causalean.Mathlib.Algebra.BigOperators

/-- For [a real ratio](hyp:z) and [a truncation index](hyp:N), multiplying the
finite sum with coefficient `i + 2` by the squared geometric denominator gives
[its exact endpoint-remainder identity](goal). -/
lemma shiftedArithmeticGeometric_sum_identity (z : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 2) * z ^ i) * (1 - z) ^ 2 =
      2 - z - z ^ N * ((N : ℝ) + 2 - ((N : ℝ) + 1) * z) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    push_cast
    ring

/-- For [a nonnegative real ratio below one](hyp:z,hz,hz1) and [a truncation
index](hyp:N), [the finite sum of (i + 2)·zⁱ over i below N is at most
(2 − z)/(1 − z)², the value of the corresponding infinite series](goal). -/
lemma shiftedArithmeticGeometric_sum_le (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 2) * z ^ i) ≤
      (2 - z) / (1 - z) ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - z))).mpr
  rw [shiftedArithmeticGeometric_sum_identity]
  have hr : 0 ≤ (N : ℝ) + 2 - ((N : ℝ) + 1) * z := by
    have h := mul_le_mul_of_nonneg_left hz1.le (show 0 ≤ (N : ℝ) + 1 by positivity)
    linarith
  have := mul_nonneg (pow_nonneg hz N) hr
  linarith

end Causalean.Mathlib.Algebra.BigOperators

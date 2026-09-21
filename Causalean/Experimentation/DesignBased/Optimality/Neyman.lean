/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman optimal allocation

For a two-arm experiment the randomization variance of the difference-in-means estimator, as a
function of the treatment fraction `x ∈ (0,1)`, has the form `A/x + B/(1−x)`. For positive
treated- and control-arm outcome variances, **Neyman allocation** chooses
`x* = √A / (√A + √B) ∈ (0,1)` and minimizes this variance. This file proves the analytic lower
bound and equality identity under nonnegative variances. In the zero-variance boundary cases the
totalized fraction is `0` or `1`, so the proved value comparison does not assert an interior
minimizer.
-/

module
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Neyman allocation

For positive arm variances, Neyman allocation minimizes the two-arm variance proxy by assigning
in proportion to standard deviations. Under merely nonnegative variances, this module's totalized
formula may lie at a boundary point.

The definitions `neymanFraction` and `neymanOptimalValue` package the fraction
`sqrt A / (sqrt A + sqrt B)` and the lower-bound value `(sqrt A + sqrt B)^2`. Theorems
`neyman_allocation_lower_bound`, `neyman_allocation_eq_at_fraction`, and
`neyman_fraction_value_le_on_Ioo` prove the lower bound, show equality at the totalized Neyman
fraction, and compare its value with every point of `(0, 1)`. The separate membership theorem
`neymanFraction_mem_Ioo` requires both variances to be positive.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- For [a first real-valued input](hyp:A) and [a second real-valued input](hyp:B), [the Neyman
allocation fraction](goal) is $\sqrt{A}/(\sqrt{A}+\sqrt{B})$. When the inputs are nonnegative
arm variances, this is the ratio of the treated arm's standard deviation to the sum of the two
arms' standard deviations. -/
noncomputable def neymanFraction (A B : ℝ) : ℝ := Real.sqrt A / (Real.sqrt A + Real.sqrt B)

/-- For [a first real-valued input](hyp:A) and [a second real-valued input](hyp:B), [the Neyman
optimal-value formula](goal) is $(\sqrt{A}+\sqrt{B})^2$. When the inputs are nonnegative arm
variances, this is the squared sum of their standard deviations. -/
noncomputable def neymanOptimalValue (A B : ℝ) : ℝ := (Real.sqrt A + Real.sqrt B) ^ 2

/-- **Neyman allocation lower bound.** For nonnegative arm variances `A, B` and any treatment
fraction `x ∈ (0,1)`, the two-arm variance is at least `(√A + √B)²`. -/
theorem neyman_allocation_lower_bound {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx0 : 0 < x) (hx1 : x < 1) :
    neymanOptimalValue A B ≤ A / x + B / (1 - x) := by
  -- A/x + B/(1−x) − (√A+√B)² = (√(A(1−x)/x) − √(Bx/(1−x)))² ≥ 0  (the cross term √(AB) cancels x).
  unfold neymanOptimalValue
  have hx1' : 0 < 1 - x := sub_pos.mpr hx1
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1xne : 1 - x ≠ 0 := ne_of_gt hx1'
  have hden : 0 < x * (1 - x) := mul_pos hx0 hx1'
  have hcommon : A / x + B / (1 - x) =
      (A * (1 - x) + B * x) / (x * (1 - x)) := by
    field_simp [hxne, h1xne]
  rw [hcommon]
  rw [le_div_iff₀ hden]
  have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt A - (Real.sqrt A + Real.sqrt B) * x)]

/-- The Neyman fraction lies in `(0,1)`. -/
theorem neymanFraction_mem_Ioo {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    0 < neymanFraction A B ∧ neymanFraction A B < 1 := by
  unfold neymanFraction
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  constructor
  · exact div_pos hs (add_pos hs ht)
  · exact (div_lt_one (add_pos hs ht)).2
      (lt_add_of_pos_right (Real.sqrt A) ht)

/-- **Neyman allocation optimum.** For [nonnegative treated-arm and control-arm outcome variances
`A` and `B`](hyp:hA,hB), [evaluating the two-arm variance `A/x + B/(1−x)` at the Neyman fraction
`x* = √A/(√A+√B)` yields exactly its lower bound `(√A + √B)²`](goal). When one variance
is zero, this totalized fraction is a boundary point rather than an element of `(0,1)`. -/
theorem neyman_allocation_eq_at_fraction {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A / neymanFraction A B + B / (1 - neymanFraction A B) = neymanOptimalValue A B := by
  rcases eq_or_lt_of_le hA with rfl | hA
  · simp [neymanFraction, neymanOptimalValue, Real.sq_sqrt hB]
  rcases eq_or_lt_of_le hB with rfl | hB
  · simp [neymanFraction, neymanOptimalValue, Real.sq_sqrt (le_of_lt hA),
      ne_of_gt (Real.sqrt_pos.2 hA)]
  unfold neymanFraction neymanOptimalValue
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsum : Real.sqrt A + Real.sqrt B ≠ 0 := ne_of_gt (add_pos hs ht)
  have hsne : Real.sqrt A ≠ 0 := ne_of_gt hs
  have htne : Real.sqrt B ≠ 0 := ne_of_gt ht
  have hsub : 1 - Real.sqrt A / (Real.sqrt A + Real.sqrt B) =
      Real.sqrt B / (Real.sqrt A + Real.sqrt B) := by
    field_simp [hsum]
    ring
  rw [hsub]
  field_simp [hsum, hsne, htne]
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hA), Real.sq_sqrt (le_of_lt hB)]
  ring

/-- Given [nonnegative arm variances](hyp:hA,hB),
[its value at the totalized fraction is no larger than at every interior fraction](goal).
This comparison does not assert that the Neyman fraction
belongs to `(0,1)` in the zero-variance boundary cases. -/
theorem neyman_fraction_value_le_on_Ioo {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ x, 0 < x → x < 1 →
      A / neymanFraction A B + B / (1 - neymanFraction A B) ≤ A / x + B / (1 - x) := by
  intro x hx0 hx1
  rw [neyman_allocation_eq_at_fraction hA hB]
  exact neyman_allocation_lower_bound hA hB hx0 hx1

end DesignBased
end Experimentation
end Causalean

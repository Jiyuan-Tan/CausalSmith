module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier

/-!
# Distance and character separation on the real circle

The torus distance is the distance to integer multiples of `2π`. These
estimates connect that distance to the denominator in finite Abel summation.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- For [any real angle](hyp:u), [its torus distance is nonnegative and at most π](goal). -/
theorem torusDistance_bounds (u : ℝ) :
    0 ≤ torusDistance u ∧ torusDistance u ≤ Real.pi := by
  let S : Set ℝ := {r | ∃ j : ℤ, r = |u - 2 * Real.pi * j|}
  have hS : S.Nonempty := ⟨|u|, 0, by simp⟩
  have hbelow : BddBelow S := ⟨0, by rintro r ⟨j, rfl⟩; exact abs_nonneg _⟩
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  let j : ℤ := round (u / (2 * Real.pi))
  have hj := abs_sub_round (u / (2 * Real.pi))
  have hdist : |u - 2 * Real.pi * j| ≤ Real.pi := by
    have heq : u - 2 * Real.pi * (j : ℝ) =
        (2 * Real.pi) * (u / (2 * Real.pi) - (j : ℝ)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hp]
    have : (2 * Real.pi) * |u / (2 * Real.pi) - (j : ℝ)| ≤
        (2 * Real.pi) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hj hp.le
    nlinarith
  change 0 ≤ sInf S ∧ sInf S ≤ Real.pi
  constructor
  · exact le_csInf hS (by rintro r ⟨j, rfl⟩; exact abs_nonneg _)
  · exact (csInf_le hbelow ⟨j, rfl⟩).trans hdist

/-- For [a real angle](hyp:u) [of absolute value at most π](hyp:hu), [its torus distance equals its
absolute value](goal). -/
theorem torusDistance_eq_abs (u : ℝ) (hu : |u| ≤ Real.pi) :
    torusDistance u = |u| := by
  let S : Set ℝ := {r | ∃ j : ℤ, r = |u - 2 * Real.pi * j|}
  have hbelow : BddBelow S := ⟨0, by rintro r ⟨j, rfl⟩; exact abs_nonneg _⟩
  have hzero : |u| ∈ S := ⟨0, by simp⟩
  change sInf S = |u|
  apply le_antisymm (csInf_le hbelow hzero)
  apply le_csInf ⟨|u|, hzero⟩
  rintro r ⟨j, rfl⟩
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hu₁ : -Real.pi ≤ u := (abs_le.mp hu).1
  have hu₂ : u ≤ Real.pi := (abs_le.mp hu).2
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt hj)
    have : u + 2 * Real.pi ≤ u - 2 * Real.pi * (j : ℝ) := by nlinarith
    calc
      |u| ≤ Real.pi := hu
      _ ≤ u + 2 * Real.pi := by linarith
      _ ≤ u - 2 * Real.pi * (j : ℝ) := this
      _ ≤ |u - 2 * Real.pi * (j : ℝ)| := le_abs_self _
  · simp [hj]
  · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast (Int.add_one_le_iff.mpr hj)
    have : u - 2 * Real.pi * (j : ℝ) ≤ u - 2 * Real.pi := by nlinarith
    calc
      |u| ≤ Real.pi := hu
      _ ≤ -(u - 2 * Real.pi) := by linarith
      _ ≤ -(u - 2 * Real.pi * (j : ℝ)) := by linarith
      _ ≤ |u - 2 * Real.pi * (j : ℝ)| := neg_le_abs _

/-- For [any real angle u](hyp:u), [2 / π times its torus distance is at most the modulus of the
complex exponential of −i u minus one](goal). -/
theorem character_gap_ge_torusDistance (u : ℝ) :
    2 / Real.pi * torusDistance u ≤
      ‖Complex.exp (-Complex.I * (u : ℂ)) - 1‖ := by
  let j : ℤ := round (u / (2 * Real.pi))
  let v : ℝ := u - 2 * Real.pi * j
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hj := abs_sub_round (u / (2 * Real.pi))
  have hv : |v| ≤ Real.pi := by
    have heq : v = (2 * Real.pi) * (u / (2 * Real.pi) - (j : ℝ)) := by
      dsimp [v]
      field_simp
    rw [heq, abs_mul, abs_of_pos hp]
    have := mul_le_mul_of_nonneg_left hj hp.le
    nlinarith
  have hdist : torusDistance u ≤ |v| := by
    apply csInf_le
    · exact ⟨0, by rintro r ⟨k, rfl⟩; exact abs_nonneg _⟩
    · exact ⟨j, rfl⟩
  have hhalf : |v / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hv (by norm_num)
  have hs := Real.mul_abs_le_abs_sin hhalf
  have hsin : 2 / Real.pi * |v| ≤ 2 * |Real.sin (v / 2)| := by
    have heq : |v / 2| = |v| / 2 := by norm_num [abs_div]
    rw [heq] at hs
    nlinarith
  have hperiod : Complex.exp (-Complex.I * (u : ℂ)) =
      Complex.exp (Complex.I * ((-v : ℝ) : ℂ)) := by
    have hshift : (-Complex.I * (u : ℂ)) =
        Complex.I * ((-v : ℝ) : ℂ) + ((-j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [v]
      push_cast
      ring
    rw [hshift, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hperiod, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hnorm : ‖(2 : ℝ) * Real.sin (-v / 2)‖ = 2 * |Real.sin (v / 2)| := by
    rw [neg_div, Real.sin_neg, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_neg]
  rw [hnorm]
  have hpos : 0 ≤ 2 / Real.pi := by positivity
  exact (mul_le_mul_of_nonneg_left hdist hpos).trans hsin

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson


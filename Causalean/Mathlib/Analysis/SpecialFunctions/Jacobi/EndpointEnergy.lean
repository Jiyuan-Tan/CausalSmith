module
public import Mathlib

/-!
# Endpoint comparison for a single change of derivative sign

An energy whose derivative is a nonnegative multiple of an affine function
starting nonpositive cannot exceed both endpoint energies.  This calculus
lemma isolates the monotonicity argument used for Jacobi differential
equations and applies to other second-order equations as well.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

/-- An [energy function](hyp:E), [left affine coefficient](hyp:A), [right affine coefficient](hyp:B), and [point in the unit interval](hyp:x,hx), when [the left coefficient is nonnegative](hyp:hA), [the energy is continuous on the unit interval](hyp:hE), [it is differentiable in the interior](hyp:hd), and [its derivative has the stated one-sign-change form](hyp:hder), give [an energy no larger than the greater endpoint energy](goal).

A continuous energy on `[0,1]` is at most its larger endpoint value when
its interior derivative is a nonnegative multiple of `-A + B x`, with `A ≥ 0`.
The affine factor can change sign only from negative to positive, so the
energy first decreases and then increases. -/
theorem affine_deriv_energy_le_max (E : ℝ → ℝ) (A B x : ℝ)
    (hA : 0 ≤ A) (hE : ContinuousOn E (Set.Icc (0 : ℝ) 1))
    (hd : ∀ y ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ E y)
    (hder : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      ∃ q : ℝ, 0 ≤ q ∧ deriv E y = (-A + B * y) * q)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    E x ≤ max (E 0) (E 1) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases le_or_gt B 0 with hB | hB
  · have hmono : AntitoneOn E (Set.Icc (0 : ℝ) 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hE
        (by
          rw [interior_Icc]
          intro y hy
          exact (hd y hy).differentiableWithinAt)
        (by
          rw [interior_Icc]
          intro y hy
          obtain ⟨q, hq, hqder⟩ := hder y hy
          rw [hqder]
          apply mul_nonpos_of_nonpos_of_nonneg _ hq
          nlinarith [hy.1])
    exact le_trans (hmono ⟨by norm_num, by norm_num⟩ ⟨hx0, hx1⟩ hx0)
      (le_max_left _ _)
  · by_cases hcut : x ≤ A / B
    · have hBx : B * x ≤ A := by
        have := (le_div_iff₀ hB).mp hcut
        nlinarith
      have hmono : AntitoneOn E (Set.Icc (0 : ℝ) x) :=
        antitoneOn_of_deriv_nonpos (convex_Icc 0 x)
          (hE.mono (by intro y hy; exact ⟨hy.1, le_trans hy.2 hx1⟩))
          (by
            rw [interior_Icc]
            intro y hy
            exact (hd y ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩).differentiableWithinAt)
          (by
            rw [interior_Icc]
            intro y hy
            obtain ⟨q, hq, hqder⟩ := hder y ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩
            rw [hqder]
            apply mul_nonpos_of_nonpos_of_nonneg _ hq
            nlinarith [mul_le_mul_of_nonneg_left hy.2.le hB.le])
      exact le_trans (hmono ⟨le_refl _, hx0⟩ ⟨hx0, le_refl _⟩ hx0)
        (le_max_left _ _)
    · have hBx : A < B * x := by
        have := (div_lt_iff₀ hB).mp (lt_of_not_ge hcut)
        nlinarith
      have hmono : MonotoneOn E (Set.Icc x 1) :=
        monotoneOn_of_deriv_nonneg (convex_Icc x 1)
          (hE.mono (by intro y hy; exact ⟨le_trans hx0 hy.1, hy.2⟩))
          (by
            rw [interior_Icc]
            intro y hy
            exact (hd y ⟨lt_of_le_of_lt hx0 hy.1, hy.2⟩).differentiableWithinAt)
          (by
            rw [interior_Icc]
            intro y hy
            obtain ⟨q, hq, hqder⟩ := hder y ⟨lt_of_le_of_lt hx0 hy.1, hy.2⟩
            rw [hqder]
            apply mul_nonneg
            · nlinarith [mul_le_mul_of_nonneg_left hy.1.le hB.le]
            · exact hq)
      exact le_trans (hmono ⟨le_refl _, hx1⟩ ⟨hx1, le_refl _⟩ hx1)
        (le_max_right _ _)

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

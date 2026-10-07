module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigPoly
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Finite cosine expansion of even periodic convolution

Separate the change of integration window, removal of sine modes, and explicit
convolution coefficients before attempting Jackson span membership. These are
generic angular statements independent of the target's Hölder regularity and of
the numerical Jackson moment bounds.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Analysis.BernsteinSzegoTrig
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- [Angular convolution](goal) of a [target](hyp:g) and [kernel](hyp:h)
at an [angle](hyp:θ) integrates their translated product over the principal period. -/
def angularConvolution (g h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in Set.Icc (-Real.pi) Real.pi, g (θ - t) * h t

/-- Two [periodic functions](hyp:hgper,hhper) satisfy
[the reversed angular convolution formula](goal) at every [angle](hyp:θ).

Substitute t ↦ θ-t, then use invariance of the integral of a continuous
2π-periodic product over an interval of length 2π. Convert Icc to the usual
half-open or interval integral before applying the Mathlib periodic theorem.
Search confirmed `intervalIntegral.integral_comp_sub_left` and
`Function.Periodic.intervalIntegral_add_eq` provide the required two bridges;
the latter needs no integrability premise.
-/
theorem angularConvolution_reverse {g h : ℝ → ℝ}
    (hgper : Function.Periodic g (2 * Real.pi))
    (hhper : Function.Periodic h (2 * Real.pi)) (θ : ℝ) :
    angularConvolution g h θ =
      ∫ t in Set.Icc (-Real.pi) Real.pi, g t * h (θ - t) := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp only [angularConvolution, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  let f : ℝ → ℝ := fun t => g t * h (θ - t)
  have hfper : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp [f]
    rw [hgper t]
    have ht : θ - (t + 2 * Real.pi) = (θ - t) - 2 * Real.pi := by ring
    rw [ht, hhper.sub_eq]
  have hcomp : (fun t => g (θ - t) * h t) = (fun t => f (θ - t)) := by
    funext t
    simp [f]
  rw [hcomp, intervalIntegral.integral_comp_sub_left]
  have hp := hfper.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi)
  convert hp using 1 <;> congr 1 <;> ring

/-- An [even real trigonometric polynomial](hyp:hh,heven) has
[a finite expansion using only cosine modes, with the same degree bound](goal).

Average the given expansion at t and -t. The sine terms cancel and the cosine
terms remain; no Fourier uniqueness or orthogonality theorem is needed.
-/
theorem even_trigPoly_cosine {n : ℕ} {h : ℝ → ℝ}
    (hh : IsTrigPolyLE n h) (heven : Function.Even h) :
    ∃ a : ℕ → ℝ, ∀ t : ℝ,
      h t = ∑ j ∈ Finset.range (n + 1), a j * Real.cos ((j : ℝ) * t) := by
  classical
  rcases hh with ⟨a, b, hh⟩
  refine ⟨a, fun t => ?_⟩
  have ht := hh t
  have hnt := hh (-t)
  rw [heven t] at hnt
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, mul_neg] at hnt
  have havg : h t + h t =
      ∑ j ∈ Finset.range (n + 1), 2 * (a j * Real.cos ((j : ℝ) * t)) := by
    nth_rw 1 [ht]
    rw [hnt, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← Finset.mul_sum] at havg
  linarith

/-- A [continuous even periodic target](hyp:hg,hgeven,hgper) convolved
with a [finite cosine kernel](hyp:hexp) has [the explicit cosine expansion
obtained by multiplying kernel coefficients by target cosine integrals](goal),
at every [angle](hyp:θ).

Apply the reversed formula, expand `cos_sub`, and integrate the finite sum.
The sine integrals vanish because the target is even and the period is symmetric.
Continuity and periodicity of the finite cosine kernel follow from its expansion.
-/
theorem angularConvolution_cosine_expansion {n : ℕ} {g h : ℝ → ℝ}
    (hg : Continuous g) (hgeven : Function.Even g)
    (hgper : Function.Periodic g (2 * Real.pi)) (a : ℕ → ℝ)
    (hexp : ∀ t : ℝ,
      h t = ∑ j ∈ Finset.range (n + 1), a j * Real.cos ((j : ℝ) * t)) (θ : ℝ) :
    angularConvolution g h θ =
      ∑ j ∈ Finset.range (n + 1),
        (a j * ∫ t in Set.Icc (-Real.pi) Real.pi, g t * Real.cos ((j : ℝ) * t)) *
          Real.cos ((j : ℝ) * θ) := by
  classical
  have hh : Continuous h := by
    have heq : h = fun t => ∑ j ∈ Finset.range (n + 1),
        a j * Real.cos ((j : ℝ) * t) := funext hexp
    rw [heq]
    fun_prop
  have hhper : Function.Periodic h (2 * Real.pi) := by
    intro t
    rw [hexp, hexp]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_add, Real.cos_add_nat_mul_two_pi]
  rw [angularConvolution_reverse hgper hhper θ]
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hsine (j : ℕ) :
      (∫ t in -Real.pi..Real.pi, g t * Real.sin ((j : ℝ) * t)) = 0 := by
    have href := intervalIntegral.integral_comp_neg
      (a := -Real.pi) (b := Real.pi)
      (fun t => g t * Real.sin ((j : ℝ) * t))
    simp only [show ∀ t, g (-t) = g t from hgeven, mul_neg, Real.sin_neg, mul_neg,
      intervalIntegral.integral_neg, neg_neg] at href
    linarith
  have hfun : (fun t => g t * h (θ - t)) =
      (fun t => ∑ j ∈ Finset.range (n + 1),
        (a j * (g t * Real.cos ((j : ℝ) * t)) * Real.cos ((j : ℝ) * θ) +
        a j * (g t * Real.sin ((j : ℝ) * t)) * Real.sin ((j : ℝ) * θ))) := by
    funext t
    rw [hexp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_sub, Real.cos_sub]
    ring
  rw [hfun, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul, hsine, mul_zero, zero_mul, add_zero]
    · exact (show Continuous (fun t =>
        a j * (g t * Real.cos ((j : ℝ) * t)) * Real.cos ((j : ℝ) * θ)) by
          fun_prop).intervalIntegrable _ _
    · exact (show Continuous (fun t =>
        a j * (g t * Real.sin ((j : ℝ) * t)) * Real.sin ((j : ℝ) * θ)) by
          fun_prop).intervalIntegrable _ _
  · intro j hj
    exact (show Continuous (fun t =>
        a j * (g t * Real.cos ((j : ℝ) * t)) * Real.cos ((j : ℝ) * θ) +
        a j * (g t * Real.sin ((j : ℝ) * t)) * Real.sin ((j : ℝ) * θ)) by
          fun_prop).intervalIntegrable _ _

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection


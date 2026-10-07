/-
Copyright (c) 2026 CausalSmith contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rectangular derivative remainders

This module gives a one-dimensional quadratic remainder bound with constant one half from
explicit derivative witnesses and its iterated two-coordinate consequence. The latter converts a
uniform mixed fourth-derivative envelope into a rectangular fourth-order bound.
-/
public section
noncomputable section
open Set
namespace Causalean.Mathlib.Analysis.Calculus

/-- Let f be a real function with [derivative f₁](hyp:hf) and [second derivative f₂](hyp:hf₁)
at every point of the interval from 0 to [a nonnegative endpoint a](hyp:ha). If [f₂ is bounded
in absolute value by B on that interval](hyp:hf₂), and both [f](hyp:h0) and [f₁](hyp:h10) vanish
at 0, then [the value of f at a is at most B·a²/2 in absolute value](goal).

The proof compares f with the quadratic functions ±B·x²/2. -/
lemma quadratic_remainder_bound (f f₁ f₂ : ℝ → ℝ) (a B : ℝ)
    (ha : 0 ≤ a) (hf : ∀ x ∈ Icc 0 a, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Icc 0 a, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Icc 0 a, |f₂ x| ≤ B) (h0 : f 0 = 0) (h10 : f₁ 0 = 0) :
    |f a| ≤ B*a^2/2 := by
  have hfirst (x : ℝ) (hx : x ∈ Icc 0 a) : |f₁ x| ≤ B*x := by
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hf₁ t ht).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hf₂ t ht)
      (convex_Icc 0 a) (left_mem_Icc.mpr ha) hx
    simpa only [Real.norm_eq_abs, h10, sub_zero, abs_of_nonneg hx.1] using hm
  have hderiv (s : ℝ) (hs : |s| = 1) (x : ℝ) (hx : x ∈ Icc 0 a) :
      HasDerivAt (fun t => B*t^2/2+s*f t) (B*x+s*f₁ x) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul B).div_const 2).add
      ((hf x hx).const_mul s) using 1 <;>
      first | rfl | (simp [id]; ring)
  have hmono (s : ℝ) (hs : |s| = 1) :
      MonotoneOn (fun t => B*t^2/2+s*f t) (Icc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a)
    · exact fun x hx => (hderiv s hs x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv s hs x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hbound := hfirst x (interior_subset hx)
      have habs : |s*f₁ x| ≤ B*x := by simpa only [abs_mul, hs, one_mul] using hbound
      linarith [(abs_le.mp habs).1]
  have hp := hmono 1 (by norm_num) (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
  have hn := hmono (-1) (by norm_num) (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
  simp only [h0, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
    one_mul, neg_one_mul] at hp hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Let F be a real function of two real variables and fix [nonnegative amplitudes a and
u](hyp:ha,hu). Suppose that, at the second argument u, [F has partial derivative Fa in its first
argument](hyp:hFa) and [Fa has partial derivative Faa in its first argument](hyp:hFaa) at every
point of the interval from 0 to a; that on the rectangle 0 ≤ b ≤ a, 0 ≤ v ≤ u [Faa has partial
derivative FaaU in its second argument](hyp:hFaaU), [FaaU has partial derivative FaaUU in its
second argument](hyp:hFaaUU), and [FaaUU is bounded in absolute value by B](hyp:hbound); and that
[F](hyp:hF0) and [Fa](hyp:hFa0) vanish at the point (0, u), while [Faa](hyp:hFaa0) and
[FaaU](hyp:hFaaU0) vanish at (b, 0) for every b between 0 and a. Then [the value of F at (a, u)
is at most B·a²·u²/4 in absolute value](goal).

The bound is the quadratic remainder applied once in each amplitude. All derivative witnesses
are explicit inputs. -/
lemma fourth_rectangular_remainder_bound
    (F Fa Faa FaaU FaaUU : ℝ → ℝ → ℝ) (a u B : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hFa : ∀ b ∈ Icc 0 a, HasDerivAt (fun t => F t u) (Fa b u) b)
    (hFaa : ∀ b ∈ Icc 0 a, HasDerivAt (fun t => Fa t u) (Faa b u) b)
    (hFaaU : ∀ b ∈ Icc 0 a, ∀ v ∈ Icc 0 u,
      HasDerivAt (Faa b) (FaaU b v) v)
    (hFaaUU : ∀ b ∈ Icc 0 a, ∀ v ∈ Icc 0 u,
      HasDerivAt (FaaU b) (FaaUU b v) v)
    (hbound : ∀ b ∈ Icc 0 a, ∀ v ∈ Icc 0 u, |FaaUU b v| ≤ B)
    (hF0 : F 0 u = 0) (hFa0 : Fa 0 u = 0)
    (hFaa0 : ∀ b ∈ Icc 0 a, Faa b 0 = 0)
    (hFaaU0 : ∀ b ∈ Icc 0 a, FaaU b 0 = 0) :
    |F a u| ≤ B*a^2*u^2/4 := by
  have hcurv (b : ℝ) (hb : b ∈ Icc 0 a) : |Faa b u| ≤ B*u^2/2 :=
    quadratic_remainder_bound (Faa b) (FaaU b) (FaaUU b) u B hu
      (hFaaU b hb) (hFaaUU b hb) (hbound b hb) (hFaa0 b hb) (hFaaU0 b hb)
  have hr := quadratic_remainder_bound (fun b => F b u)
    (fun b => Fa b u) (fun b => Faa b u) a (B*u^2/2) ha hFa hFaa hcurv hF0 hFa0
  calc
    _ ≤ (B*u^2/2)*a^2/2 := hr
    _ = _ := by ring

end Causalean.Mathlib.Analysis.Calculus

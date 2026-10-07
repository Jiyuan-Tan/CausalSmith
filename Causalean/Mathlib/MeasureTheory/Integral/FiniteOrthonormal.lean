/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Ring

/-!
# Finite orthonormal expansions under a measure

This file gives the raw-integral Pythagorean identity for the projection of a square-integrable
real function onto a finite orthonormal family. It avoids requiring callers to package the
functions as vectors in an abstract Hilbert space.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.MeasureTheory

/-- For [a measure](hyp:μ), [a common diagonal energy](hyp:A),
[a finite family of real functions](hyp:f), and [real coefficients](hyp:c), if
[every pairwise product is integrable](hyp:hi) and [the pairwise integrals equal the common
energy on the diagonal and vanish off it](hyp:ho), then [the integral of the square of the finite
linear combination is the common energy times the sum of squared coefficients](goal). -/
theorem finite_diagonal_square_integral {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℝ) (f : ι → Ω → ℝ) (c : ι → ℝ)
    (hi : ∀ a b, Integrable (fun x => f a x * f b x) μ)
    (ho : ∀ a b, (∫ x, f a x * f b x ∂μ) = if a = b then A else 0) :
    (∫ x, (∑ a, c a * f a x) ^ 2 ∂μ) = A * ∑ a, c a ^ 2 := by
  classical
  have he (x : Ω) : (∑ a, c a * f a x) ^ 2 =
      ∑ a, ∑ b, (c a * c b) * (f a x * f b x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => (hi a b).const_mul _))]
  simp_rw [integral_finsetSum _ (fun b _ => (hi _ b).const_mul _), integral_const_mul, ho]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Given [a measurable space](hyp:Ω), [a finite index type](hyp:ι), [a measure](hyp:μ),
[a finite family of real functions](hyp:b), [square integrability of every family
member](hyp:hb), [orthonormality through their raw integrals](hyp:hortho), [a target
function](hyp:f), and [its square integrability](hyp:hf), [the integral of the target's square splits
into the integral of the square of its finite orthonormal projection plus the integral of the
square of the residual](goal). -/
theorem finite_orthonormal_pythagoras {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (b : ι → Ω → ℝ) (hb : ∀ i, MemLp (b i) 2 μ)
    (hortho : ∀ i j, (∫ x, b i x * b j x ∂μ) = if i = j then 1 else 0)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    let g := fun x => ∑ i, b i x * (∫ y, b i y * f y ∂μ)
    (∫ x, f x^2 ∂μ) = (∫ x, g x^2 ∂μ) + (∫ x, (f x-g x)^2 ∂μ) := by
  classical
  let c := fun i => ∫ y, b i y * f y ∂μ
  let g := fun x => ∑ i, b i x * c i
  change (∫ x, f x^2 ∂μ) = (∫ x, g x^2 ∂μ) + (∫ x, (f x-g x)^2 ∂μ)
  have hg : MemLp g 2 μ := memLp_finsetSum _ (fun i _ => (hb i).mul_const (c i))
  have hgb (j : ι) : (∫ x, g x * b j x ∂μ) = c j := by
    simp only [g, Finset.sum_mul]
    simp_rw [show ∀ i x, b i x * c i * b j x = (b i x * b j x) * c i by intros; ring]
    rw [integral_finsetSum (f := fun i x => (b i x * b j x) * c i) Finset.univ
      (fun i _ => ((hb i).integrable_mul (hb j)).mul_const (c i))]
    simp_rw [integral_mul_const, hortho]
    simp
  have hfg : (∫ x, f x * g x ∂μ) = ∑ i, c i^2 := by
    simp only [g, Finset.mul_sum]
    simp_rw [show ∀ i x, f x * (b i x * c i) = (b i x * f x) * c i by intros; ring]
    rw [integral_finsetSum (f := fun i x => (b i x * f x) * c i) Finset.univ
      (fun i _ => ((hb i).integrable_mul hf).mul_const (c i))]
    simp_rw [integral_mul_const]
    change (∑ i, c i * c i) = ∑ i, c i^2
    simp only [pow_two]
  have hgg : (∫ x, g x^2 ∂μ) = ∑ i, c i^2 := by
    simp_rw [pow_two]
    conv_lhs => arg 2; ext x; rhs; change ∑ i, b i x * c i
    simp_rw [Finset.mul_sum]
    simp_rw [show ∀ i x, g x * (b i x * c i) = (g x * b i x) * c i by intros; ring]
    rw [integral_finsetSum (f := fun i x => (g x * b i x) * c i) Finset.univ
      (fun i _ => (hg.integrable_mul (hb i)).mul_const (c i))]
    simp_rw [integral_mul_const, hgb]
  have hres : (∫ x, (f x-g x)^2 ∂μ) =
      (∫ x, f x^2 ∂μ) - 2*(∫ x, f x*g x ∂μ) + (∫ x, g x^2 ∂μ) := by
    simp_rw [show ∀ x, (f x-g x)^2 = f x^2 - 2*(f x*g x) + g x^2 by intro x; ring]
    have hprod : Integrable (fun x => f x*g x) μ := hf.integrable_mul hg
    have hsub : Integrable (fun x => f x^2 - 2*(f x*g x)) μ :=
      hf.integrable_sq.sub (hprod.const_mul 2)
    rw [integral_add hsub hg.integrable_sq,
      integral_sub hf.integrable_sq (hprod.const_mul 2), integral_const_mul]
  rw [hres, hfg, hgg]
  ring

end Causalean.Mathlib.MeasureTheory

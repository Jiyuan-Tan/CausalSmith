module
public import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.GaussianFeature
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Gaussian-weighted polynomial moments

This module develops the finite algebraic layer between coordinate integrals
of the explicit Gaussian feature map and polynomial test functions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Polynomial

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- The Gaussian weight used by the explicit feature coordinates. -/
def gaussianWeight (r : ℝ) : ℝ := Real.exp (-r ^ 2)

/-- The Gaussian weight multiplied by the raw monomial of degree `m`. -/
def gaussianWeightedMonomial (m : ℕ) (r : ℝ) : ℝ :=
  gaussianWeight r * r ^ m

/-- Every Gaussian-weighted monomial is integrable under every finite real measure. -/
lemma integrable_gaussianWeightedMonomial (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℕ) :
    Integrable (gaussianWeightedMonomial m) μ := by
  let f : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toFun := gaussianWeightedMonomial m
      continuous_toFun := by
        unfold gaussianWeightedMonomial gaussianWeight
        fun_prop
      zero_at_infty' := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
          (a := (1 : ℝ)) (by positivity) (m : ℝ)
        have h' : Tendsto (fun x : ℝ => |x| ^ m * Real.exp (-1 * x ^ 2))
            (cocompact ℝ) (nhds 0) := by
          simpa only [Real.rpow_natCast] using h
        convert h' using 1
        simp [gaussianWeightedMonomial, gaussianWeight, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), mul_comm] }
  exact f.toBCF.integrable μ

private lemma integrable_gaussianWeightedPolynomial
    (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ[X]) :
    Integrable (fun r => gaussianWeight r * p.eval r) μ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have h : Integrable (fun r => gaussianWeight r * p.eval r +
          gaussianWeight r * q.eval r) μ := hp.add hq
      simpa only [Polynomial.eval_add, mul_add] using h
  | monomial n a =>
      have h := (integrable_gaussianWeightedMonomial μ n).const_mul a
      convert h using 1
      funext r
      simp only [Polynomial.eval_monomial, gaussianWeightedMonomial]
      ring

/-- Equality of all Gaussian-weighted monomial integrals implies equality against every
Gaussian-weighted polynomial. -/
lemma gaussianWeightedPolynomial_integral_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ m : ℕ,
      ∫ r, gaussianWeightedMonomial m r ∂μ =
        ∫ r, gaussianWeightedMonomial m r ∂ν)
    (p : ℝ[X]) :
    ∫ r, gaussianWeight r * p.eval r ∂μ =
      ∫ r, gaussianWeight r * p.eval r ∂ν := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hpμ := integrable_gaussianWeightedPolynomial μ p
      have hqμ := integrable_gaussianWeightedPolynomial μ q
      have hpν := integrable_gaussianWeightedPolynomial ν p
      have hqν := integrable_gaussianWeightedPolynomial ν q
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add hpμ hqμ, integral_add hpν hqν, hp, hq]
  | monomial n a =>
      have hfun :
          (fun r : ℝ => gaussianWeight r * ((Polynomial.monomial n a).eval r)) =
            fun r => a * gaussianWeightedMonomial n r := by
        funext r
        simp only [Polynomial.eval_monomial, gaussianWeightedMonomial]
        ring
      rw [hfun, integral_const_mul, integral_const_mul, hmom n]

end CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

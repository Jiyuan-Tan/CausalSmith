/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic

/-!
# Gaussian mean embeddings on bounded real supports

This module gives an explicit real Hilbert-space feature map for the Gaussian
kernel and proves that its Bochner mean embedding distinguishes finite measures
with a common bounded real support.  It exposes coordinate integration,
Gaussian-weighted moment recovery, equality of measures and second moments, and
the resulting strict norm separation.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal InnerProductSpace lp Polynomial

noncomputable section

namespace Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-- Given [two real inputs](hyp:a,b), the [Gaussian kernel](goal) is the exponential of their
negative squared difference [as specified by the displayed formula](step:1). -/
def gaussianKernel (a b : ℝ) : ℝ :=
  Real.exp (-(a - b) ^ 2)

/-- Given [a real Hilbert space](hyp:H), a [unit-norm Gaussian feature map](goal) consists of an
input-to-vector assignment [given by the feature-vector field](step:1), a unit-norm certificate
[given by the norm field](step:2), and a Gaussian inner-product identity [given by the
kernel-representation field](step:3). -/
structure UnitNormGaussianFeatureMap (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  feature : ℝ → H
  norm_eq_one : ∀ r, ‖feature r‖ = 1
  inner_eq_kernel : ∀ a b, ⟪feature a, feature b⟫_ℝ = gaussianKernel a b

/-- Given [a natural-number coordinate](hyp:m), its [Gaussian feature normalization](goal) is
the positive square-root factor [specified by the displayed formula](step:1). -/
def gaussianFeatureNormalization (m : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ m / m.factorial)

/-- For [every natural-number coordinate](hyp:m), [its Gaussian feature normalization is
strictly positive](goal). -/
lemma gaussianFeatureNormalization_pos (m : ℕ) :
    0 < gaussianFeatureNormalization m := by
  unfold gaussianFeatureNormalization
  positivity

/-- Given [a real input](hyp:r) and [a natural-number coordinate](hyp:m), the [explicit Gaussian
feature coefficient](goal) is the normalized exponentially weighted monomial [specified by the
displayed formula](step:1). -/
def gaussianFeatureCoefficient (r : ℝ) (m : ℕ) : ℝ :=
  gaussianFeatureNormalization m * Real.exp (-r ^ 2) * r ^ m

/-- For [every real input](hyp:r), [the sequence of explicit Gaussian feature coefficients is
square-summable](goal). -/
lemma gaussianFeature_memℓp (r : ℝ) :
    Memℓp (gaussianFeatureCoefficient r) 2 := by
  apply memℓp_gen
  norm_num
  simp only [gaussianFeatureCoefficient, gaussianFeatureNormalization]
  have hs : Summable (fun m : ℕ => (2 * r ^ 2) ^ m / m.factorial) :=
    Real.summable_pow_div_factorial _
  apply (hs.mul_left (Real.exp (-r ^ 2) ^ 2)).congr
  intro m
  have hnonneg : 0 ≤ (2 : ℝ) ^ m / m.factorial := by positivity
  calc
    _ = Real.exp (-r ^ 2) ^ 2 * ((2 : ℝ) ^ m / m.factorial) *
        r ^ (2 * m) := by ring
    _ = (Real.sqrt ((2 : ℝ) ^ m / m.factorial)) ^ 2 *
        Real.exp (-r ^ 2) ^ 2 * r ^ (2 * m) := by
          rw [Real.sq_sqrt hnonneg]
          ac_rfl
    _ = _ := by ring

/-- The [Gaussian Hilbert space](goal) is the complete real square-summable sequence space
[given by sequences indexed by nonnegative integers](step:1). -/
abbrev GaussianHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Given [a real input](hyp:r), the [explicit Gaussian feature vector](goal) is its
square-summable coefficient sequence [given by the preceding coefficients and their
square-summability certificate](step:1). -/
def gaussianFeature (r : ℝ) : GaussianHilbert :=
  ⟨gaussianFeatureCoefficient r, gaussianFeature_memℓp r⟩

/-- For [two real inputs](hyp:a,b), [the inner product of their explicit Gaussian feature
vectors equals the Gaussian kernel](goal). -/
lemma gaussianFeature_inner (a b : ℝ) :
    ⟪gaussianFeature a, gaussianFeature b⟫_ℝ = gaussianKernel a b := by
  rw [lp.inner_eq_tsum]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  change (∑' m : ℕ, gaussianFeatureCoefficient b m *
    gaussianFeatureCoefficient a m) = _
  have hterm : (fun m : ℕ => gaussianFeatureCoefficient b m *
      gaussianFeatureCoefficient a m) =
      fun m => (Real.exp (-a ^ 2) * Real.exp (-b ^ 2)) *
        ((2 * a * b) ^ m / m.factorial) := by
    funext m
    unfold gaussianFeatureCoefficient gaussianFeatureNormalization
    have hnonneg : 0 ≤ (2 : ℝ) ^ m / m.factorial := by positivity
    have hsqrt := Real.mul_self_sqrt hnonneg
    calc
      _ = (Real.sqrt ((2 : ℝ) ^ m / m.factorial) *
            Real.sqrt ((2 : ℝ) ^ m / m.factorial)) *
          (Real.exp (-a ^ 2) * Real.exp (-b ^ 2)) *
          (a ^ m * b ^ m) := by ring
      _ = _ := by rw [hsqrt]; ring
  rw [hterm, tsum_mul_left,
    (NormedSpace.expSeries_div_hasSum_exp (2 * a * b)).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add, ← Real.exp_add]
  unfold gaussianKernel
  congr 1
  ring

/-- For [every real input](hyp:r), [its explicit Gaussian feature vector has norm one](goal). -/
lemma gaussianFeature_norm (r : ℝ) : ‖gaussianFeature r‖ = 1 := by
  have hsq : ‖gaussianFeature r‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, gaussianFeature_inner]
    simp [gaussianKernel]
  nlinarith [norm_nonneg (gaussianFeature r)]

/-- The [explicit unit-norm Gaussian feature realization](goal) is [given by the weighted
monomial feature vector, its unit norm, and its Gaussian inner-product identity](step:1). -/
def gaussianFeatureMap : UnitNormGaussianFeatureMap GaussianHilbert where
  feature := gaussianFeature
  norm_eq_one := gaussianFeature_norm
  inner_eq_kernel := gaussianFeature_inner

private lemma UnitNormGaussianFeatureMap.dist_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : UnitNormGaussianFeatureMap H) (a b : ℝ) :
    ‖U.feature a - U.feature b‖ ^ 2 = 2 - 2 * gaussianKernel a b := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, U.inner_eq_kernel]
  simp only [gaussianKernel, sub_self]
  ring_nf
  simp

/-- Given [a unit-norm Gaussian feature realization](hyp:U), [its feature map is continuous on
the real line](goal). -/
lemma UnitNormGaussianFeatureMap.continuous {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (U : UnitNormGaussianFeatureMap H) :
    Continuous U.feature := by
  rw [continuous_iff_continuousAt]
  intro a
  change Tendsto U.feature (nhds a) (nhds (U.feature a))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : Tendsto (fun b : ℝ => ‖U.feature b - U.feature a‖ ^ 2)
      (nhds a) (nhds 0) := by
    have h : ContinuousAt (fun b : ℝ => 2 - 2 * gaussianKernel b a) a := by
      unfold gaussianKernel
      fun_prop
    have heq : (fun b : ℝ => ‖U.feature b - U.feature a‖ ^ 2) =
        fun b => 2 - 2 * gaussianKernel b a := by
      funext b
      exact U.dist_sq b a
    rw [heq]
    change Tendsto (fun b : ℝ => 2 - 2 * gaussianKernel b a) (nhds a)
      (nhds ((fun b : ℝ => 2 - 2 * gaussianKernel b a) a)) at h
    simpa [gaussianKernel] using h
  have hev : ∀ᶠ b in nhds a, ‖U.feature b - U.feature a‖ ^ 2 < ε ^ 2 :=
    (tendsto_order.1 hcont).2 _ (sq_pos_of_pos hε)
  filter_upwards [hev] with b hb
  rw [dist_eq_norm]
  have hnonneg := norm_nonneg (U.feature b - U.feature a)
  nlinarith

/-- Given [a complete real Hilbert space and its unit-norm Gaussian feature realization](hyp:U)
and [a finite real measure](hyp:μ), [the feature map is Bochner-integrable](goal). -/
lemma UnitNormGaussianFeatureMap.integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable U.feature μ := by
  exact Integrable.of_bound U.continuous.stronglyMeasurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun r => by rw [U.norm_eq_one])

/-- Given [a complete real Hilbert-space Gaussian feature realization](hyp:U) and [a real
measure](hyp:μ), its [Gaussian mean embedding](goal) is [given by the Bochner integral of the
feature map](step:1). -/
def meanEmbedding {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) : H :=
  ∫ r, U.feature r ∂μ

/-- Given [a natural-number coordinate](hyp:m), the [continuous Gaussian coordinate evaluation](goal)
is [given by evaluation in the real square-summable sequence space](step:1). -/
def gaussianCoordinate (m : ℕ) : GaussianHilbert →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m

/-- For [a coordinate](hyp:m) and [a real input](hyp:r), [evaluating the explicit Gaussian
feature at that coordinate returns its defining coefficient](goal). -/
@[simp] lemma gaussianCoordinate_feature (m : ℕ) (r : ℝ) :
    gaussianCoordinate m (gaussianFeature r) = gaussianFeatureCoefficient r m := rfl

/-- Given [a finite real measure](hyp:μ) and [a coordinate](hyp:m), [coordinate evaluation of
its explicit Gaussian mean embedding commutes with the Bochner integral](goal). -/
lemma gaussianCoordinate_meanEmbedding (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℕ) :
    gaussianCoordinate m (meanEmbedding gaussianFeatureMap μ) =
      ∫ r, gaussianFeatureCoefficient r m ∂μ := by
  unfold meanEmbedding
  rw [← (gaussianCoordinate m).integral_comp_comm (gaussianFeatureMap.integrable μ)]
  rfl






/-- Given [a real input](hyp:r), the [Gaussian weight](goal) is [the positive exponential weight
specified by the displayed formula](step:1). -/
def gaussianWeight (r : ℝ) : ℝ := Real.exp (-r ^ 2)

/-- Given [a natural-number degree](hyp:m) and [a real input](hyp:r), the [Gaussian-weighted
monomial](goal) is [the Gaussian weight times that raw monomial](step:1). -/
def gaussianWeightedMonomial (m : ℕ) (r : ℝ) : ℝ :=
  gaussianWeight r * r ^ m

/-- Given [a finite real measure](hyp:μ) and [a natural-number degree](hyp:m), [the
Gaussian-weighted monomial is Bochner-integrable](goal). -/
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

/-- Given [two finite real measures](hyp:μ,ν), [equality of all their Gaussian-weighted
monomial integrals](hyp:hmom), and [a real polynomial](hyp:p), [their Gaussian-weighted
polynomial integrals are equal](goal). -/
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






/-- Given [two finite real measures](hyp:μ,ν), [a nonnegative common support radius](hyp:B,hB),
[their concentration on that closed interval](hyp:hμ,hν), [equality of every Gaussian-weighted
monomial integral](hyp:hmom), and [a continuous real test function](hyp:f,hf), [their integrals
of that test function are equal](goal). -/
theorem continuousIntegral_eq_of_gaussianWeightedMoments_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : ∀ m : ℕ,
      ∫ r, gaussianWeightedMonomial m r ∂μ =
        ∫ r, gaussianWeightedMonomial m r ∂ν)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ r, f r ∂μ = ∫ r, f r ∂ν := by
  apply eq_of_forall_dist_le
  intro ε hε
  let M : ℝ := μ.real univ + ν.real univ + 1
  have hMpos : 0 < M := by
    dsimp [M]
    have hμnonneg : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    have hνnonneg : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
    linarith
  let δ : ℝ := ε / M
  have hδ : 0 < δ := div_pos hε hMpos
  have hquot : Continuous (fun r : ℝ => f r / gaussianWeight r) := by
    apply hf.div
    · unfold gaussianWeight
      fun_prop
    · intro r
      unfold gaussianWeight
      exact (Real.exp_pos _).ne'
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-B) B
      (fun r : ℝ => f r / gaussianWeight r) hquot.continuousOn δ hδ
  let g : ℝ → ℝ := fun r => gaussianWeight r * p.eval r
  have hg : Continuous g := by
    dsimp [g]
    unfold gaussianWeight
    fun_prop
  have hμmem : ∀ᵐ r ∂μ, r ∈ Icc (-B) B := by
    rw [ae_iff]
    exact hμ
  have hνmem : ∀ᵐ r ∂ν, r ∈ Icc (-B) B := by
    rw [ae_iff]
    exact hν
  have hμres : μ.restrict (Icc (-B) B) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμmem
  have hνres : ν.restrict (Icc (-B) B) = ν :=
    Measure.restrict_eq_self_of_ae_mem hνmem
  have hfμ : Integrable f μ := by
    rw [← hμres]
    exact hf.integrableOn_Icc
  have hfν : Integrable f ν := by
    rw [← hνres]
    exact hf.integrableOn_Icc
  have hgμ : Integrable g μ := by
    rw [← hμres]
    exact hg.integrableOn_Icc
  have hgν : Integrable g ν := by
    rw [← hνres]
    exact hg.integrableOn_Icc
  have herror : ∀ r ∈ Icc (-B) B, ‖f r - g r‖ ≤ δ := by
    intro r hr
    have hwpos : 0 < gaussianWeight r := by
      unfold gaussianWeight
      exact Real.exp_pos _
    have hwle : gaussianWeight r ≤ 1 := by
      unfold gaussianWeight
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (sq_nonneg r)
    have happ := hp r hr
    rw [Real.norm_eq_abs]
    dsimp [g]
    have hid :
        f r - gaussianWeight r * p.eval r =
          -gaussianWeight r * (p.eval r - f r / gaussianWeight r) := by
      field_simp
      ring
    rw [hid, abs_mul, abs_neg, abs_of_pos hwpos]
    have habs := abs_nonneg (p.eval r - f r / gaussianWeight r)
    nlinarith
  have herrμ :
      ‖∫ r, (f r - g r) ∂μ‖ ≤ δ * μ.real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hμmem] with r hr
    exact herror r hr
  have herrν :
      ‖∫ r, (f r - g r) ∂ν‖ ≤ δ * ν.real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hνmem] with r hr
    exact herror r hr
  rw [integral_sub hfμ hgμ] at herrμ
  rw [integral_sub hfν hgν] at herrν
  have hpoly :
      (∫ r, g r ∂μ) = ∫ r, g r ∂ν := by
    dsimp [g]
    exact gaussianWeightedPolynomial_integral_eq μ ν hmom p
  have hmassμ : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hmassν : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  calc
    dist (∫ r, f r ∂μ) (∫ r, f r ∂ν) =
        ‖((∫ r, f r ∂μ) - ∫ r, g r ∂μ) +
          ((∫ r, g r ∂ν) - ∫ r, f r ∂ν)‖ := by
            rw [dist_eq_norm, hpoly]
            congr 1
            ring
    _ ≤ ‖(∫ r, f r ∂μ) - ∫ r, g r ∂μ‖ +
        ‖(∫ r, g r ∂ν) - ∫ r, f r ∂ν‖ := norm_add_le _ _
    _ = ‖(∫ r, f r ∂μ) - ∫ r, g r ∂μ‖ +
        ‖(∫ r, f r ∂ν) - ∫ r, g r ∂ν‖ := by
          congr 1
          exact norm_sub_rev _ _
    _ ≤ δ * μ.real univ + δ * ν.real univ := add_le_add herrμ herrν
    _ = δ * (μ.real univ + ν.real univ) := by ring
    _ ≤ δ * (μ.real univ + ν.real univ + 1) := by nlinarith
    _ = ε := by
      dsimp [δ, M]
      field_simp

/-- Given [two finite real measures](hyp:μ,ν) that [have equal integrals against every continuous
real test function](hyp:h), [the measures are equal](goal). -/
theorem measure_eq_of_continuousIntegral_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : ℝ → ℝ), Continuous f → ∫ r, f r ∂μ = ∫ r, f r ∂ν) :
    μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact h f f.continuous






/-- Given [two finite real measures](hyp:μ,ν), [a nonnegative common support radius](hyp:B,hB),
[their concentration on that closed interval](hyp:hμ,hν), and [equality of every
Gaussian-weighted monomial integral](hyp:hmom), [the measures are equal](goal). -/
theorem measure_eq_of_gaussianWeightedMoments_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : ∀ m : ℕ,
      ∫ r, gaussianWeightedMonomial m r ∂μ =
        ∫ r, gaussianWeightedMonomial m r ∂ν) :
    μ = ν := by
  apply measure_eq_of_continuousIntegral_eq μ ν
  intro f hf
  exact continuousIntegral_eq_of_gaussianWeightedMoments_eq μ ν B hB hμ hν hmom f hf






/-- Given [two finite real measures](hyp:μ,ν), [equality of their explicit Gaussian mean
embeddings](hyp:hemb), and [a natural-number degree](hyp:m), [their Gaussian-weighted monomial
integrals at that degree are equal](goal). -/
lemma gaussianWeightedMoments_eq_of_meanEmbedding_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν)
    (m : ℕ) :
    ∫ r, gaussianWeightedMonomial m r ∂μ =
      ∫ r, gaussianWeightedMonomial m r ∂ν := by
  have hcoord := congrArg (gaussianCoordinate m) hemb
  rw [gaussianCoordinate_meanEmbedding, gaussianCoordinate_meanEmbedding] at hcoord
  have hscaled :
      gaussianFeatureNormalization m * ∫ r, gaussianWeightedMonomial m r ∂μ =
        gaussianFeatureNormalization m * ∫ r, gaussianWeightedMonomial m r ∂ν := by
    simpa only [gaussianFeatureCoefficient, gaussianWeightedMonomial, gaussianWeight,
      mul_assoc, integral_const_mul] using hcoord
  exact mul_left_cancel₀ (ne_of_gt (gaussianFeatureNormalization_pos m)) hscaled

/-- Given [two finite real measures](hyp:μ,ν), [a nonnegative common support radius](hyp:B,hB),
[their concentration on that closed interval](hyp:hμ,hν), and [equal explicit Gaussian mean
embeddings](hyp:hemb), [the measures are equal](goal). -/
theorem measure_eq_of_meanEmbedding_eq_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν) :
    μ = ν := by
  apply measure_eq_of_gaussianWeightedMoments_eq μ ν B hB hμ hν
  exact gaussianWeightedMoments_eq_of_meanEmbedding_eq μ ν hemb

/-- Given [two finite real measures](hyp:μ,ν), [a nonnegative common support radius](hyp:B,hB),
[their concentration on that closed interval](hyp:hμ,hν), and [equal explicit Gaussian mean
embeddings](hyp:hemb), [their raw second moments are equal](goal). -/
theorem secondMoment_eq_of_meanEmbedding_eq_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν) :
    (∫ r, r ^ 2 ∂μ) = ∫ r, r ^ 2 ∂ν := by
  rw [measure_eq_of_meanEmbedding_eq_of_boundedSupport μ ν B hB hμ hν hemb]

/-- Given [two finite real measures](hyp:μ,ν), [a nonnegative common support radius](hyp:B,hB),
[their concentration on that closed interval](hyp:hμ,hν), and [unequal raw second moments](hyp:hmom),
[the norm of the difference between their explicit Gaussian mean embeddings is strictly positive](goal). -/
theorem norm_meanEmbedding_sub_pos_of_secondMoment_ne_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : (∫ r, r ^ 2 ∂μ) ≠ ∫ r, r ^ 2 ∂ν) :
    0 < ‖meanEmbedding gaussianFeatureMap μ - meanEmbedding gaussianFeatureMap ν‖ := by
  rw [norm_pos_iff]
  intro hzero
  apply hmom
  apply secondMoment_eq_of_meanEmbedding_eq_of_boundedSupport μ ν B hB hμ hν
  exact sub_eq_zero.mp hzero

end Causalean.Mathlib.Probability.GaussianMeanEmbedding

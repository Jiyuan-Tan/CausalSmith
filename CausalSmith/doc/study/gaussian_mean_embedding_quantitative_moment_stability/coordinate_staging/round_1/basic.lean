import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# An explicit Gaussian feature map and weighted moments

This module realizes the kernel `exp (-(a - b) ^ 2)` by weighted monomial
coordinates in real `ℓ²`.  It also supplies the analytic facts needed to form
Bochner mean embeddings and to read their coordinates through continuous
linear evaluation maps.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace lp

noncomputable section

namespace Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-- [Two real inputs `a` and `b`](hyp:a,b) determine [the unit-scale Gaussian kernel
value](goal) `exp(−(a − b)²)`. -/
def gaussianKernel (a b : ℝ) : ℝ :=
  Real.exp (-(a - b) ^ 2)

/-- [A real Hilbert space `H`](hyp:H) determines [the structure](goal) of a unit-norm
feature realization of the unit-scale Gaussian kernel, [given by a feature map](step:1),
[a unit-norm certificate](step:2), and [a kernel inner-product certificate](step:3). -/
structure UnitNormGaussianFeatureMap (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  feature : ℝ → H
  norm_eq_one : ∀ r, ‖feature r‖ = 1
  inner_eq_kernel : ∀ a b, ⟪feature a, feature b⟫_ℝ = gaussianKernel a b

/-- [A coordinate index `m`](hyp:m) determines [the positive normalization](goal) that
multiplies coordinate `m` of the explicit Gaussian feature vector. -/
def gaussianFeatureNormalization (m : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ m / m.factorial)

/-- [A coordinate index `m`](hyp:m) has [strictly positive Gaussian-feature
normalization](goal). -/
lemma gaussianFeatureNormalization_pos (m : ℕ) :
    0 < gaussianFeatureNormalization m := by
  unfold gaussianFeatureNormalization
  positivity

/-- [A real input `r`](hyp:r) and [a coordinate index `m`](hyp:m) determine [the explicit
Gaussian feature coefficient](goal) at that coordinate. -/
def gaussianFeatureCoefficient (r : ℝ) (m : ℕ) : ℝ :=
  gaussianFeatureNormalization m * Real.exp (-r ^ 2) * r ^ m

/-- [A real input `r`](hyp:r) has [a square-summable explicit Gaussian coefficient
sequence](goal). -/
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

/-- [The complete real Hilbert space](goal) used for the explicit Gaussian feature map
is the square-summable sequence space. -/
abbrev GaussianHilbert := lp (fun _ : ℕ => ℝ) 2

/-- [A real input `r`](hyp:r) determines [its explicit Gaussian feature vector](goal) in
the real square-summable sequence space. -/
def gaussianFeature (r : ℝ) : GaussianHilbert :=
  ⟨gaussianFeatureCoefficient r, gaussianFeature_memℓp r⟩

/-- [Two real inputs `a` and `b`](hyp:a,b) have [an explicit feature-vector inner product
equal to their Gaussian kernel value](goal). -/
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

/-- [A real input `r`](hyp:r) has [an explicit Gaussian feature vector of norm one](goal). -/
lemma gaussianFeature_norm (r : ℝ) : ‖gaussianFeature r‖ = 1 := by
  have hsq : ‖gaussianFeature r‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, gaussianFeature_inner]
    simp [gaussianKernel]
  nlinarith [norm_nonneg (gaussianFeature r)]

/-- [The explicit Gaussian feature map](goal) is [given by the square-summable feature
vector](step:1), [its unit-norm certificate](step:2), and [its kernel-inner-product
certificate](step:3). -/
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

/-- [A unit-norm Gaussian feature realization `U`](hyp:U) has [a continuous feature
map](goal). -/
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

/-- [A unit-norm Gaussian feature realization `U`](hyp:U) and [a finite real measure `μ`](hyp:μ)
make [the feature map Bochner integrable](goal). -/
lemma UnitNormGaussianFeatureMap.integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable U.feature μ := by
  exact Integrable.of_bound U.continuous.stronglyMeasurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun r => by rw [U.norm_eq_one])

/-- [A unit-norm Gaussian feature realization `U`](hyp:U) and [a real measure `μ`](hyp:μ)
determine [their Bochner mean embedding](goal). -/
def meanEmbedding {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) : H :=
  ∫ r, U.feature r ∂μ

/-- [A coordinate index `m`](hyp:m) determines [the continuous linear evaluation map](goal)
on the real square-summable sequence space. -/
def gaussianCoordinate (m : ℕ) : GaussianHilbert →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m

/-- [A coordinate index `m`](hyp:m) and [a real input `r`](hyp:r) make [coordinate
evaluation of the explicit feature equal its defining coefficient](goal). -/
@[simp] lemma gaussianCoordinate_feature (m : ℕ) (r : ℝ) :
    gaussianCoordinate m (gaussianFeature r) = gaussianFeatureCoefficient r m := rfl

/-- [A finite real measure `μ`](hyp:μ) and [a coordinate index `m`](hyp:m) make [coordinate
evaluation commute with the Bochner Gaussian mean integral](goal). -/
lemma gaussianCoordinate_meanEmbedding (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℕ) :
    gaussianCoordinate m (meanEmbedding gaussianFeatureMap μ) =
      ∫ r, gaussianFeatureCoefficient r m ∂μ := by
  unfold meanEmbedding
  rw [← (gaussianCoordinate m).integral_comp_comm (gaussianFeatureMap.integrable μ)]
  rfl

/-! ## Gaussian-weighted moments -/

/-- [The input real value `r`](hyp:r) is assigned [its Gaussian weight](goal), the factor
`exp (−r²)` used by the explicit feature coordinates. -/
def gaussianWeight (r : ℝ) : ℝ := Real.exp (-r ^ 2)

/-- [A nonnegative integer degree `m`](hyp:m) and [a real value `r`](hyp:r) determine
[the Gaussian-weighted monomial](goal) `exp (−r²) rᵐ`. -/
def gaussianWeightedMonomial (m : ℕ) (r : ℝ) : ℝ :=
  gaussianWeight r * r ^ m

/-- [A finite real measure `μ`](hyp:μ) and [a monomial degree `m`](hyp:m) make [the
corresponding Gaussian-weighted monomial integrable](goal). -/
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

end Causalean.Mathlib.Probability.GaussianMeanEmbedding

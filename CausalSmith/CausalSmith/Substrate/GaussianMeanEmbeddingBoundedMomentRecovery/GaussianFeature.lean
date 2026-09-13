import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# An explicit Gaussian feature map

This module realizes the kernel `exp (-(a - b) ^ 2)` by weighted monomial
coordinates in real `ℓ²`.  It also supplies the analytic facts needed to form
Bochner mean embeddings and to read their coordinates through continuous
linear evaluation maps.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace lp

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- The Gaussian kernel with exponent parameter one. -/
def gaussianKernel (a b : ℝ) : ℝ :=
  Real.exp (-(a - b) ^ 2)

/-- A unit-norm real Hilbert-space feature realization of `gaussianKernel`. -/
structure UnitNormGaussianFeatureMap (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  feature : ℝ → H
  norm_eq_one : ∀ r, ‖feature r‖ = 1
  inner_eq_kernel : ∀ a b, ⟪feature a, feature b⟫_ℝ = gaussianKernel a b

/-- The positive normalization multiplying coordinate `m` of the explicit feature vector. -/
def gaussianFeatureNormalization (m : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ m / m.factorial)

/-- Every Gaussian-feature coordinate normalization is strictly positive. -/
lemma gaussianFeatureNormalization_pos (m : ℕ) :
    0 < gaussianFeatureNormalization m := by
  unfold gaussianFeatureNormalization
  positivity

/-- Coordinate `m` of the explicit Gaussian feature vector at `r`. -/
def gaussianFeatureCoefficient (r : ℝ) (m : ℕ) : ℝ :=
  gaussianFeatureNormalization m * Real.exp (-r ^ 2) * r ^ m

/-- The explicit coefficient sequence is square-summable for every real input. -/
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

/-- The complete real Hilbert space used for the explicit Gaussian feature map. -/
abbrev GaussianHilbert := lp (fun _ : ℕ => ℝ) 2

/-- The explicit Gaussian feature vector in real `ℓ²`. -/
def gaussianFeature (r : ℝ) : GaussianHilbert :=
  ⟨gaussianFeatureCoefficient r, gaussianFeature_memℓp r⟩

/-- The inner product of two explicit feature vectors is the Gaussian kernel. -/
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

/-- Every explicit Gaussian feature vector has norm one. -/
lemma gaussianFeature_norm (r : ℝ) : ‖gaussianFeature r‖ = 1 := by
  have hsq : ‖gaussianFeature r‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, gaussianFeature_inner]
    simp [gaussianKernel]
  nlinarith [norm_nonneg (gaussianFeature r)]

/-- The explicit unit-norm Hilbert-space realization of the Gaussian kernel. -/
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

/-- Every unit-norm realization of this Gaussian kernel is continuous. -/
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

/-- A unit-norm Gaussian feature map is Bochner-integrable under every finite real measure. -/
lemma UnitNormGaussianFeatureMap.integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable U.feature μ := by
  exact Integrable.of_bound U.continuous.stronglyMeasurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun r => by rw [U.norm_eq_one])

/-- The Bochner mean embedding associated with a unit-norm Gaussian feature realization. -/
def meanEmbedding {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (U : UnitNormGaussianFeatureMap H) (μ : Measure ℝ) : H :=
  ∫ r, U.feature r ∂μ

/-- Continuous linear evaluation of real `ℓ²` vectors at coordinate `m`. -/
def gaussianCoordinate (m : ℕ) : GaussianHilbert →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m

/-- Coordinate evaluation of the explicit feature returns its defining coefficient. -/
@[simp] lemma gaussianCoordinate_feature (m : ℕ) (r : ℝ) :
    gaussianCoordinate m (gaussianFeature r) = gaussianFeatureCoefficient r m := rfl

/-- Continuous linear coordinate evaluation commutes with the Bochner Gaussian mean integral. -/
lemma gaussianCoordinate_meanEmbedding (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℕ) :
    gaussianCoordinate m (meanEmbedding gaussianFeatureMap μ) =
      ∫ r, gaussianFeatureCoefficient r m ∂μ := by
  unfold meanEmbedding
  rw [← (gaussianCoordinate m).integral_comp_comm (gaussianFeatureMap.integrable μ)]
  rfl

end CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

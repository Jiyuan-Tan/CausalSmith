module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionInverseLimit

/-! # Passage to the reflected spectral endpoint limit

Reflection is continuous on spatial L² classes. Character pairing is continuous
on torus L² classes, and finite Fourier sums pass to the limit without losing
any part of the weight. These are the completion steps in roadmap (5).
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Character pairing expresses each normalized coefficient as an L² inner product.](goal) -/
-- @node: reflectionTorusCoeff_eq_inner
lemma reflectionTorusCoeff_eq_inner {p : ℕ}
    (f : Lp ℂ 2 (torusMeasure p)) (k : Fin p → ℤ) :
    UnitAddTorus.mFourierCoeff f k = inner ℂ (torusCharacterLp k) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
    (torusMeasure p) (UnitAddTorus.mFourier k)] with y hy
  simp only [torusCharacterLp] at *
  rw [hy]
  simp only [RCLike.inner_apply, UnitAddTorus.mFourier_neg, smul_eq_mul, mul_comm]

/-- [ Spatial L² convergence implies convergence of each normalized Fourier coefficient.](goal) -/
-- @node: reflectionTorusCoeff_tendsto
lemma reflectionTorusCoeff_tendsto {p : ℕ}
    {f : ℕ → Lp ℂ 2 (torusMeasure p)} {g : Lp ℂ 2 (torusMeasure p)}
    (h : Tendsto f atTop (𝓝 g)) (k : Fin p → ℤ) :
    Tendsto (fun n => UnitAddTorus.mFourierCoeff (f n) k) atTop
      (𝓝 (UnitAddTorus.mFourierCoeff g k)) := by
  simp_rw [reflectionTorusCoeff_eq_inner]
  exact tendsto_const_nhds.inner h

/-- A uniform exact weighted Fourier bound survives an L² limit. The proof
passes each finite sum to the limit and then takes their supremum. Under [the stated conditions](hyp:C,hb), [the asserted mathematical result follows](goal). -/
-- @node: reflectionTorus_weightedBudget_le_of_tendsto
lemma reflectionTorus_weightedBudget_le_of_tendsto {p : ℕ}
    {f : ℕ → Lp ℂ 2 (torusMeasure p)} {g : Lp ℂ 2 (torusMeasure p)}
    (h : Tendsto f atTop (𝓝 g)) (w : (Fin p → ℤ) → ℝ) (C : ℝ≥0∞)
    (hb : ∀ n, (∑' k, ENNReal.ofReal
      (w k * ‖UnitAddTorus.mFourierCoeff (f n) k‖ ^ 2)) ≤ C) :
    (∑' k, ENNReal.ofReal (w k * ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2)) ≤ C := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun K => ?_
  have ht : Tendsto (fun n => ∑ k ∈ K, ENNReal.ofReal
      (w k * ‖UnitAddTorus.mFourierCoeff (f n) k‖ ^ 2)) atTop
      (𝓝 (∑ k ∈ K, ENNReal.ofReal
        (w k * ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2))) := by
    apply tendsto_finsetSum
    intro k hk
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((reflectionTorusCoeff_tendsto h k).norm.pow 2))
  exact le_of_tendsto ht (Eventually.of_forall fun n =>
    (ENNReal.sum_le_tsum K).trans (hb n))

/-- [ The genuine smooth inverse truncations converge after even reflection to
reflection of the original extension. No periodic trace condition is needed.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionSmoothApproximation_tendsto_reflected_original
lemma reflectionSmoothApproximation_tendsto_reflected_original {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    Tendsto (fun n : ℕ => reflectionL2Operator p
      ((reflectionSmoothApproximation_memLp hF (n : ℝ)).toLp
        (reflectionSmoothApproximation (Fourier G) (n : ℝ)))) atTop
      (𝓝 (reflectionL2Operator p (hG2.toLp G))) := by
  dsimp only
  exact (reflectionL2Operator p).continuous.continuousAt.tendsto.comp
    (reflectionSmoothApproximation_tendsto_original hG1 hG2)

/-- [ Every admissible whole-space extension has exactly the cube function's
reflected equivalence class under the common operator.](goal) Under [the stated conditions](hyp:hG2,hG). -/
-- @node: reflectionL2Operator_extension_ae
lemma reflectionL2Operator_extension_ae {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ} (hG2 : MemLp G 2 volume)
    (g : Cube p → ℝ)
    (hG : G =ᵐ[volume.restrict (euclideanCube p)]
      fun u => (g (fun j => u j) : ℂ)) :
    reflectionL2Operator p (hG2.toLp G) =ᵐ[torusMeasure p] reflExt g := by
  have hrep := (foldEuclidean_measurePreserving p).quasiMeasurePreserving.ae
    (ae_restrict_of_ae hG2.coeFn_toLp)
  have hext := (foldEuclidean_measurePreserving p).quasiMeasurePreserving.ae hG
  filter_upwards [reflectionL2Operator_coeFn p (hG2.toLp G), hrep, hext]
    with y hy hrep hext
  exact hy.trans (hrep.trans hext)

/-- [ Fourier coefficients of the reflected extension are independent of which
admissible whole-space extension was chosen.](goal) Under [the stated conditions](hyp:hG2,hG). -/
-- @node: reflectionTorusCoeff_extension
lemma reflectionTorusCoeff_extension {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ} (hG2 : MemLp G 2 volume)
    (g : Cube p → ℝ)
    (hG : G =ᵐ[volume.restrict (euclideanCube p)]
      fun u => (g (fun j => u j) : ℂ)) (k : Fin p → ℤ) :
    UnitAddTorus.mFourierCoeff (reflectionL2Operator p (hG2.toLp G)) k = Fhat g k := by
  rw [← mFourierCoeff_reflExt]
  apply integral_congr_ae
  filter_upwards [reflectionL2Operator_extension_ae hG2 g hG] with y hy
  rw [hy]

/-- [ Smooth truncations of any admissible extension recover the specified cube
function's Fourier coefficients after reflection, with the exact normalization.](goal) Under [the stated conditions](hyp:hG1,hG2,hG). -/
-- @node: reflectionSmoothApproximation_coeff_tendsto_Fhat
lemma reflectionSmoothApproximation_coeff_tendsto_Fhat {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (g : Cube p → ℝ)
    (hG : G =ᵐ[volume.restrict (euclideanCube p)]
      fun u => (g (fun j => u j) : ℂ)) (k : Fin p → ℤ) :
    let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    Tendsto (fun n : ℕ => UnitAddTorus.mFourierCoeff
      (reflectionL2Operator p ((reflectionSmoothApproximation_memLp hF (n : ℝ)).toLp
        (reflectionSmoothApproximation (Fourier G) (n : ℝ)))) k) atTop
      (𝓝 (Fhat g k)) := by
  dsimp only
  rw [← reflectionTorusCoeff_extension hG2 g hG k]
  exact reflectionTorusCoeff_tendsto
    (reflectionSmoothApproximation_tendsto_reflected_original hG1 hG2) k

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionSmoothEndpoint
public import Causalean.Mathlib.Analysis.RealInterpolation.Operators

/-! # Reflection endpoints on full frequency L² classes

The inverse angular transform is a real linear isometry on all frequency L²
classes. Composing it with even reflection supplies the common operator for
interpolation. Smooth inverse truncations prove its first-order endpoints in
both component dimensions without any L¹ premise on the spatial representative.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The inverse angular transform on equivalence classes is real linear. -/
-- @node: reflectionInverseL2Linear
def reflectionInverseL2Linear (p : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) →ₗ[ℝ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) where
  toFun ψ := (reflectionInverseL2Representative_memLp ψ).toLp
    (reflectionInverseL2Representative ψ)
  map_add' ψ χ := by
    apply Lp.ext
    have h := (reflectionInverseDilation_quasiMeasurePreserving p).ae
      (Lp.coeFn_add
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ)
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ χ))
    filter_upwards [(reflectionInverseL2Representative_memLp (ψ + χ)).coeFn_toLp,
      (reflectionInverseL2Representative_memLp ψ).coeFn_toLp,
      (reflectionInverseL2Representative_memLp χ).coeFn_toLp,
      Lp.coeFn_add
        ((reflectionInverseL2Representative_memLp ψ).toLp _)
        ((reflectionInverseL2Representative_memLp χ).toLp _), h]
      with u hsum hψ hχ hadd hF
    simp only [hadd, hsum, hψ, hχ, reflectionInverseL2Representative,
      map_add, hF, Pi.add_apply, smul_add]
  map_smul' c ψ := by
    apply Lp.ext
    have h := (reflectionInverseDilation_quasiMeasurePreserving p).ae
      (Lp.coeFn_smul c (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ))
    filter_upwards [(reflectionInverseL2Representative_memLp (c • ψ)).coeFn_toLp,
      (reflectionInverseL2Representative_memLp ψ).coeFn_toLp,
      Lp.coeFn_smul c ((reflectionInverseL2Representative_memLp ψ).toLp _), h]
      with u hsmul hψ hout hF
    have hmap :=
      ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ).restrictScalars ℝ).map_smul c ψ
    change (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ) (c • ψ) =
      c • (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ) ψ at hmap
    simp only [RingHom.id_apply, hout, hsmul, Pi.smul_apply, hψ,
      reflectionInverseL2Representative]
    rw [hmap, hF]
    rw [Pi.smul_apply]
    exact smul_comm (Causalean.Mathlib.Analysis.Fourier.angularPrefactor p) c
      ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ) ((2 * Real.pi)⁻¹ • (-u)))

/-- Angular inversion preserves the L² norm with constant exactly one.](goal) This uses [the stated conclusion](goal). -/
-- @node: reflectionInverseL2Linear_norm
lemma reflectionInverseL2Linear_norm (p : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    ‖reflectionInverseL2Linear p ψ‖ = ‖ψ‖ := by
  have h : ‖reflectionInverseL2Linear p ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [reflectionInverseL2Linear, LinearMap.coe_mk, AddHom.coe_mk,
      reflectionToLp_norm_sq, reflectionInverseL2Representative_energy,
      reflectionLp_energy_eq_enorm_sq]
    simp
  nlinarith [norm_nonneg (reflectionInverseL2Linear p ψ), norm_nonneg ψ]

/-- [ The complete frequency L² space maps isometrically into spatial L². -/
-- @node: reflectionInverseL2Isometry
def reflectionInverseL2Isometry (p : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) →ₗᵢ[ℝ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) :=
  ⟨reflectionInverseL2Linear p, reflectionInverseL2Linear_norm p⟩

/-- The common operator for both interpolation endpoints: angular inversion
followed by genuine restriction and even reflection. -/
-- @node: reflectionProfileOperator
def reflectionProfileOperator (p : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) →L[ℝ]
      Lp ℂ 2 (torusMeasure p) :=
  (reflectionL2Operator p).comp (reflectionInverseL2Isometry p).toContinuousLinearMap

/-- The common frequency-to-torus operator contracts the zero-order norm.](goal) This uses [the stated conclusion](goal). -/
-- @node: reflectionProfileOperator_norm_le
lemma reflectionProfileOperator_norm_le (p : ℕ) : ‖reflectionProfileOperator p‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro ψ
  change ‖reflectionL2Operator p (reflectionInverseL2Isometry p ψ)‖ ≤ 1 * ‖ψ‖
  calc
    _ ≤ ‖reflectionL2Operator p‖ * ‖reflectionInverseL2Isometry p ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := by
      rw [(reflectionInverseL2Isometry p).norm_map]
      exact mul_le_mul_of_nonneg_right (reflectionL2Operator_norm_le p) (norm_nonneg _)

/-- [ Smooth profile truncations converge under the actual common reflection
operator on every frequency L² class.](goal) -/
-- @node: reflectionProfileOperator_tendsto
lemma reflectionProfileOperator_tendsto (p : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    Tendsto (fun n : ℕ => reflectionL2Operator p
      ((reflectionSmoothApproximation_memLp (Lp.memLp ψ) (n : ℝ)).toLp
        (reflectionSmoothApproximation ψ (n : ℝ)))) atTop
      (𝓝 (reflectionProfileOperator p ψ)) := by
  have hclass : (Lp.memLp ψ).toLp (fun ω => ψ ω) = ψ := by
    apply Lp.ext
    exact (Lp.memLp ψ).coeFn_toLp
  have h := (reflectionL2Operator p).continuous.continuousAt.tendsto.comp
    (reflectionSmoothApproximation_tendsto_inverseL2Representative
      (Lp.stronglyMeasurable ψ).measurable (Lp.memLp ψ))
  rw [hclass] at h
  exact h

/-- [ The full one-dimensional first-order endpoint holds for all frequency L²
classes, including those whose spatial inverse has no L¹ representative.](goal) -/
-- @node: reflectionProfileOperator_line_firstOrder_le
lemma reflectionProfileOperator_line_firstOrder_le
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)))) :
    (∑' k : Fin 1 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k) *
      ‖UnitAddTorus.mFourierCoeff (reflectionProfileOperator 1 ψ) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2)) := by
  exact reflectionTorus_weightedBudget_le_of_tendsto
    (reflectionProfileOperator_tendsto 1 ψ)
    (fun k => 1 + Real.pi ^ 2 * frequencySq k) _
    (fun n => reflectionSmoothApproximation_line_operator_budget (Lp.memLp ψ) (n : ℝ))

/-- [ The full two-dimensional endpoint retains the exact gradient factor 1/2
on all frequency L² classes, without additional integrability assumptions.](goal) -/
-- @node: reflectionProfileOperator_plane_firstOrder_le
lemma reflectionProfileOperator_plane_firstOrder_le
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) :
    (∑' k : Fin 2 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / 2) *
      ‖UnitAddTorus.mFourierCoeff (reflectionProfileOperator 2 ψ) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / 2)) := by
  exact reflectionTorus_weightedBudget_le_of_tendsto
    (reflectionProfileOperator_tendsto 2 ψ)
    (fun k => 1 + Real.pi ^ 2 * frequencySq k / 2) _
    (fun n => reflectionSmoothApproximation_plane_operator_budget (Lp.memLp ψ) (n : ℝ))

/-- The whole-space first-order frequency gauge, infinite off the endpoint. -/
-- @node: reflectionProfileFirstOrderNorm
def reflectionProfileFirstOrderNorm (p : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) : ℝ≥0∞ :=
  ENNReal.rpow (∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) (1 / 2)

/-- The periodic first-order Fourier gauge with the exact local dimension factor. -/
-- @node: reflectionTorusFirstOrderNorm
def reflectionTorusFirstOrderNorm (p : ℕ) (f : Lp ℂ 2 (torusMeasure p)) : ℝ≥0∞ :=
  ENNReal.rpow (∑' k : Fin p → ℤ, ENNReal.ofReal
    ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) *
      ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2)) (1 / 2)

/-- The common operator contracts the full first-order endpoint gauge in
both component dimensions; the bound was derived from smooth truncations. Under [the stated conditions](hyp:hp), [the asserted mathematical result follows](goal). -/
-- @node: reflectionProfileOperator_firstOrder_norm_le
lemma reflectionProfileOperator_firstOrder_norm_le (p : ℕ) (hp : p = 1 ∨ p = 2)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    reflectionTorusFirstOrderNorm p (reflectionProfileOperator p ψ) ≤
      reflectionProfileFirstOrderNorm p ψ := by
  apply ENNReal.rpow_le_rpow _ (by positivity : (0 : ℝ) ≤ 1 / 2)
  rcases hp with rfl | rfl
  · simpa only [Nat.cast_one, div_one] using reflectionProfileOperator_line_firstOrder_le ψ
  · simpa only [Nat.cast_ofNat] using reflectionProfileOperator_plane_firstOrder_le ψ

/-- [ The normalized quadratic K norm contracts under the genuine common
reflection operator. Both endpoint bounds are proved here, rather than assumed;
the remaining fractional step is identification with the weighted Fourier norms.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: reflectionProfileOperator_kNormSq_le
lemma reflectionProfileOperator_kNormSq_le (p : ℕ) (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      (fun f : Lp ℂ 2 (torusMeasure p) => ‖f‖ₑ)
      (reflectionTorusFirstOrderNorm p) s (reflectionProfileOperator p ψ) ≤
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      (fun f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) => ‖f‖ₑ)
      (reflectionProfileFirstOrderNorm p) s ψ := by
  have hzero (χ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
      ‖reflectionProfileOperator p χ‖ₑ ≤ (1 : ℝ≥0∞) * ‖χ‖ₑ := by
    simp only [one_mul, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ‖reflectionProfileOperator p‖ * ‖χ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖χ‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (reflectionProfileOperator_norm_le p) (norm_nonneg χ)
  have hone (χ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
      reflectionTorusFirstOrderNorm p (reflectionProfileOperator p χ) ≤
        (1 : ℝ≥0∞) * reflectionProfileFirstOrderNorm p χ := by
    simpa only [one_mul] using reflectionProfileOperator_firstOrder_norm_le p hp χ
  have h := Causalean.Mathlib.Analysis.RealInterpolation.kNormSq_map_le_of_pos
    (fun f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) => ‖f‖ₑ)
    (reflectionProfileFirstOrderNorm p)
    (fun f : Lp ℂ 2 (torusMeasure p) => ‖f‖ₑ)
    (reflectionTorusFirstOrderNorm p)
    (reflectionProfileOperator p).toLinearMap.toAddMonoidHom
    1 1 (by norm_num) (by norm_num) hzero hone s hs ψ
  simpa using h

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

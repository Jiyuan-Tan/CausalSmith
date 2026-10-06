module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionGradientLimit
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionPlaneParseval

/-! # Spectral endpoints for the actual smooth inverse truncations

Coordinate changes preserve Lebesgue measure. The slice and plane reflected
Parseval identities therefore apply to the genuine inverse angular truncations,
with their actual derivatives and exact whole-space Fourier energy.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.Fourier
set_option backward.isDefEq.respectTransparency false

/-- [ The single-coordinate parametrization of Euclidean one-space preserves volume.](goal) -/
-- @node: reflectionLine_coordinates_measurePreserving
lemma reflectionLine_coordinates_measurePreserving :
    MeasurePreserving (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
      volume (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).symm
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  exact (PiLp.volume_preserving_toLp (Fin 1)).comp h

/-- On the real-line parametrization, the constructed coordinate derivative
is the actual derivative of the smooth inverse truncation. Under [the stated conditions](hyp:hψ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothApproximation_line_hasDerivAt
lemma reflectionSmoothApproximation_line_hasDerivAt
    {ψ : EuclideanSpace ℝ (Fin 1) → ℂ} (hψ : MemLp ψ 2 volume)
    (R x : ℝ) :
    HasDerivAt (fun t : ℝ => reflectionSmoothApproximation ψ R
      (WithLp.toLp 2 (fun _ : Fin 1 => t)))
      (reflectionSmoothDerivative ψ R 0 (WithLp.toLp 2 (fun _ : Fin 1 => x))) x := by
  have he (t : ℝ) : updateCoordinate (0 : EuclideanSpace ℝ (Fin 1)) 0 t =
      WithLp.toLp 2 (fun _ : Fin 1 => t) := by
    ext j
    fin_cases j
    simp [updateCoordinate]
  simpa only [he] using reflectionSmoothApproximation_hasDerivAt_slice hψ R 0 0 x

/-- [ The one-dimensional smooth reflected spectrum contracts the exact angular
first-order frequency energy. No derivative or endpoint bound is assumed.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_line_spectral_le_profile
lemma reflectionSmoothApproximation_line_spectral_le_profile
    {ψ : EuclideanSpace ℝ (Fin 1) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∑' a : ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * (a : ℝ) ^ 2) *
      ‖periodTwoSliceCoeff (evenReflectionSlice (fun x =>
        reflectionSmoothApproximation ψ R (WithLp.toLp 2 (fun _ : Fin 1 => x)))) a‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2)) := by
  let e : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => WithLp.toLp 2 (fun _ => x)
  let f : ℝ → ℂ := fun x => reflectionSmoothApproximation ψ R (e x)
  let f' : ℝ → ℂ := fun x => reflectionSmoothDerivative ψ R 0 (e x)
  have hd : ∀ x, HasDerivAt f (f' x) x :=
    reflectionSmoothApproximation_line_hasDerivAt hψ R
  have hc : Continuous f' := by
    dsimp [f', e]
    fun_prop
  have hL : MemLp f 2 volume :=
    (reflectionSmoothApproximation_memLp hψ R).comp_measurePreserving
      reflectionLine_coordinates_measurePreserving
  have hD : MemLp f' 2 volume :=
    (reflectionSmoothDerivative_memLp hψ R 0).comp_measurePreserving
      reflectionLine_coordinates_measurePreserving
  have hs := evenReflectionSlice_firstOrder_parseval hd hc
  have hb := evenReflectionSlice_firstOrder_le_wholeSpace hd hc hL hD
  have he (F : EuclideanSpace ℝ (Fin 1) → ℂ) :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖F (e x)‖ ^ 2)) =
        ∫⁻ u, ENNReal.ofReal (‖F u‖ ^ 2) := by
    exact reflectionLine_coordinates_measurePreserving.lintegral_comp_emb
      ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))).measurableEmbedding
        (fun u => ENNReal.ofReal (‖F u‖ ^ 2))
  change (∑' a : ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * (a : ℝ) ^ 2) *
    ‖periodTwoSliceCoeff (evenReflectionSlice f) a‖ ^ 2)) ≤ _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hs.summable]
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [ENNReal.ofReal_add (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal (hL.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (hD.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _)]
  dsimp only [f, f']
  rw [he, he]
  have h := reflectionSmoothApproximation_firstOrder_le_profile hψ R
  simp only [reflectionSmoothApproximation_coordinateDerivative hψ,
    Fin.sum_univ_one, Nat.cast_one, inv_one, ENNReal.ofReal_one, one_mul, div_one] at h
  exact h

/-- The two-coordinate parametrization of Euclidean two-space preserves volume. [The asserted mathematical result follows](goal). -/
-- @node: reflectionPlane_coordinates_measurePreserving
lemma reflectionPlane_coordinates_measurePreserving :
    MeasurePreserving (fun z : ℝ × ℝ => WithLp.toLp 2 ![z.1, z.2])
      volume (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have h := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp h

/-- Both real coordinate slices of the genuine two-dimensional truncation
have the constructed inverse derivatives. Under [the stated conditions](hyp:hψ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothApproximation_plane_hasDerivAt
lemma reflectionSmoothApproximation_plane_hasDerivAt
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hψ : MemLp ψ 2 volume)
    (R x y : ℝ) :
    HasDerivAt (fun t : ℝ => reflectionSmoothApproximation ψ R (WithLp.toLp 2 ![t, y]))
      (reflectionSmoothDerivative ψ R 0 (WithLp.toLp 2 ![x, y])) x ∧
    HasDerivAt (fun t : ℝ => reflectionSmoothApproximation ψ R (WithLp.toLp 2 ![x, t]))
      (reflectionSmoothDerivative ψ R 1 (WithLp.toLp 2 ![x, y])) y := by
  have hx (t : ℝ) : updateCoordinate (WithLp.toLp 2 ![x, y]) 0 t =
      WithLp.toLp 2 ![t, y] := by
    ext j
    fin_cases j <;> simp [updateCoordinate]
  have hy (t : ℝ) : updateCoordinate (WithLp.toLp 2 ![x, y]) 1 t =
      WithLp.toLp 2 ![x, t] := by
    ext j
    fin_cases j <;> simp [updateCoordinate]
  constructor
  · simpa only [hx] using
      reflectionSmoothApproximation_hasDerivAt_slice hψ R (WithLp.toLp 2 ![x, y]) 0 x
  · simpa only [hy] using
      reflectionSmoothApproximation_hasDerivAt_slice hψ R (WithLp.toLp 2 ![x, y]) 1 y

/-- [ The actual two-dimensional smooth reflected spectrum contracts the angular
first-order energy with exactly the local gradient factor one half.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_plane_spectral_le_profile
lemma reflectionSmoothApproximation_plane_spectral_le_profile
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∑' k : ℤ × ℤ, ENNReal.ofReal
      ((1 + Real.pi ^ 2 * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) / 2) *
        ‖periodTwoPlaneCoeff (evenReflectionPlane (fun x y =>
          reflectionSmoothApproximation ψ R (WithLp.toLp 2 ![x, y]))) k.1 k.2‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / 2)) := by
  let e : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun z => WithLp.toLp 2 ![z.1, z.2]
  let f : ℝ → ℝ → ℂ := fun x y => reflectionSmoothApproximation ψ R (e (x, y))
  let fx : ℝ → ℝ → ℂ := fun x y => reflectionSmoothDerivative ψ R 0 (e (x, y))
  let fy : ℝ → ℝ → ℂ := fun x y => reflectionSmoothDerivative ψ R 1 (e (x, y))
  have hdx : ∀ x y, HasDerivAt (fun t => f t y) (fx x y) x :=
    fun x y => (reflectionSmoothApproximation_plane_hasDerivAt hψ R x y).1
  have hdy : ∀ x y, HasDerivAt (f x) (fy x y) y :=
    fun x y => (reflectionSmoothApproximation_plane_hasDerivAt hψ R x y).2
  have hf : Continuous f.uncurry := by
    dsimp [f, Function.uncurry, e]
    exact (reflectionSmoothApproximation_contDiff hψ R).continuous.comp (by fun_prop)
  have hfx : Continuous fx.uncurry := by dsimp [fx, Function.uncurry, e]; fun_prop
  have hfy : Continuous fy.uncurry := by dsimp [fy, Function.uncurry, e]; fun_prop
  have hL : MemLp f.uncurry 2 volume :=
    (reflectionSmoothApproximation_memLp hψ R).comp_measurePreserving
      reflectionPlane_coordinates_measurePreserving
  have hDx : MemLp fx.uncurry 2 volume :=
    (reflectionSmoothDerivative_memLp hψ R 0).comp_measurePreserving
      reflectionPlane_coordinates_measurePreserving
  have hDy : MemLp fy.uncurry 2 volume :=
    (reflectionSmoothDerivative_memLp hψ R 1).comp_measurePreserving
      reflectionPlane_coordinates_measurePreserving
  have hs := evenReflectionPlane_firstOrder_parseval hdx hdy hf hfx hfy
  have hb := evenReflectionPlane_firstOrder_spectral_le_wholeSpace
    hdx hdy hf hfx hfy hL hDx hDy
  have he (F : EuclideanSpace ℝ (Fin 2) → ℂ) :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖F (e z)‖ ^ 2)) =
        ∫⁻ u, ENNReal.ofReal (‖F u‖ ^ 2) := by
    exact reflectionPlane_coordinates_measurePreserving.lintegral_comp_emb
      (MeasurableEquiv.finTwoArrow.symm.trans
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))).measurableEmbedding
        (fun u => ENNReal.ofReal (‖F u‖ ^ 2))
  change (∑' k : ℤ × ℤ, ENNReal.ofReal
    ((1 + Real.pi ^ 2 * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) / 2) *
      ‖periodTwoPlaneCoeff (evenReflectionPlane f) k.1 k.2‖ ^ 2)) ≤ _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable]
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  change MemLp (fun z : ℝ × ℝ => f z.1 z.2) 2 volume at hL
  change MemLp (fun z : ℝ × ℝ => fx z.1 z.2) 2 volume at hDx
  change MemLp (fun z : ℝ × ℝ => fy z.1 z.2) 2 volume at hDy
  rw [ENNReal.ofReal_add (integral_nonneg (fun _ => sq_nonneg _)) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_add (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal (hL.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (hDx.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (hDy.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _)]
  dsimp only [f, fx, fy]
  rw [he, he, he]
  have h := reflectionSmoothApproximation_firstOrder_le_profile hψ R
  simpa only [reflectionSmoothApproximation_coordinateDerivative hψ,
    Fin.sum_univ_two, Nat.cast_ofNat, one_div] using h

/-- The unit-circle coordinate convention gives precisely the normalized
period-two slice coefficient after folding, for any complex cube slice. [The asserted mathematical result follows](goal). -/
-- @node: reflectionTorusCoeff_line_eq_slice
lemma reflectionTorusCoeff_line_eq_slice (f : ℝ → ℂ) (a : ℤ) :
    UnitAddTorus.mFourierCoeff (fun y : Torus 1 => f (fold y 0)) (fun _ => a) =
      periodTwoSliceCoeff (evenReflectionSlice f) a := by
  have h := (measurePreserving_funUnique AddCircle.haarAddCircle (Fin 1)).symm
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle)
  have hi := h.integral_comp
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm.measurableEmbedding
    (fun y : Torus 1 => UnitAddTorus.mFourier (-(fun _ => a)) y * f (fold y 0))
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  change (∫ y : Torus 1, UnitAddTorus.mFourier (-(fun _ => a)) y * f (fold y 0) ∂torusMeasure 1) = _
  rw [← hi, AddCircle.integral_haarAddCircle]
  norm_num only [inv_one, one_smul]
  rw [← UnitAddCircle.intervalIntegral_preimage 0]
  norm_num only [zero_add]
  change (∫ u in (0 : ℝ)..1,
    UnitAddTorus.mFourier (-(fun _ : Fin 1 => a)) (fun _ => (u : UnitAddCircle)) *
      f (fold (fun _ : Fin 1 => (u : UnitAddCircle)) 0)) = _
  have he : (∫ u in (0 : ℝ)..1,
      UnitAddTorus.mFourier (-(fun _ : Fin 1 => a)) (fun _ => (u : UnitAddCircle)) *
        f (fold (fun _ : Fin 1 => (u : UnitAddCircle)) 0)) =
      ∫ u in (0 : ℝ)..1, fourier (-a) ((2 * u : ℝ) : AddCircle (2 : ℝ)) *
        evenReflectionSlice f (2 * u) := by
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo] using hu
    have hfold : fold (fun _ : Fin 1 => (u : UnitAddCircle)) 0 = min (2 * u) (2 - 2 * u) := by
      unfold fold
      rw [AddCircle.equivIco_coe_of_mem]
      exact ⟨hu'.1.le, by simpa using hu'.2⟩
    have hf : f (fold (fun _ : Fin 1 => (u : UnitAddCircle)) 0) =
        evenReflectionSlice f (2 * u) := by
      rw [hfold]
      unfold evenReflectionSlice
      by_cases hu2 : 2 * u ≤ 1
      · rw [if_pos hu2, min_eq_left (by linarith)]
      · rw [if_neg hu2, min_eq_right (by linarith)]
    dsimp only
    rw [hf]
    congr 1
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_one,
      Pi.neg_apply, fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, intervalIntegral.integral_comp_mul_left
    (fun y : ℝ => fourier (-a) (y : AddCircle (2 : ℝ)) * evenReflectionSlice f y)
    (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num [periodTwoSliceCoeff, Complex.real_smul, smul_eq_mul]

/-- The actual whole-space reflection operator's coefficients agree with the
period-two slice coefficients, independently of the chosen L² representative. Under [the stated conditions](hyp:hG), [the asserted mathematical result follows](goal). -/
-- @node: reflectionL2Operator_line_coeff_eq_slice
lemma reflectionL2Operator_line_coeff_eq_slice {G : EuclideanSpace ℝ (Fin 1) → ℂ}
    (hG : MemLp G 2 volume) (a : ℤ) :
    UnitAddTorus.mFourierCoeff (reflectionL2Operator 1 (hG.toLp G)) (fun _ => a) =
      periodTwoSliceCoeff (evenReflectionSlice (fun x =>
        G (WithLp.toLp 2 (fun _ : Fin 1 => x)))) a := by
  rw [← reflectionTorusCoeff_line_eq_slice]
  have hr := (foldEuclidean_measurePreserving 1).quasiMeasurePreserving.ae
    (ae_restrict_of_ae hG.coeFn_toLp)
  apply integral_congr_ae
  filter_upwards [reflectionL2Operator_coeFn 1 (hG.toLp G), hr] with y hy hr
  have he : WithLp.toLp 2 (fold y) = WithLp.toLp 2 (fun _ : Fin 1 => fold y 0) := by
    ext j
    fin_cases j
    rfl
  simp only [smul_eq_mul]
  rw [hy, hr, he]

/-- [ Smooth inverse truncations satisfy the first-order bound in the actual
torus L² operator, rather than merely in interval coordinates.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_line_operator_budget
lemma reflectionSmoothApproximation_line_operator_budget
    {ψ : EuclideanSpace ℝ (Fin 1) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∑' k : Fin 1 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k) *
      ‖UnitAddTorus.mFourierCoeff (reflectionL2Operator 1
        ((reflectionSmoothApproximation_memLp hψ R).toLp
          (reflectionSmoothApproximation ψ R))) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2)) := by
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  have he (a : ℤ) : (Equiv.funUnique (Fin 1) ℤ).symm a = (fun _ => a) := by
    funext j
    simp [Equiv.funUnique, Equiv.piUnique, uniqueElim_const]
  simp_rw [he]
  simpa only [reflectionL2Operator_line_coeff_eq_slice, frequencySq, Fin.sum_univ_one] using
    reflectionSmoothApproximation_line_spectral_le_profile hψ R

/-- [ Spatial L² convergence passes the proved smooth spectral bound to every
admissible one-dimensional extension, with no trace condition or assumed endpoint.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionL2Operator_line_firstOrder_le
lemma reflectionL2Operator_line_firstOrder_le
    {G : EuclideanSpace ℝ (Fin 1) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (∑' k : Fin 1 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k) *
      ‖UnitAddTorus.mFourierCoeff (reflectionL2Operator 1 (hG2.toLp G)) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2)) := by
  have hF := angularFourier_memLp G hG1 hG2
  exact reflectionTorus_weightedBudget_le_of_tendsto
    (reflectionSmoothApproximation_tendsto_reflected_original hG1 hG2)
    (fun k => 1 + Real.pi ^ 2 * frequencySq k) _
    (fun n => reflectionSmoothApproximation_line_operator_budget hF (n : ℝ))

/-- Taking the infimum over genuine extensions proves the complete
one-dimensional component contraction at the first-order endpoint. [The asserted mathematical result follows](goal). -/
-- @node: componentFourierBudget_one_firstOrder_le
lemma componentFourierBudget_one_firstOrder_le (g : Cube 1 → ℝ) :
    componentFourierBudget 1 1 g ≤ sobolevNormSq 1 1 g := by
  unfold sobolevNormSq
  refine le_iInf fun G => le_iInf fun hG => ?_
  have h := reflectionL2Operator_line_firstOrder_le hG.1 hG.2.1
  simp_rw [reflectionTorusCoeff_extension hG.2.1 g hG.2.2] at h
  simpa only [componentFourierBudget, Nat.cast_one, div_one, Real.rpow_one] using h

/-- [ The folded one-coordinate coefficient can be integrated directly on the circle.](goal) -/
-- @node: reflectionCircleCoeff_eq_slice
lemma reflectionCircleCoeff_eq_slice (f : ℝ → ℂ) (a : ℤ) :
    (∫ u : UnitAddCircle, UnitAddTorus.mFourier (fun _ : Fin 1 => -a) (fun _ => u) *
      f (fold (fun _ : Fin 1 => u) 0) ∂AddCircle.haarAddCircle) =
      periodTwoSliceCoeff (evenReflectionSlice f) a := by
  have h := (measurePreserving_funUnique AddCircle.haarAddCircle (Fin 1)).symm
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle)
  have hi := h.integral_comp
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm.measurableEmbedding
    (fun y : Torus 1 => UnitAddTorus.mFourier (-(fun _ => a)) y * f (fold y 0))
  exact hi.trans (reflectionTorusCoeff_line_eq_slice f a)

/-- The two-dimensional torus coefficient is the iterated period-two coefficient
of the actual folded whole-space representative. Under [the stated conditions](hyp:hG), [the asserted mathematical result follows](goal). -/
-- @node: reflectionTorusCoeff_plane_eq_plane
lemma reflectionTorusCoeff_plane_eq_plane
    {G : EuclideanSpace ℝ (Fin 2) → ℂ} (hG : MemLp G 2 volume) (a b : ℤ) :
    UnitAddTorus.mFourierCoeff (fun y : Torus 2 => G (WithLp.toLp 2 (fold y))) ![a, b] =
      periodTwoPlaneCoeff (evenReflectionPlane (fun x y => G (WithLp.toLp 2 ![x, y]))) a b := by
  let f : Torus 2 → ℂ := fun y => G (WithLp.toLp 2 (fold y))
  have hL : MemLp f 2 (torusMeasure 2) :=
    (hG.restrict (euclideanCube 2)).comp_measurePreserving (foldEuclidean_measurePreserving 2)
  have hI : Integrable (fun y => UnitAddTorus.mFourier (-![a, b]) y * f y)
      (torusMeasure 2) := hL.integrable (by norm_num) |>.bdd_mul
        (by fun_prop) (Eventually.of_forall fun y =>
          ((UnitAddTorus.mFourier (-![a, b])).norm_coe_le_norm y).trans
            (by rw [UnitAddTorus.mFourier_norm]))
  have h := (measurePreserving_finTwoArrow AddCircle.haarAddCircle).symm
    (MeasurableEquiv.finTwoArrow : Torus 2 ≃ᵐ UnitAddCircle × UnitAddCircle)
  have hi := h.integral_comp MeasurableEquiv.finTwoArrow.symm.measurableEmbedding
    (fun y => UnitAddTorus.mFourier (-![a, b]) y * f y)
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  change (∫ y, UnitAddTorus.mFourier (-![a, b]) y * f y ∂torusMeasure 2) = _
  rw [← hi]
  have hIp : Integrable (fun z : UnitAddCircle × UnitAddCircle =>
      UnitAddTorus.mFourier (-![a, b]) (MeasurableEquiv.finTwoArrow.symm z) *
        f (MeasurableEquiv.finTwoArrow.symm z))
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) :=
    (h.integrable_comp_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).2 hI
  rw [integral_prod _ hIp]
  have he (u v : UnitAddCircle) :
      UnitAddTorus.mFourier (-![a, b]) (MeasurableEquiv.finTwoArrow.symm (u, v)) =
        UnitAddTorus.mFourier (fun _ : Fin 1 => -a) (fun _ => u) *
        UnitAddTorus.mFourier (fun _ : Fin 1 => -b) (fun _ => v) := by
    simp [UnitAddTorus.mFourier, Fin.prod_univ_two]
  simp_rw [he, mul_assoc, integral_const_mul]
  have hf (u v : UnitAddCircle) :
      f (MeasurableEquiv.finTwoArrow.symm (u, v)) =
        G (WithLp.toLp 2 ![fold (fun _ : Fin 1 => u) 0, fold (fun _ : Fin 1 => v) 0]) := by
    dsimp only [f]
    congr 1
    ext j
    fin_cases j <;> rfl
  simp_rw [hf]
  have hs (u : UnitAddCircle) := reflectionCircleCoeff_eq_slice
    (fun y => G (WithLp.toLp 2 ![fold (fun _ : Fin 1 => u) 0, y])) b
  simp_rw [hs]
  rw [reflectionCircleCoeff_eq_slice
    (fun x => periodTwoSliceCoeff (evenReflectionSlice
      (fun y => G (WithLp.toLp 2 ![x, y]))) b) a]
  unfold periodTwoPlaneCoeff
  change (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..2, fourier (-a) (x : AddCircle (2 : ℝ)) *
    evenReflectionSlice (fun x => periodTwoSliceCoeff
      (evenReflectionSlice (fun y => G (WithLp.toLp 2 ![x, y]))) b) x) = _
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  unfold evenReflectionPlane
  by_cases h : x ≤ 1 <;> simp [evenReflectionSlice, h] <;> rfl

/-- [ The actual reflection operator has the joint period-two coefficients of
any whole-space L² representative.](goal) Under [the stated conditions](hyp:hG). -/
-- @node: reflectionL2Operator_plane_coeff_eq_plane
lemma reflectionL2Operator_plane_coeff_eq_plane
    {G : EuclideanSpace ℝ (Fin 2) → ℂ} (hG : MemLp G 2 volume) (a b : ℤ) :
    UnitAddTorus.mFourierCoeff (reflectionL2Operator 2 (hG.toLp G)) ![a, b] =
      periodTwoPlaneCoeff (evenReflectionPlane (fun x y => G (WithLp.toLp 2 ![x, y]))) a b := by
  rw [← reflectionTorusCoeff_plane_eq_plane hG]
  have hr := (foldEuclidean_measurePreserving 2).quasiMeasurePreserving.ae
    (ae_restrict_of_ae hG.coeFn_toLp)
  apply integral_congr_ae
  filter_upwards [reflectionL2Operator_coeFn 2 (hG.toLp G), hr] with y hy hr
  simp only [smul_eq_mul]
  rw [hy, hr]

/-- [ The smooth plane estimate holds in the actual torus reflection operator,
with precisely the local factor one half.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_plane_operator_budget
lemma reflectionSmoothApproximation_plane_operator_budget
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∑' k : Fin 2 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / 2) *
      ‖UnitAddTorus.mFourierCoeff (reflectionL2Operator 2
        ((reflectionSmoothApproximation_memLp hψ R).toLp
          (reflectionSmoothApproximation ψ R))) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / 2)) := by
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  have he (k : ℤ × ℤ) : (finTwoArrowEquiv ℤ).symm k = ![k.1, k.2] := rfl
  simp_rw [he]
  simpa only [reflectionL2Operator_plane_coeff_eq_plane,
    frequencySq, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    reflectionSmoothApproximation_plane_spectral_le_profile hψ R

/-- [ The proved smooth two-dimensional endpoint passes to every whole-space
extension by spatial L² convergence, without a cube trace assumption.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionL2Operator_plane_firstOrder_le
lemma reflectionL2Operator_plane_firstOrder_le
    {G : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (∑' k : Fin 2 → ℤ, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / 2) *
      ‖UnitAddTorus.mFourierCoeff (reflectionL2Operator 2 (hG2.toLp G)) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / 2)) := by
  have hF := angularFourier_memLp G hG1 hG2
  exact reflectionTorus_weightedBudget_le_of_tendsto
    (reflectionSmoothApproximation_tendsto_reflected_original hG1 hG2)
    (fun k => 1 + Real.pi ^ 2 * frequencySq k / 2) _
    (fun n => reflectionSmoothApproximation_plane_operator_budget hF (n : ℝ))

/-- The extension infimum gives the complete two-dimensional component
contraction at smoothness one, with constant one. [The asserted mathematical result follows](goal). -/
-- @node: componentFourierBudget_two_firstOrder_le
lemma componentFourierBudget_two_firstOrder_le (g : Cube 2 → ℝ) :
    componentFourierBudget 2 1 g ≤ sobolevNormSq 2 1 g := by
  unfold sobolevNormSq
  refine le_iInf fun G => le_iInf fun hG => ?_
  have h := reflectionL2Operator_plane_firstOrder_le hG.1 hG.2.1
  simp_rw [reflectionTorusCoeff_extension hG.2.1 g hG.2.2] at h
  simpa only [componentFourierBudget, Nat.cast_ofNat, Real.rpow_one] using h

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

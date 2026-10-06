module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionInterpolation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Target Fourier interpolation

Fourier coefficients transport the periodic endpoint gauges to weighted counting
measure spaces. Exact weighted interpolation gives the fractional spectral budget
from the genuine reflection operator's K norm without any loss of constant.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.RealInterpolation

/-- [ The normalized Fourier characters form the periodic L² basis. -/
-- @node: reflectionTargetBasis
def reflectionTargetBasis (p : ℕ) (hp : 0 < p) :
    HilbertBasis (Fin p → ℤ) ℂ (Lp ℂ 2 (torusMeasure p)) :=
  HilbertBasis.mk (torusParseval p hp 0).1 (torusParseval p hp 0).2.1

/-- The basis coordinates are the paper's normalized Fourier coefficients.](goal) Under [the stated conditions](hyp:hp). This uses [the stated conclusion](goal). -/
-- @node: reflectionTargetBasis_repr
lemma reflectionTargetBasis_repr (p : ℕ) (hp : 0 < p)
    (f : Lp ℂ 2 (torusMeasure p)) (k : Fin p → ℤ) :
    (reflectionTargetBasis p hp).repr f k = UnitAddTorus.mFourierCoeff f k := by
  trans ∫ t, conj (torusCharacterLp k t) * f t ∂torusMeasure p
  · rw [HilbertBasis.repr_apply_apply, MeasureTheory.L2.inner_def]
    simp only [reflectionTargetBasis, HilbertBasis.coe_mk, RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
      (torusMeasure p) (UnitAddTorus.mFourier k)] with t ht
    simp only [torusCharacterLp]
    rw [ht, ← UnitAddTorus.mFourier_neg, smul_eq_mul]

/-- [ Fourier coordinates define an additive map into measurable counting classes. -/
-- @node: reflectionTargetCoefficients
def reflectionTargetCoefficients (p : ℕ) (hp : 0 < p) :
    Lp ℂ 2 (torusMeasure p) →+ ((Fin p → ℤ) →ₘ[Measure.count] ℂ) where
  toFun f := AEEqFun.mk (fun k => UnitAddTorus.mFourierCoeff f k)
    (measurable_of_countable _).aestronglyMeasurable
  map_zero' := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff (0 : Lp ℂ 2 (torusMeasure p)) k)
      (measurable_of_countable _).aestronglyMeasurable, AEEqFun.coeFn_zero (α := Fin p → ℤ) (μ := Measure.count) (β := ℂ)] with k hk hz
    rw [hk, hz, ← reflectionTargetBasis_repr p hp]
    simp
  map_add' f g := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff (f + g) k)
      (measurable_of_countable _).aestronglyMeasurable,
      AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff f k)
        (measurable_of_countable _).aestronglyMeasurable,
      AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff g k)
        (measurable_of_countable _).aestronglyMeasurable,
      AEEqFun.coeFn_add
        (AEEqFun.mk (fun k => UnitAddTorus.mFourierCoeff f k) (measurable_of_countable _).aestronglyMeasurable)
        (AEEqFun.mk (fun k => UnitAddTorus.mFourierCoeff g k) (measurable_of_countable _).aestronglyMeasurable)]
      with k hsum hf hg hadd
    rw [hadd, hsum, Pi.add_apply, hf, hg]
    simp only [← reflectionTargetBasis_repr p hp, map_add, lp.coeFn_add, Pi.add_apply]

/-- Every weighted coefficient gauge is its explicit spectral sum.](goal) Under [the stated conditions](hyp:hp,w). This uses [the stated conclusion](goal). -/
-- @node: reflectionTargetCoefficients_wNorm
lemma reflectionTargetCoefficients_wNorm (p : ℕ) (hp : 0 < p)
    (w : (Fin p → ℤ) → ℝ≥0∞) (f : Lp ℂ 2 (torusMeasure p)) :
    Causalean.Mathlib.Analysis.RealInterpolation.wNorm w Measure.count (reflectionTargetCoefficients p hp f) =
      ENNReal.rpow (∑' k, w k * ENNReal.ofReal (‖UnitAddTorus.mFourierCoeff f k‖ ^ 2)) (1 / 2) := by
  unfold Causalean.Mathlib.Analysis.RealInterpolation.wNorm
  congr 1
  calc
    _ = ∫⁻ k, w k * ENNReal.ofReal (‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) ∂Measure.count := by
      apply lintegral_congr_ae
      filter_upwards [AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff f k)
        (measurable_of_countable _).aestronglyMeasurable] with k hk
      change w k * (‖(AEEqFun.mk _ _) k‖₊ : ℝ≥0∞) ^ 2 = _
      rw [hk, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    _ = _ := lintegral_count _

/-- [ Parseval identifies the zero-order coefficient gauge with the torus norm.](goal) Under [the stated conditions](hyp:hp). -/
-- @node: reflectionTargetCoefficients_zeroNorm
lemma reflectionTargetCoefficients_zeroNorm (p : ℕ) (hp : 0 < p)
    (f : Lp ℂ 2 (torusMeasure p)) :
    Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) Measure.count (reflectionTargetCoefficients p hp f) = ‖f‖ₑ := by
  rw [reflectionTargetCoefficients_wNorm]
  simp only [one_mul]
  have hs := (torusParseval p hp f).2.2.1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs.summable,
    hs.tsum_eq, ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp f).integrable_norm_pow (by norm_num))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  rw [Lp.enorm_def]
  symm
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    enorm_eq_nnnorm, NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.rpow_eq_pow] using
    eLpNorm_nnreal_eq_lintegral (f := fun t => f t) (μ := torusMeasure p)
      (p := 2) (by norm_num)

/-- [ The first-order target gauge is exactly the weighted coefficient gauge.](goal) Under [the stated conditions](hyp:hp). -/
-- @node: reflectionTargetCoefficients_firstNorm
lemma reflectionTargetCoefficients_firstNorm (p : ℕ) (hp : 0 < p)
    (f : Lp ℂ 2 (torusMeasure p)) :
    Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun k => ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)))
      Measure.count (reflectionTargetCoefficients p hp f) = reflectionTorusFirstOrderNorm p f := by
  rw [reflectionTargetCoefficients_wNorm]
  unfold reflectionTorusFirstOrderNorm
  congr 1
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (by unfold frequencySq; positivity : 0 ≤ 1 + Real.pi ^ 2 * frequencySq k / (p : ℝ))]

/-- [ Exact weighted interpolation evaluates the coefficient K norm.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: reflectionTargetCoefficients_kNormSq
lemma reflectionTargetCoefficients_kNormSq (p : ℕ) (hp : 0 < p)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (f : Lp ℂ 2 (torusMeasure p)) :
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) Measure.count)
      (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun k => ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ))) Measure.count)
      s (reflectionTargetCoefficients p hp f) =
      ∑' k, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ^ s *
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
  have hw : ∀ᵐ k : Fin p → ℤ ∂Measure.count,
      0 < (1 : ℝ≥0∞) ∧ (1 : ℝ≥0∞) < ⊤ ∧
      0 < ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ∧
      ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) < ⊤ := by
    filter_upwards [] with k
    refine ⟨by norm_num, by norm_num, ENNReal.ofReal_pos.mpr (by unfold frequencySq; positivity), ENNReal.ofReal_lt_top⟩
  have hsum : ∃ f0 f1 : (Fin p → ℤ) →ₘ[Measure.count] ℂ,
      reflectionTargetCoefficients p hp f = f0 + f1 ∧
      Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) Measure.count f0 < ⊤ ∧
      Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun k => ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ))) Measure.count f1 < ⊤ := by
    refine ⟨reflectionTargetCoefficients p hp f, 0, by simp, ?_, ?_⟩
    · rw [reflectionTargetCoefficients_zeroNorm, Lp.enorm_def]
      exact (Lp.memLp f).2
    · rw [reflection_wNorm_zero]
      exact ENNReal.zero_lt_top
  rw [weighted_l2_interpolation Measure.count _ _ measurable_const
    (measurable_of_countable _) hw s hs _ hsum]
  calc
    _ = ∫⁻ k, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ^ s *
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) ∂Measure.count := by
      apply lintegral_congr_ae
      filter_upwards [AEEqFun.coeFn_mk (fun k => UnitAddTorus.mFourierCoeff f k)
        (measurable_of_countable _).aestronglyMeasurable] with k hk
      change _ * (‖(AEEqFun.mk _ _) k‖₊ : ℝ≥0∞) ^ 2 = _
      rw [hk]
      simp only [ENNReal.rpow_eq_pow, ENNReal.one_rpow, one_mul]
      rw [ENNReal.ofReal_rpow_of_nonneg (by unfold frequencySq; positivity) hs.1.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (by unfold frequencySq; positivity) _), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, enorm_eq_nnnorm]
    _ = _ := lintegral_count _

/-- [ The fractional spectral energy is controlled by the actual torus K norm.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: reflectionTorus_fractionalBudget_le_kNormSq
lemma reflectionTorus_fractionalBudget_le_kNormSq (p : ℕ) (hp : 0 < p)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (f : Lp ℂ 2 (torusMeasure p)) :
    (∑' k, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ^ s *
      ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2)) ≤
      Causalean.Mathlib.Analysis.RealInterpolation.kNormSq (fun g : Lp ℂ 2 (torusMeasure p) => ‖g‖ₑ)
        (reflectionTorusFirstOrderNorm p) s f := by
  rw [← reflectionTargetCoefficients_kNormSq p hp s hs f]
  have h := kNormSq_map_le_of_pos
    (fun g : Lp ℂ 2 (torusMeasure p) => ‖g‖ₑ) (reflectionTorusFirstOrderNorm p)
    (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) Measure.count)
    (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun k => ENNReal.ofReal (1 + Real.pi ^ 2 * frequencySq k / (p : ℝ))) Measure.count)
    (reflectionTargetCoefficients p hp) 1 1 (by norm_num) (by norm_num)
    (fun g => by rw [reflectionTargetCoefficients_zeroNorm]; simp)
    (fun g => by rw [reflectionTargetCoefficients_firstNorm]; simp) s hs f
  simpa using h

/-- [ Both genuine endpoint contractions give the exact fractional reflection budget.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: reflectionProfileOperator_fractionalBudget_le
lemma reflectionProfileOperator_fractionalBudget_le (p : ℕ) (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    (∑' k, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ^ s *
      ‖UnitAddTorus.mFourierCoeff (reflectionProfileOperator p ψ) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) := by
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> omega
  exact (reflectionTorus_fractionalBudget_le_kNormSq p hp0 s hs _).trans
    (reflectionProfileOperator_kNormSq_le_energy p hp s hs ψ)

/-- [ Angular inversion identifies the common profile operator with reflection of
an original admissible spatial extension.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionProfileOperator_fourier_original
lemma reflectionProfileOperator_fourier_original {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    let hF : MemLp (Fourier G) 2 volume := Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    reflectionProfileOperator p (hF.toLp (Fourier G)) =
      reflectionL2Operator p (hG2.toLp G) := by
  dsimp only
  let hF : MemLp (Fourier G) 2 volume := Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  change reflectionL2Operator p
    ((reflectionInverseL2Representative_memLp (hF.toLp (Fourier G))).toLp
      (reflectionInverseL2Representative (hF.toLp (Fourier G)))) = _
  congr 1
  apply Lp.ext
  exact ((reflectionInverseL2Representative_memLp (hF.toLp (Fourier G))).coeFn_toLp).trans
    ((reflectionInverseL2Representative_fourier_ae_original hG1 hG2).trans
      hG2.coeFn_toLp.symm)

/-- [ Each whole-space extension contracts to its exact fractional periodic budget.](goal) Under [the stated conditions](hyp:hp,hs,hG1,hG2). -/
-- @node: reflectionL2Operator_fractionalBudget_le
lemma reflectionL2Operator_fractionalBudget_le {p : ℕ} (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (∑' k, ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencySq k / (p : ℝ)) ^ s *
      ‖UnitAddTorus.mFourierCoeff (reflectionL2Operator p (hG2.toLp G)) k‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) := by
  let hF : MemLp (Fourier G) 2 volume := Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  have h := reflectionProfileOperator_fractionalBudget_le p hp s hs (hF.toLp (Fourier G))
  rw [reflectionProfileOperator_fourier_original hG1 hG2] at h
  refine h.trans_eq ?_
  apply lintegral_congr_ae
  filter_upwards [hF.coeFn_toLp] with ω hω
  rw [hω]

/-- [ Infimizing over extensions completes the fractional component contraction.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: componentFourierBudget_fractional_le
lemma componentFourierBudget_fractional_le (p : ℕ) (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (g : Cube p → ℝ) :
    componentFourierBudget p s g ≤ sobolevNormSq p s g := by
  unfold sobolevNormSq
  refine le_iInf fun G => le_iInf fun hG => ?_
  have h := reflectionL2Operator_fractionalBudget_le hp s hs hG.1 hG.2.1
  simp_rw [reflectionTorusCoeff_extension hG.2.1 g hG.2.2] at h
  simpa only [componentFourierBudget, mul_comm] using h

/-- [ The complete component reflection contraction, including the first-order
endpoint, has constant one in each local dimension.](goal) Under [the stated conditions](hyp:hp,hs,hs1). -/
-- @node: componentFourierBudget_le_sobolevNormSq
lemma componentFourierBudget_le_sobolevNormSq (p : ℕ) (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (g : Cube p → ℝ) :
    componentFourierBudget p s g ≤ sobolevNormSq p s g := by
  by_cases hendpoint : s = 1
  · subst s
    rcases hp with rfl | rfl
    · exact componentFourierBudget_one_firstOrder_le g
    · exact componentFourierBudget_two_firstOrder_le g
  · exact componentFourierBudget_fractional_le p hp s
      ⟨hs, lt_of_le_of_ne hs1 hendpoint⟩ g

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionEndpointZero
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Face cancellation for the first-order reflection endpoint

On the period-two representative interval, a smooth cube slice is reflected at
one. Its signed derivative satisfies integration by parts against periodic
smooth tests: the internal face cancels, and the two external faces cancel
using periodicity of the test alone. The cube slice has no boundary condition.
Parseval then proves the one-dimensional smooth first-order spectral endpoint
with constant one. These establish equations (4) and (5) of the reflection-budget
roadmap on slices, before Fourier truncation and completion.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The even reflected slice on the period-two representative interval. -/
-- @node: evenReflectionSlice
def evenReflectionSlice (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  if y ≤ 1 then f y else f (2 - y)

/-- The derivative on reflected open cells has opposite signs on the two halves. -/
-- @node: signedReflectionSlice
def signedReflectionSlice (f' : ℝ → ℂ) (y : ℝ) : ℂ :=
  if y ≤ 1 then f' y else -f' (2 - y)

/-- Splitting a two-cell integral is valid even if its two formulas disagree on the join.](goal) Under [the stated conditions](hyp:h₀,h₁). This uses [the stated conclusion](goal). -/
-- @node: reflectionCells_integral_split
lemma reflectionCells_integral_split {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f₀ f₁ : ℝ → E}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) :
    (∫ y in (0 : ℝ)..2, if y ≤ 1 then f₀ y else f₁ y) =
      (∫ y in (0 : ℝ)..1, f₀ y) + ∫ y in (1 : ℝ)..2, f₁ y := by
  have hi₀ : IntervalIntegrable (fun y => if y ≤ 1 then f₀ y else f₁ y)
      volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo ?_).mpr (h₀.intervalIntegrable 0 1)
    intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo] using hy
    simp [hy'.2.le]
  have hi₁ : IntervalIntegrable (fun y => if y ≤ 1 then f₀ y else f₁ y)
      volume 1 2 := by
    apply (intervalIntegrable_congr_uIoo ?_).mpr (h₁.intervalIntegrable 1 2)
    intro y hy
    have hy' : y ∈ Ioo (1 : ℝ) 2 := by simpa [uIoo] using hy
    simp [not_le.mpr hy'.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁]
  congr 1
  · apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun y hy => by
      have hy' : y ∈ Ioc (0 : ℝ) 1 := by simpa using hy
      simp [hy'.2])
  · apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun y hy => by
      have hy' : y ∈ Ioc (1 : ℝ) 2 := by simpa using hy
      simp [not_le.mpr hy'.1])

/-- [ Reflecting a differentiable slice reverses its derivative on the second cell.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: reflectedSlice_hasDerivAt
lemma reflectedSlice_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {y : ℝ}
    (hf : HasDerivAt f f' (2 - y)) :
    HasDerivAt (fun t => f (2 - t)) (-f') y := by
  simpa using! hf.scomp y ((hasDerivAt_id y).const_sub 2)

/-- [ Integration by parts cancels both reflected faces. Only the test values at zero and
 two must agree; no equality between the cube function's values at zero and one is used.](goal) Under [the stated conditions](hyp:hf,hf',hv,hv',hperiod). -/
-- @node: evenReflectionSlice_integration_by_parts
lemma evenReflectionSlice_integration_by_parts {f f' v v' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v')
    (hperiod : v 2 = v 0) :
    (∫ y in (0 : ℝ)..2, evenReflectionSlice f y * v' y) =
      -(∫ y in (0 : ℝ)..2, signedReflectionSlice f' y * v y) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun x => (hv x).continuousAt)
  have hrc : Continuous (fun y => f (2 - y)) := by fun_prop
  have hrd : Continuous (fun y => -f' (2 - y)) := by fun_prop
  have hleft := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfc.continuousOn hvc.continuousOn (fun x _ => hf x) (fun x _ => hv x)
    (hf'.intervalIntegrable 0 1) (hv'.intervalIntegrable 0 1)
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hrc.continuousOn hvc.continuousOn (fun x _ => reflectedSlice_hasDerivAt (hf (2 - x)))
    (fun x _ => hv x) (hrd.intervalIntegrable 1 2) (hv'.intervalIntegrable 1 2)
  simp only [evenReflectionSlice, signedReflectionSlice, ite_mul]
  have hi := reflectionCells_integral_split (hfc.mul hv') (hrc.mul hv')
  have hj := reflectionCells_integral_split (hf'.mul hvc) (hrd.mul hvc)
  simp only [Pi.mul_apply] at hi hj
  rw [hi, hj, hleft, hright]
  norm_num only at *
  rw [hperiod]
  ring

/-- [ The normalized reflected L² energy is exactly the cube-slice energy.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: evenReflectionSlice_energy
lemma evenReflectionSlice_energy {f : ℝ → ℂ} (hf : Continuous f) :
    (1 / 2 : ℝ) * (∫ y in (0 : ℝ)..2, ‖evenReflectionSlice f y‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  have h₀ : Continuous (fun y => ‖f y‖ ^ 2) := by fun_prop
  have h₁ : Continuous (fun y => ‖f (2 - y)‖ ^ 2) := by fun_prop
  simp only [evenReflectionSlice, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]
  rw [reflectionCells_integral_split h₀ h₁,
    intervalIntegral.integral_comp_sub_left (fun y => ‖f y‖ ^ 2) 2]
  norm_num
  ring

/-- [ The sign reversal preserves the normalized derivative energy, with constant one.](goal) Under [the stated conditions](hyp:hf'). -/
-- @node: signedReflectionSlice_energy
lemma signedReflectionSlice_energy {f' : ℝ → ℂ} (hf' : Continuous f') :
    (1 / 2 : ℝ) * (∫ y in (0 : ℝ)..2, ‖signedReflectionSlice f' y‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ‖f' x‖ ^ 2 := by
  have he : (fun y => ‖signedReflectionSlice f' y‖ ^ 2) =
      fun y => ‖evenReflectionSlice f' y‖ ^ 2 := by
    funext y
    simp only [signedReflectionSlice, evenReflectionSlice]
    split_ifs <;> simp
  rw [he]
  exact evenReflectionSlice_energy hf'

/-- [ Fourier coefficients on the period-two representative interval use normalized Haar mass. -/
-- @node: periodTwoSliceCoeff
def periodTwoSliceCoeff (f : ℝ → ℂ) (a : ℤ) : ℂ :=
  (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, fourier (-a) (y : AddCircle (2 : ℝ)) * f y

/-- Testing the cancelled slice identity with a character gives the exact derivative
multiplier, including zero frequency.](goal) Under [the stated conditions](hyp:hf,hf'). This uses [the stated conclusion](goal). -/
-- @node: signedReflectionSlice_fourierCoeff
lemma signedReflectionSlice_fourierCoeff {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (a : ℤ) :
    periodTwoSliceCoeff (signedReflectionSlice f') a =
      Complex.I * (Real.pi : ℂ) * (a : ℂ) *
        periodTwoSliceCoeff (evenReflectionSlice f) a := by
  let v : ℝ → ℂ := fun y => fourier (-a) (y : AddCircle (2 : ℝ))
  let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / 2
  have hv (y : ℝ) : HasDerivAt v (c * v y) y :=
    hasDerivAt_fourier_neg 2 a y
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun y => (hv y).continuousAt)
  have hv' : Continuous (fun y => c * v y) := by fun_prop
  have hp : v 2 = v 0 := by
    change fourier (-a) ((2 : ℝ) : AddCircle (2 : ℝ)) =
      fourier (-a) (0 : AddCircle (2 : ℝ))
    rw [AddCircle.coe_period]
  have h := evenReflectionSlice_integration_by_parts hf hf' hv hv' hp
  have hl : (∫ y in (0 : ℝ)..2, evenReflectionSlice f y * (c * v y)) =
      c * ∫ y in (0 : ℝ)..2, v y * evenReflectionSlice f y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hr : (∫ y in (0 : ℝ)..2, signedReflectionSlice f' y * v y) =
      ∫ y in (0 : ℝ)..2, v y * signedReflectionSlice f' y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hl, hr] at h
  dsimp only [periodTwoSliceCoeff, v, c] at h ⊢
  linear_combination (1 / 2 : ℂ) * h

/-- [ The zeroth and derivative energies add without loss under normalized even reflection.](goal) Under [the stated conditions](hyp:hf,hf'). -/
-- @node: evenReflectionSlice_firstOrder_energy
lemma evenReflectionSlice_firstOrder_energy {f f' : ℝ → ℂ}
    (hf : Continuous f) (hf' : Continuous f') :
    (1 / 2 : ℝ) * ((∫ y in (0 : ℝ)..2, ‖evenReflectionSlice f y‖ ^ 2) +
      ∫ y in (0 : ℝ)..2, ‖signedReflectionSlice f' y‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖f' x‖ ^ 2 := by
  rw [mul_add, evenReflectionSlice_energy hf, signedReflectionSlice_energy hf']

/-- [ Continuous cell formulas give Lp regularity on the finite representative interval,
even when the signed derivative jumps at the reflection face.](goal) Under [the stated conditions](hyp:h₀,h₁,q). -/
-- @node: reflectionCells_memLp
lemma reflectionCells_memLp {f₀ f₁ : ℝ → ℂ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (q : ℝ≥0∞) :
    MemLp (fun y => if y ≤ 1 then f₀ y else f₁ y) q
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 2)).bddAbove_image
    h₀.norm.continuousOn
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 2)).bddAbove_image
    h₁.norm.continuousOn
  apply MemLp.of_bound (C := max C₀ C₁)
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite measurableSet_Iic h₀.measurable h₁.measurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyc : y ∈ Icc (0 : ℝ) 2 := ⟨hy.1.le, hy.2⟩
    by_cases h : y ≤ 1
    · simp only [if_pos h]
      exact (hC₀ ⟨y, hyc, rfl⟩).trans (le_max_left _ _)
    · simp only [if_neg h]
      exact (hC₁ ⟨y, hyc, rfl⟩).trans (le_max_right _ _)

/-- The local slice normalization agrees with Mathlib's interval Fourier coefficients. [The asserted mathematical result follows](goal). -/
-- @node: periodTwoSliceCoeff_eq_fourierCoeffOn
lemma periodTwoSliceCoeff_eq_fourierCoeffOn (f : ℝ → ℂ) (a : ℤ) :
    periodTwoSliceCoeff f a = fourierCoeffOn (by norm_num : (0 : ℝ) < 2) f a := by
  rw [fourierCoeffOn_eq_integral]
  simp only [periodTwoSliceCoeff, sub_zero, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, smul_eq_mul]
  simp only [fourier_coe_apply, sub_zero]

/-- Squaring the exact derivative multiplier supplies the first-order Fourier weight. Under [the stated conditions](hyp:hf,hf'), [the asserted mathematical result follows](goal). -/
-- @node: signedReflectionSlice_fourierCoeff_normSq
lemma signedReflectionSlice_fourierCoeff_normSq {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (a : ℤ) :
    ‖periodTwoSliceCoeff (signedReflectionSlice f') a‖ ^ 2 =
      Real.pi ^ 2 * (a : ℝ) ^ 2 * ‖periodTwoSliceCoeff (evenReflectionSlice f) a‖ ^ 2 := by
  rw [signedReflectionSlice_fourierCoeff hf hf']
  simp [mul_pow, Complex.norm_intCast, Real.norm_eq_abs, sq_abs]

/-- [ Parseval on the function and its signed weak derivative proves the smooth,
one-dimensional first-order endpoint with the exact constant one.](goal) Under [the stated conditions](hyp:hf,hf'). -/
-- @node: evenReflectionSlice_firstOrder_parseval
lemma evenReflectionSlice_firstOrder_parseval {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    HasSum (fun a : ℤ => (1 + Real.pi ^ 2 * (a : ℝ) ^ 2) *
      ‖periodTwoSliceCoeff (evenReflectionSlice f) a‖ ^ 2)
      ((∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖f' x‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hrc : Continuous (fun y => f (2 - y)) := by fun_prop
  have hrd : Continuous (fun y => -f' (2 - y)) := by fun_prop
  have hL : MemLp (evenReflectionSlice f) 2 (volume.restrict (Ioc (0 : ℝ) 2)) :=
    reflectionCells_memLp hfc hrc 2
  have hD : MemLp (signedReflectionSlice f') 2 (volume.restrict (Ioc (0 : ℝ) 2)) :=
    reflectionCells_memLp hf' hrd 2
  have h₀ := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 2) hL
  have h₁ := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 2) hD
  simp only [← periodTwoSliceCoeff_eq_fourierCoeffOn, sub_zero, inv_eq_one_div,
    smul_eq_mul, evenReflectionSlice_energy hfc, signedReflectionSlice_energy hf'] at h₀ h₁
  convert h₀.add h₁ using 1
  funext a
  rw [signedReflectionSlice_fourierCoeff_normSq hf hf']
  ring

/-- [ Restricting the smooth one-dimensional endpoint energy to the cube is a contraction
from whole-space spatial H¹ energy, independently of the two original face values.](goal) Under [the stated conditions](hyp:hf,hf',hL,hD). -/
-- @node: evenReflectionSlice_firstOrder_le_wholeSpace
lemma evenReflectionSlice_firstOrder_le_wholeSpace {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hL : MemLp f 2 volume) (hD : MemLp f' 2 volume) :
    (∑' a : ℤ, (1 + Real.pi ^ 2 * (a : ℝ) ^ 2) *
      ‖periodTwoSliceCoeff (evenReflectionSlice f) a‖ ^ 2) ≤
      (∫ x : ℝ, ‖f x‖ ^ 2) + ∫ x : ℝ, ‖f' x‖ ^ 2 := by
  rw [(evenReflectionSlice_firstOrder_parseval hf hf').tsum_eq]
  have hi := hL.integrable_norm_pow (by norm_num)
  have hd := hD.integrable_norm_pow (by norm_num)
  have h₀ : (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤ ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
  have h₁ : (∫ x in (0 : ℝ)..1, ‖f' x‖ ^ 2) ≤ ∫ x : ℝ, ‖f' x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_le_integral hd (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f' x‖))
  exact add_le_add h₀ h₁

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic
public import Causalean.Mathlib.Analysis.RealInterpolation.Pointwise

/-!
# The quadratic K-functional of weighted L² spaces

Pointwise completion of the square gives a lower bound for every decomposition
and an explicit measurable minimizing decomposition. Their combination evaluates
the K-functional as harmonic-weight energy on any measure space, even when the
energy is infinite. Scalar normalization and Tonelli are separate later layers.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- Conversion of a nonnegative real weighted energy to extended energy. -/
private theorem ofReal_energy (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ENNReal.ofReal (a * ‖z‖ ^ 2) = ENNReal.ofReal a * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_pow (norm_nonneg z)]
  rw [ofReal_norm, enorm_eq_nnnorm]

/-- Finite positive weights identify the harmonic extended weight with its real formula. -/
private theorem harmonicWeight_real (a b : ℝ≥0∞) (ha : a < ⊤) (hb : b < ⊤)
    (hapos : 0 < a) (hbpos : 0 < b) (t : ℝ) (ht : 0 < t) :
    harmonicWeight a b t =
      ENNReal.ofReal (a.toReal * (t ^ 2 * b.toReal) / (a.toReal + t ^ 2 * b.toReal)) := by
  have ha' : 0 < a.toReal := ENNReal.toReal_pos_iff.mpr ⟨hapos, ha⟩
  have hb' : 0 < t ^ 2 * b.toReal :=
    mul_pos (sq_pos_of_pos ht) (ENNReal.toReal_pos_iff.mpr ⟨hbpos, hb⟩)
  rw [harmonicWeight, ENNReal.ofReal_div_of_pos (add_pos ha' hb'),
    ENNReal.ofReal_mul ha'.le, ENNReal.ofReal_add ha'.le hb'.le,
    ENNReal.ofReal_mul (sq_nonneg t), ENNReal.ofReal_toReal ha.ne,
    ENNReal.ofReal_toReal hb.ne]

/-- Decomposition cost is the integral of the sum of its extended energy densities. -/
private theorem cost_integral {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞) (hw0 : Measurable w0)
    (t : ℝ) (f0 f1 : S →ₘ[μ] ℂ) :
    wNorm w0 μ f0 ^ 2 + ENNReal.ofReal (t ^ 2) * wNorm w1 μ f1 ^ 2 =
      ∫⁻ x, w0 x * (‖f0 x‖₊ : ℝ≥0∞) ^ 2 +
        ENNReal.ofReal (t ^ 2) * (w1 x * (‖f1 x‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  rw [wNorm_sq, wNorm_sq, lintegral_add_left',
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hw0.aemeasurable.mul (f0.aestronglyMeasurable.enorm.pow_const 2)

/-- [Measurable weights](hyp:w0,w1,hw0,hw1) that are [positive finite almost
everywhere](hyp:hw) give [a pointwise-minimum lower bound on each decomposition's
quadratic weighted energy](goal), at [a positive scale](hyp:t,ht) for
[a decomposition modulo null sets](hyp:f,f0,f1,hf).
Use wNorm_sq, the almost-everywhere addition rule, harmonic_quadratic_le,
and monotonicity and addition of nonnegative integrals. -/
theorem harmonic_energy_le_cost {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (t : ℝ) (ht : 0 < t) (f f0 f1 : S →ₘ[μ] ℂ) (hf : f = f0 + f1) :
    (∫⁻ x, harmonicWeight (w0 x) (w1 x) t * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤
      wNorm w0 μ f0 ^ 2 + ENNReal.ofReal (t ^ 2) * wNorm w1 μ f1 ^ 2 := by
  rw [cost_integral μ w0 w1 hw0 t f0 f1]
  apply lintegral_mono_ae
  filter_upwards [hw, AEEqFun.coeFn_add f0 f1] with x hx hadd
  have ha : 0 < (w0 x).toReal := ENNReal.toReal_pos_iff.mpr ⟨hx.1, hx.2.1⟩
  have hb : 0 < t ^ 2 * (w1 x).toReal :=
    mul_pos (sq_pos_of_pos ht) (ENNReal.toReal_pos_iff.mpr ⟨hx.2.2.1, hx.2.2.2⟩)
  have h := ENNReal.ofReal_le_ofReal
    (harmonic_quadratic_le _ _ ha hb (f0 x) (f1 x))
  rw [ENNReal.ofReal_add (mul_nonneg ha.le (sq_nonneg _))
    (mul_nonneg hb.le (sq_nonneg _)), ofReal_energy _ ha.le,
    ofReal_energy _ hb.le, ENNReal.ofReal_mul (sq_nonneg t),
    ENNReal.ofReal_toReal hx.2.1.ne, ENNReal.ofReal_toReal hx.2.2.2.ne,
    ofReal_energy _ (div_nonneg (mul_nonneg ha.le hb.le) (add_nonneg ha.le hb.le))] at h
  rw [harmonicWeight_real _ _ hx.2.1 hx.2.2.2 hx.1 hx.2.2.1 t ht, hf, hadd]
  simpa only [mul_assoc, Pi.add_apply] using h

/-- [Measurable weights](hyp:w0,w1,hw0,hw1) that are [positive finite almost
everywhere](hyp:hw) give [a measurable minimizing decomposition](goal) of
[any measurable complex function modulo null sets](hyp:f), at [a positive scale](hyp:t,ht).

Construct f0=(t²*w1.toReal)/(w0.toReal+t²*w1.toReal) times f and f1=f-f0
as AEEqFun.mk of measurable representatives. Bad weights on a null set cause no
problem. Use harmonic_quadratic_attained for equality of the integrands; endpoint
energies may be infinite, since this lemma has no finite-energy conclusion. -/
theorem exists_harmonic_minimizer {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (t : ℝ) (ht : 0 < t) (f : S →ₘ[μ] ℂ) :
    ∃ f0 f1 : S →ₘ[μ] ℂ, f = f0 + f1 ∧
      wNorm w0 μ f0 ^ 2 + ENNReal.ofReal (t ^ 2) * wNorm w1 μ f1 ^ 2 =
        ∫⁻ x, harmonicWeight (w0 x) (w1 x) t * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  let a : S → ℝ := fun x => (w0 x).toReal
  let b : S → ℝ := fun x => t ^ 2 * (w1 x).toReal
  have hma : Measurable a := hw0.ennreal_toReal
  have hmb : Measurable b := measurable_const.mul hw1.ennreal_toReal
  let g0 : S → ℂ := fun x => (b x / (a x + b x)) • f x
  let g1 : S → ℂ := fun x => (a x / (a x + b x)) • f x
  have hm0 : AEStronglyMeasurable g0 μ :=
    ((hmb.div (hma.add hmb)).aestronglyMeasurable).smul f.aestronglyMeasurable
  have hm1 : AEStronglyMeasurable g1 μ :=
    ((hma.div (hma.add hmb)).aestronglyMeasurable).smul f.aestronglyMeasurable
  let f0 : S →ₘ[μ] ℂ := AEEqFun.mk g0 hm0
  let f1 : S →ₘ[μ] ℂ := AEEqFun.mk g1 hm1
  have he0 : f0 =ᵐ[μ] g0 := AEEqFun.coeFn_mk g0 hm0
  have he1 : f1 =ᵐ[μ] g1 := AEEqFun.coeFn_mk g1 hm1
  refine ⟨f0, f1, ?_, ?_⟩
  · apply AEEqFun.ext
    filter_upwards [hw, he0, he1, AEEqFun.coeFn_add f0 f1] with x hx h0 h1 hadd
    have ha : 0 < a x := ENNReal.toReal_pos_iff.mpr ⟨hx.1, hx.2.1⟩
    have hb : 0 < b x :=
      mul_pos (sq_pos_of_pos ht) (ENNReal.toReal_pos_iff.mpr ⟨hx.2.2.1, hx.2.2.2⟩)
    rw [hadd]
    change f x = f0 x + f1 x
    rw [h0, h1]
    exact (harmonic_quadratic_attained _ _ ha hb (f x)).1
  · rw [cost_integral μ w0 w1 hw0 t f0 f1]
    apply lintegral_congr_ae
    filter_upwards [hw, he0, he1] with x hx h0 h1
    have ha : 0 < a x := ENNReal.toReal_pos_iff.mpr ⟨hx.1, hx.2.1⟩
    have hb : 0 < b x :=
      mul_pos (sq_pos_of_pos ht) (ENNReal.toReal_pos_iff.mpr ⟨hx.2.2.1, hx.2.2.2⟩)
    have h := congrArg ENNReal.ofReal
      (harmonic_quadratic_attained _ _ ha hb (f x)).2
    rw [ENNReal.ofReal_add (mul_nonneg ha.le (sq_nonneg _))
      (mul_nonneg hb.le (sq_nonneg _)), ofReal_energy _ ha.le,
      ofReal_energy _ hb.le,
      ofReal_energy _ (div_nonneg (mul_nonneg ha.le hb.le) (add_nonneg ha.le hb.le))] at h
    dsimp only [a, b] at h
    rw [ENNReal.ofReal_mul (sq_nonneg t), ENNReal.ofReal_toReal hx.2.1.ne,
      ENNReal.ofReal_toReal hx.2.2.2.ne] at h
    rw [harmonicWeight_real _ _ hx.2.1 hx.2.2.2 hx.1 hx.2.2.1 t ht, h0, h1]
    simpa only [g0, g1, a, b, mul_assoc] using h

/-- [Measurable weights](hyp:w0,w1,hw0,hw1) that are [positive finite almost
everywhere](hyp:hw) give [the harmonic-weight formula for the squared K-functional](goal)
of [any measurable function modulo null sets](hyp:f), at [a positive scale](hyp:t,ht).
Combine the preceding lower bound and attained upper bound by the infimum rules. -/
theorem kFunctionalSq_wNorm {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (t : ℝ) (ht : 0 < t) (f : S →ₘ[μ] ℂ) :
    kFunctionalSq (wNorm w0 μ) (wNorm w1 μ) t f =
      ∫⁻ x, harmonicWeight (w0 x) (w1 x) t * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  apply le_antisymm
  · obtain ⟨f0, f1, hf, he⟩ := exists_harmonic_minimizer μ w0 w1 hw0 hw1 hw t ht f
    unfold kFunctionalSq
    exact iInf_le_of_le f0 (iInf_le_of_le f1 (iInf_le_of_le hf he.le))
  · unfold kFunctionalSq
    refine le_iInf fun f0 => le_iInf fun f1 => le_iInf fun hf => ?_
    exact harmonic_energy_le_cost μ w0 w1 hw0 hw1 hw t ht f f0 f1 hf

end Causalean.Mathlib.Analysis.RealInterpolation

module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineExtension
public import Mathlib.MeasureTheory.Integral.MeanInequalities
/-! # Fractional Fourier energy of cutoff extensions

The cosine-prior roadmap interpolates its zero- and first-order whole-space
energy estimates by Hölder's inequality. This file proves that step for the
paper's angular-frequency transform, including zero-energy and endpoint cases.
The weak-derivative identities and endpoint estimates remain separate obligations.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators FourierTransform
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
/-- [ The angular-frequency transform equals Mathlib's transform at the rescaled frequency, with
the unitary normalization.](goal) -/
-- @node: Fourier_eq_scaled
lemma Fourier_eq_scaled {p : ℕ} (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (ω : EuclideanSpace ℝ (Fin p)) :
    Fourier G ω = (2 * Real.pi) ^ (-(p : ℝ) / 2) •
      𝓕 G (((2 * Real.pi)⁻¹ : ℝ) • ω) := by
  unfold Fourier
  congr 1
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  congr 2
  simp only [inner_smul_right, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- [ An integrable extension has a continuous angular-frequency Fourier transform. This uses [the hG hypothesis](hyp:hG), [the stated conclusion](goal). -/
-- @node: Fourier_continuous
@[fun_prop] lemma Fourier_continuous {p : ℕ} {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG : Integrable G volume) : Continuous (Fourier G) := by
  have hc : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hG
  have he : Fourier G = fun ω => (2 * Real.pi) ^ (-(p : ℝ) / 2) •
      𝓕 G (((2 * Real.pi)⁻¹ : ℝ) • ω) := funext (Fourier_eq_scaled G)
  rw [he]
  fun_prop

/-- The squared whole-space Fourier energy at a local Sobolev exponent. -/
-- @node: extensionFourierEnergy
def extensionFourierEnergy (p : ℕ) (s : ℝ)
    (G : EuclideanSpace ℝ (Fin p) → ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)

/-- The weighted real energy density factors into nonnegative extended-real factors.](goal) This uses [the stated conclusion](goal). -/
-- @node: extensionFourierEnergy_density
lemma extensionFourierEnergy_density {p : ℕ} (s : ℝ)
    (G : EuclideanSpace ℝ (Fin p) → ℂ) (ω : EuclideanSpace ℝ (Fin p)) :
    ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) =
      ENNReal.ofReal (‖Fourier G ω‖ ^ 2) *
        ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s := by
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_rpow_of_pos (by positivity)]

/-- Hölder interpolates the zero- and first-order extension energies, including both endpoints
and zero energy. Under [the stated conditions](hyp:hs,hs1,hG), [the asserted mathematical result follows](goal). -/
-- @node: extensionFourierEnergy_interpolation
lemma extensionFourierEnergy_interpolation {p : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG : Integrable G volume) :
    extensionFourierEnergy p s G ≤
      extensionFourierEnergy p 0 G ^ (1 - s) * extensionFourierEnergy p 1 G ^ s := by
  let f := fun ω => ENNReal.ofReal (‖Fourier G ω‖ ^ 2)
  let w := fun ω : EuclideanSpace ℝ (Fin p) =>
    ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ))
  have hf : AEMeasurable f volume := by dsimp [f]; fun_prop
  have hfw : AEMeasurable (fun ω => f ω * w ω) volume := by dsimp [f, w]; fun_prop
  have he (ω : EuclideanSpace ℝ (Fin p)) :
      f ω ^ (1 - s) * (f ω * w ω) ^ s = f ω * w ω ^ s := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs, ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hs1) hs]
    simp
  have h := ENNReal.lintegral_mul_norm_pow_le hf hfw
    (sub_nonneg.mpr hs1) hs (by ring : 1 - s + s = 1)
  simp_rw [he] at h
  simpa only [extensionFourierEnergy, extensionFourierEnergy_density,
    ENNReal.rpow_zero, ENNReal.rpow_one, mul_one, f, w] using h

/-- [ Zero-order energy at most A and first-order energy at most A times the squared cutoff give
fractional energy at most A times the cutoff to power twice the smoothness.](goal) Under [the stated conditions](hyp:hs,hs1,hL,hG,A,h0,h1). -/
-- @node: extensionFourierEnergy_le_of_endpoints
lemma extensionFourierEnergy_le_of_endpoints {p : ℕ} {s L : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hL : 0 ≤ L)
    {G : EuclideanSpace ℝ (Fin p) → ℂ} (hG : Integrable G volume)
    (A : ℝ≥0∞) (h0 : extensionFourierEnergy p 0 G ≤ A)
    (h1 : extensionFourierEnergy p 1 G ≤ A * ENNReal.ofReal (L ^ 2)) :
    extensionFourierEnergy p s G ≤ A * ENNReal.ofReal ((L ^ s) ^ 2) := by
  have hpow : (L ^ 2) ^ s = (L ^ s) ^ 2 := by
    rw [← Real.rpow_natCast_mul hL, mul_comm, Real.rpow_mul_natCast hL]
  calc
    extensionFourierEnergy p s G ≤
        extensionFourierEnergy p 0 G ^ (1 - s) * extensionFourierEnergy p 1 G ^ s :=
      extensionFourierEnergy_interpolation hs hs1 hG
    _ ≤ A ^ (1 - s) * (A * ENNReal.ofReal (L ^ 2)) ^ s := by
      exact mul_le_mul' (ENNReal.rpow_le_rpow h0 (sub_nonneg.mpr hs1))
        (ENNReal.rpow_le_rpow h1 hs)
    _ = A * ENNReal.ofReal ((L ^ s) ^ 2) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs, ← mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hs1) hs]
      simp only [sub_add_cancel, ENNReal.rpow_one]
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hs, hpow]

/-- [ The roadmap's two endpoint estimates for the explicit cutoff extension imply the required
pair restriction bound; the endpoint estimates are explicit remaining proof obligations.](goal) Under [the stated conditions](hyp:hg,hs,hs1,H,h0,h1). -/
-- @node: cosinePair_restriction_bound_of_endpoints
lemma cosinePair_restriction_bound_of_endpoints {g : Cube 2 → ℝ}
    (hg : Continuous g) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (L : ℕ) (H : ℝ≥0∞)
    (h0 : extensionFourierEnergy 2 0 (cosinePairExtension g) ≤ 16 * H)
    (h1 : extensionFourierEnergy 2 1 (cosinePairExtension g) ≤
      ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal ((L : ℝ) ^ 2) * H) :
    sobolevNormSq 2 s g ≤ ENNReal.ofReal (C0 ^ 2 * ((L : ℝ) ^ s) ^ 2) * H := by
  have hC : (16 : ℝ) ≤ C0 ^ 2 := by
    rw [C0, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg Real.pi]
  have h0' : extensionFourierEnergy 2 0 (cosinePairExtension g) ≤
      ENNReal.ofReal (C0 ^ 2) * H :=
    h0.trans (mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal hC) le_rfl)
  have h1' : extensionFourierEnergy 2 1 (cosinePairExtension g) ≤
      (ENNReal.ofReal (C0 ^ 2) * H) * ENNReal.ofReal ((L : ℝ) ^ 2) := by
    simpa only [mul_assoc, mul_comm H] using h1
  have h := extensionFourierEnergy_le_of_endpoints hs.le hs1 (Nat.cast_nonneg L)
    (cosinePairExtension_admissible hg).1 _ h0' h1'
  apply (sobolevNormSq_le_extension_energy s g _ (cosinePairExtension_admissible hg)).trans
  simpa only [extensionFourierEnergy, ENNReal.ofReal_mul (sq_nonneg C0),
    mul_assoc, mul_comm H] using h
end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.Estimator
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ClipBounds

/-! # Clipping bias and squared-error contraction

The clipping step in roadmap equation (28) contracts squared error around an
in-interval polynomial mean. Its change in expectation is controlled by the
second moment around the clipping center divided by the clipping width. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Stat.Sample.Stratified.TreatmentRegression (clip clip_sq_error_le)

-- @node: centeredClip_eq
/-- Translating symmetric clipping gives the interval used by the cell estimator. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma centeredClip_eq (c A z : ℝ) :
    max (c - A) (min (c + A) z) = c + clip A (z - c) := by
  simp only [clip, add_max, add_min]
  congr 1
  congr 1
  ring

/-- The paper's cell clipping contracts squared error at every target in its interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth,hp), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_sq_error_le (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) (p : ℝ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
    (hp : |p - armwiseExtensionFormula ε c| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    (clippedCellValueFormula ε K d m c r Ne - p) ^ 2 ≤
      (factorialCellValue ε K m c r Ne - p) ^ 2 := by
  rw [clippedCellValueFormula, centeredClip_eq]
  have h := clip_sq_error_le
    ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
    (factorialCellValue ε K m c r Ne - armwiseExtensionFormula ε c)
    (p - armwiseExtensionFormula ε c) hwidth (abs_le.mp hp)
  convert h using 1 <;> congr 1 <;> ring

-- @node: clip_displacement_le_sq_div
/-- A positive clipping width controls clipping displacement by a quadratic tail scale. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA), the [stated conclusion](goal) holds. -/
lemma clip_displacement_le_sq_div {A z : ℝ} (hA : 0 < A) :
    |clip A z - z| ≤ z ^ 2 / A := by
  apply (le_div_iff₀ hA).2
  by_cases hlo : z < -A
  · have hmin : min A z = z := min_eq_right (by linarith)
    rw [clip, hmin, max_eq_left hlo.le, abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (z + A)]
  · by_cases hhi : A < z
    · rw [clip, min_eq_left hhi.le, max_eq_right (by linarith),
        abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (z - A)]
    · rw [clip, min_eq_right (le_of_not_gt hhi), max_eq_right (le_of_not_gt hlo)]
      simp only [sub_self, abs_zero, zero_mul]
      exact sq_nonneg z

/-- The exact cell statistic obeys the quadratic clipping-displacement bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_displacement_le (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ)
    (hwidth : 0 < (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    |clippedCellValueFormula ε K d m c r Ne - factorialCellValue ε K m c r Ne| ≤
      (factorialCellValue ε K m c r Ne - armwiseExtensionFormula ε c) ^ 2 /
        ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) := by
  rw [clippedCellValueFormula, centeredClip_eq]
  convert clip_displacement_le_sq_div
    (z := factorialCellValue ε K m c r Ne - armwiseExtensionFormula ε c) hwidth using 1
  congr 1
  ring

-- @node: centeredClip_integral_bias_le
/-- Integrating the displacement bound gives the clipping bias in equation (28). The second moment is an input to this transfer lemma, rather than an assumed risk rate. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hZ,hsecond), the [stated conclusion](goal) holds. -/
lemma centeredClip_integral_bias_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → ℝ) (c A : ℝ) (hA : 0 < A)
    (hZ : Integrable Z μ)
    (hsecond : Integrable (fun ω => (Z ω - c) ^ 2) μ) :
    |(∫ ω, max (c - A) (min (c + A) (Z ω)) ∂μ) - ∫ ω, Z ω ∂μ| ≤
      (∫ ω, (Z ω - c) ^ 2 ∂μ) / A := by
  have hT : Integrable (fun ω => max (c - A) (min (c + A) (Z ω))) μ :=
    (integrable_const (c - A)).sup ((integrable_const (c + A)).inf hZ)
  rw [← integral_sub hT hZ]
  calc
    _ ≤ ∫ ω, |max (c - A) (min (c + A) (Z ω)) - Z ω| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, (Z ω - c) ^ 2 / A ∂μ := by
      apply integral_mono (hT.sub hZ).abs (hsecond.div_const A)
      intro ω
      change |max (c - A) (min (c + A) (Z ω)) - Z ω| ≤ (Z ω - c) ^ 2 / A
      rw [centeredClip_eq]
      convert clip_displacement_le_sq_div (z := Z ω - c) hA using 1
      congr 1
      ring
    _ = _ := by simp only [integral_div]

-- @node: projectUnit_sq_error_le
/-- Projection to the unit interval contracts the loss relative to the observed target. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma projectUnit_sq_error_le {z p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (projectUnit z - p) ^ 2 ≤ (z - p) ^ 2 := by
  have heq : projectUnit z = (1 / 2 : ℝ) + clip (1 / 2) (z - 1 / 2) := by
    convert centeredClip_eq (1 / 2) (1 / 2) z using 1
    norm_num [projectUnit]
  rw [heq]
  have h := clip_sq_error_le (1 / 2) (z - 1 / 2) (p - 1 / 2)
    (by norm_num) (by constructor <;> linarith [hp.1, hp.2])
  convert h using 1 <;> congr 1 <;> ring

/-- Integrating the pointwise contraction proves the second-moment part of (28). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth,hp,hsecond), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_integral_sq_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ne : Ω → Fin 4 → ℕ)
    (ε : ℝ) (K d : ℕ) (m : ℝ) (c r : Fin 4 → ℝ) (p : ℝ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
    (hp : |p - armwiseExtensionFormula ε c| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
    (hsecond : Integrable (fun ω =>
      (factorialCellValue ε K m c r (Ne ω) - p) ^ 2) μ) :
    (∫ ω, (clippedCellValueFormula ε K d m c r (Ne ω) - p) ^ 2 ∂μ) ≤
      ∫ ω, (factorialCellValue ε K m c r (Ne ω) - p) ^ 2 ∂μ := by
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    hsecond
  exact Filter.Eventually.of_forall fun ω =>
    clippedCellValue_sq_error_le ε K d m c r (Ne ω) p hwidth hp

/-- An unbiased factorial lift transfers its center second moment to clipping bias. This is the first part of (28) before substituting the factorial moment bound (27). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth,hZ,hmean,hsecond), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_integral_bias_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Ne : Ω → Fin 4 → ℕ)
    (ε : ℝ) (K d : ℕ) (m : ℝ) (c r : Fin 4 → ℝ) (p : ℝ)
    (hwidth : 0 < (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
    (hZ : Integrable (fun ω => factorialCellValue ε K m c r (Ne ω)) μ)
    (hmean : (∫ ω, factorialCellValue ε K m c r (Ne ω) ∂μ) = p)
    (hsecond : Integrable (fun ω =>
      (factorialCellValue ε K m c r (Ne ω) - armwiseExtensionFormula ε c) ^ 2) μ) :
    |(∫ ω, clippedCellValueFormula ε K d m c r (Ne ω) ∂μ) - p| ≤
      (∫ ω, (factorialCellValue ε K m c r (Ne ω) - armwiseExtensionFormula ε c) ^ 2 ∂μ) /
        ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) := by
  simpa only [clippedCellValueFormula, hmean] using centeredClip_integral_bias_le μ
    (fun ω => factorialCellValue ε K m c r (Ne ω)) (armwiseExtensionFormula ε c)
    ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) hwidth hZ hsecond

/-- Zero oscillation scale makes clipping exactly equal to its center. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hscale), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_eq_center_of_zero_scale (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) (hscale : clippingScaleFormula ε c r = 0) :
    clippedCellValueFormula ε K d m c r Ne = armwiseExtensionFormula ε c := by
  simp only [clippedCellValueFormula, hscale, mul_zero, sub_zero, add_zero]
  exact max_eq_left (min_le_left _ _)

/-- The clipped cell statistic stays within its chosen width of the center, regardless of the evaluation counts or pilot localization. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_abs_sub_center_le (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    |clippedCellValueFormula ε K d m c r Ne - armwiseExtensionFormula ε c| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r := by
  apply abs_le.mpr
  constructor
  · have h := le_max_left
      (armwiseExtensionFormula ε c - (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
      (min (armwiseExtensionFormula ε c + (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r)
        (factorialCellValue ε K m c r Ne))
    change armwiseExtensionFormula ε c - _ ≤ clippedCellValueFormula ε K d m c r Ne at h
    linarith
  · have h : clippedCellValueFormula ε K d m c r Ne ≤
        armwiseExtensionFormula ε c + (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r := by
      exact max_le (by linarith) (min_le_left _ _)
    linarith

/-- On bad pilots the cell error is bounded by width plus center error. This is the pathwise inequality following roadmap (28), retaining the local scales rather than substituting unit loss. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_abs_error_le (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) (p : ℝ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    |clippedCellValueFormula ε K d m c r Ne - p| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r + |armwiseExtensionFormula ε c - p| := by
  calc
    _ ≤ |clippedCellValueFormula ε K d m c r Ne - armwiseExtensionFormula ε c| +
        |armwiseExtensionFormula ε c - p| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add
      (clippedCellValue_abs_sub_center_le ε K d m c r Ne hwidth) le_rfl

/-- The bad-pilot squared error is controlled by twice the width square and twice the center-error square, precisely the two quantities in roadmap (22). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_sq_error_le_width_center (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) (p : ℝ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    (clippedCellValueFormula ε K d m c r Ne - p) ^ 2 ≤
      2 * ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) ^ 2 +
        2 * (armwiseExtensionFormula ε c - p) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (clippedCellValue_abs_error_le ε K d m c r Ne p hwidth) 2
  rw [sq_abs] at h
  have ht :
      ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r + |armwiseExtensionFormula ε c - p|) ^ 2 ≤
      2 * ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) ^ 2 +
        2 * (armwiseExtensionFormula ε c - p) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r -
      |armwiseExtensionFormula ε c - p|), sq_abs (armwiseExtensionFormula ε c - p)]
  exact h.trans ht

/-- On any pilot event, the integrated absolute cell error is controlled by the local width and center deviation. This is the first-moment use of roadmap (22) and does not require an integrability premise on the cell statistic. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth,hA,hF,hB), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_integral_abs_on_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Ω) (c r : Ω → Fin 4 → ℝ) (Ne : Ω → Fin 4 → ℕ)
    (ε : ℝ) (K d : ℕ) (m p : ℝ)
    (hwidth : ∀ ω ∈ B, 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω))
    (hA : Integrable (fun ω =>
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω)) (μ.restrict B))
    (hF : Integrable (fun ω => |armwiseExtensionFormula ε (c ω) - p|) (μ.restrict B))
    (hB : MeasurableSet B) :
    (∫ ω in B, |clippedCellValueFormula ε K d m (c ω) (r ω) (Ne ω) - p| ∂μ) ≤
      (∫ ω in B, (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω) ∂μ) +
        (∫ ω in B, |armwiseExtensionFormula ε (c ω) - p| ∂μ) := by
  calc
    _ ≤ ∫ ω in B,
        (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω) +
          |armwiseExtensionFormula ε (c ω) - p| ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hA.add hF)
      exact (ae_restrict_iff' hB).mpr (ae_of_all _ fun ω hω =>
        clippedCellValue_abs_error_le ε K d m (c ω) (r ω) (Ne ω) p (hwidth ω hω))
    _ = _ := integral_add hA hF

/-- Integrating over any pilot event transfers the tail width and center second moments to the actual clipped cell loss. Applying this to the bad-pilot event is the second-moment use of roadmap (22) after (28). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth,hA,hF,hB), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_integral_sq_on_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Ω) (c r : Ω → Fin 4 → ℝ) (Ne : Ω → Fin 4 → ℕ)
    (ε : ℝ) (K d : ℕ) (m p : ℝ)
    (hwidth : ∀ ω ∈ B, 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω))
    (hA : Integrable (fun ω =>
      ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω)) ^ 2) (μ.restrict B))
    (hF : Integrable (fun ω => (armwiseExtensionFormula ε (c ω) - p) ^ 2) (μ.restrict B))
    (hB : MeasurableSet B) :
    (∫ ω in B, (clippedCellValueFormula ε K d m (c ω) (r ω) (Ne ω) - p) ^ 2 ∂μ) ≤
      2 * (∫ ω in B, ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω)) ^ 2 ∂μ) +
        2 * (∫ ω in B, (armwiseExtensionFormula ε (c ω) - p) ^ 2 ∂μ) := by
  calc
    _ ≤ ∫ ω in B,
        2 * ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (c ω) (r ω)) ^ 2 +
          2 * (armwiseExtensionFormula ε (c ω) - p) ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
        ((hA.const_mul 2).add (hF.const_mul 2))
      exact (ae_restrict_iff' hB).mpr (ae_of_all _ fun ω hω =>
        clippedCellValue_sq_error_le_width_center ε K d m (c ω) (r ω) (Ne ω) p (hwidth ω hω))
    _ = _ := by
      rw [integral_add (hA.const_mul 2) (hF.const_mul 2)]
      simp only [integral_const_mul]

end CausalSmith.Stat.OptvalueVanishingoverlapRate

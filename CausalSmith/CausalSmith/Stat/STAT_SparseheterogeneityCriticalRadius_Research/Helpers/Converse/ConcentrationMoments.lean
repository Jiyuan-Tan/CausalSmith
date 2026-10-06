module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.GammaCalibration
public import Causalean.Stat.Concentration.TailBounds.Bernstein

/-! One-cell envelopes and variance proxies for the normalization concentration step. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private lemma tiltedSide_integrable_any_concentration (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : ℝ → ℝ) : Integrable f (tiltedSide a J D h) := by
  rw [tiltedSide, integrable_add_measure]
  constructor
  · rw [integrable_finsetSum_measure]
    intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma oneCellPrior_integrable_of_stronglyMeasurable_concentration
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : LatentCell → ℝ) (hf : StronglyMeasurable f) :
    Integrable f (oneCellPrior a J D h) := by
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_any_concentration a J D t
      (f ∘ latentFromIntensity s a)
  rw [oneCellPrior]
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply Integrable.smul_measure
    · apply Integrable.add_measure
      · exact (hmap false (!h)).smul_measure (by norm_num)
      · exact (hmap true h).smul_measure (by norm_num)
    · exact ENNReal.ofReal_ne_top

private lemma oneCellPrior_integral_eq_concentration
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hJ : 1 ≤ J) (f : LatentCell → ℝ)
    (hf : StronglyMeasurable f) :
    ∫ z, f z ∂oneCellPrior a J D h =
      1 / (J : ℝ) * f referenceLatent + (1 - 1 / (J : ℝ)) *
        ((1 / 2 : ℝ) * ∫ x, f (latentFromIntensity false a x)
            ∂tiltedSide a J D (!h) +
          (1 / 2 : ℝ) * ∫ x, f (latentFromIntensity true a x)
            ∂tiltedSide a J D h) := by
  have hJpos : (0 : ℝ) < J := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hscale : 0 ≤ 1 - 1 / (J : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    exact_mod_cast hJ
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_any_concentration a J D t
      (f ∘ latentFromIntensity s a)
  have hhalfFalse : Integrable f
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h))) :=
    (hmap false (!h)).smul_measure (by norm_num)
  have hhalfTrue : Integrable f
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
    (hmap true h).smul_measure (by norm_num)
  rw [oneCellPrior, integral_add_measure]
  · rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (J : ℝ)),
      integral_smul_measure, ENNReal.toReal_ofReal hscale,
      integral_add_measure hhalfFalse hhalfTrue,
      integral_smul_measure, integral_smul_measure,
      integral_map (latentFromIntensity_measurable false a).aemeasurable
        hf.aestronglyMeasurable,
      integral_map (latentFromIntensity_measurable true a).aemeasurable
        hf.aestronglyMeasurable]
    norm_num [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply Integrable.smul_measure
    · exact hhalfFalse.add_measure hhalfTrue
    · exact ENNReal.ofReal_ne_top

lemma oneCellPrior_ae_latentIntensity_mem_Icc
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∀ᵐ z ∂oneCellPrior a J D h, latentIntensity z ∈ Icc (0 : ℝ) 4 := by
  have hgood : MeasurableSet {z : LatentCell |
      latentIntensity z ∈ Icc (0 : ℝ) 4} := by
    exact measurableSet_Icc.preimage latentIntensity_stronglyMeasurable.measurable
  rw [oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff hgood]
    norm_num [referenceLatent, latentIntensity]
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D (!h)] with x hx
      rcases hx with rfl | hx
      · simp [latentFromIntensity, zeroLatent, latentIntensity]
      · simp only [latentFromIntensity, ne_of_gt (ha.trans_le hx.1), ↓reduceIte,
          latentIntensity, Set.mem_Icc]
        exact ⟨ha.le.trans hx.1, hx.2.trans (by norm_num)⟩
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D h] with x hx
      rcases hx with rfl | hx
      · simp [latentFromIntensity, zeroLatent, latentIntensity]
      · simp only [latentFromIntensity, ne_of_gt (ha.trans_le hx.1), ↓reduceIte,
          latentIntensity, Set.mem_Icc]
        exact ⟨ha.le.trans hx.1, hx.2.trans (by norm_num)⟩

lemma oneCellPrior_ae_abs_latentSignedScore_le
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∀ᵐ z ∂oneCellPrior a J D h, |latentSignedScore z| ≤ 1 := by
  have hgood : MeasurableSet {z : LatentCell | |latentSignedScore z| ≤ 1} := by
    exact measurableSet_le latentSignedScore_stronglyMeasurable.measurable.abs
      measurable_const
  have hside (s t : Bool) :
      ∀ᵐ x ∂tiltedSide a J D t,
        |latentSignedScore (latentFromIntensity s a x)| ≤ 1 := by
    filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D t] with x hx
    rcases hx with rfl | hx
    · simp [latentSignedScore, latentFromIntensity, zeroLatent, latentIntensity,
        latentSignValue, latentSign, latentScore]
    · have hxpos : 0 < x := ha.trans_le hx.1
      have hratio : 0 ≤ x / (x + a) ∧ x / (x + a) ≤ 1 := by
        constructor
        · positivity
        · rw [div_le_one (by positivity : 0 < x + a)]
          linarith
      cases s <;>
          simp only [latentSignedScore, latentFromIntensity, hxpos.ne', ↓reduceIte,
          latentIntensity, latentSignValue, latentSign, latentScore,
          Bool.false_eq_true, abs_neg, abs_mul, abs_one,
          abs_of_nonneg hxpos.le,
          abs_of_nonneg hratio.1] <;>
        nlinarith [hx.2]
  rw [oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff hgood]
    simp [latentSignedScore, referenceLatent, latentIntensity, latentSignValue,
      latentSign, latentScore]
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hgood]
      exact hside false (!h)
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hgood]
      exact hside true h

lemma oneCellPrior_integral_latentIntensity_sq_le
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∫ z, latentIntensity z ^ 2 ∂oneCellPrior a J D h ≤
      16 / (J : ℝ) + a := by
  let f : LatentCell → ℝ := fun z => latentIntensity z ^ 2
  have hf : StronglyMeasurable f :=
    latentIntensity_stronglyMeasurable.pow 2
  have hside (s t : Bool) :
      ∫ x, f (latentFromIntensity s a x) ∂tiltedSide a J D t ≤ a := by
    have hsq : Integrable (fun x => f (latentFromIntensity s a x))
        (tiltedSide a J D t) :=
      tiltedSide_integrable_any_concentration a J D t _
    have hid : Integrable (fun x : ℝ => x) (tiltedSide a J D t) :=
      tiltedSide_integrable_any_concentration a J D t _
    calc
      ∫ x, f (latentFromIntensity s a x) ∂tiltedSide a J D t ≤
          ∫ x, x ∂tiltedSide a J D t := by
        apply integral_mono_ae hsq hid
        filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D t] with x hx
        rcases hx with rfl | hx
        · simp [f, latentFromIntensity, zeroLatent, latentIntensity]
        · have hxpos : 0 < x := ha.trans_le hx.1
          simp only [f, latentFromIntensity, hxpos.ne', ↓reduceIte, latentIntensity]
          nlinarith [hx.1, hx.2]
      _ = a := tiltedSide_integral_id a J D t ha
  rw [oneCellPrior_integral_eq_concentration a J D h hJ f hf]
  have hJpos : (0 : ℝ) < J := by positivity
  have hscale0 : 0 ≤ 1 - 1 / (J : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    exact_mod_cast hJ
  have hscale1 : 1 - 1 / (J : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (J : ℝ) := by positivity
    linarith
  have href : f referenceLatent = 16 := by
    norm_num [f, referenceLatent, latentIntensity]
  rw [href]
  have hfalse := hside false (!h)
  have htrue := hside true h
  have havg :
      (1 / 2 : ℝ) * (∫ x, f (latentFromIntensity false a x)
          ∂tiltedSide a J D (!h)) +
        (1 / 2 : ℝ) * (∫ x, f (latentFromIntensity true a x)
          ∂tiltedSide a J D h) ≤ a := by
    linarith
  calc
    1 / (J : ℝ) * 16 + (1 - 1 / (J : ℝ)) *
          ((1 / 2 : ℝ) * ∫ x, f (latentFromIntensity false a x)
              ∂tiltedSide a J D (!h) +
            (1 / 2 : ℝ) * ∫ x, f (latentFromIntensity true a x)
              ∂tiltedSide a J D h)
        ≤ 1 / (J : ℝ) * 16 + (1 - 1 / (J : ℝ)) * a := by
          gcongr
    _ ≤ 1 / (J : ℝ) * 16 + a := by
      have hmul : (1 - 1 / (J : ℝ)) * a ≤ a :=
        mul_le_of_le_one_left ha.le hscale1
      simpa [add_comm] using add_le_add_left hmul (1 / (J : ℝ) * 16)
    _ = 16 / (J : ℝ) + a := by ring

lemma oneCellPrior_integral_latentSignedScore_sq_le
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∫ z, latentSignedScore z ^ 2 ∂oneCellPrior a J D h ≤ a := by
  let f : LatentCell → ℝ := fun z => latentSignedScore z ^ 2
  have hf : StronglyMeasurable f :=
    latentSignedScore_stronglyMeasurable.pow 2
  have hside (s t : Bool) :
      ∫ x, f (latentFromIntensity s a x) ∂tiltedSide a J D t ≤ a := by
    have hsq : Integrable (fun x => f (latentFromIntensity s a x))
        (tiltedSide a J D t) :=
      tiltedSide_integrable_any_concentration a J D t _
    have hid : Integrable (fun x : ℝ => x) (tiltedSide a J D t) :=
      tiltedSide_integrable_any_concentration a J D t _
    calc
      ∫ x, f (latentFromIntensity s a x) ∂tiltedSide a J D t ≤
          ∫ x, x ∂tiltedSide a J D t := by
        apply integral_mono_ae hsq hid
        filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D t] with x hx
        rcases hx with rfl | hx
        · simp [f, latentSignedScore, latentFromIntensity, zeroLatent,
            latentIntensity, latentSignValue, latentSign, latentScore]
        · have hxpos : 0 < x := ha.trans_le hx.1
          have hr0 : 0 ≤ x / (x + a) := by positivity
          have hr1 : x / (x + a) ≤ 1 := by
            rw [div_le_one (by positivity : 0 < x + a)]
            linarith
          have hprod0 : 0 ≤ x * (x / (x + a)) :=
            mul_nonneg hxpos.le hr0
          have hprod_le : x * (x / (x + a)) ≤ x :=
            mul_le_of_le_one_right hxpos.le hr1
          have hsq_le : (x * (x / (x + a))) ^ 2 ≤ x := by
            nlinarith [hx.2]
          cases s <;>
            simp only [f, latentSignedScore, latentFromIntensity, hxpos.ne',
              ↓reduceIte, latentIntensity, latentSignValue, latentSign,
              latentScore, Bool.false_eq_true] <;>
            nlinarith
      _ = a := tiltedSide_integral_id a J D t ha
  rw [oneCellPrior_integral_eq_concentration a J D h hJ f hf]
  have hJpos : (0 : ℝ) < J := by positivity
  have hscale0 : 0 ≤ 1 - 1 / (J : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    exact_mod_cast hJ
  have hscale1 : 1 - 1 / (J : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (J : ℝ) := by positivity
    linarith
  have href : f referenceLatent = 0 := by
    simp [f, latentSignedScore, referenceLatent, latentIntensity,
      latentSignValue, latentSign, latentScore]
  rw [href]
  have hfalse := hside false (!h)
  have htrue := hside true h
  have havg :
      (1 / 2 : ℝ) * (∫ x, f (latentFromIntensity false a x)
          ∂tiltedSide a J D (!h)) +
        (1 / 2 : ℝ) * (∫ x, f (latentFromIntensity true a x)
          ∂tiltedSide a J D h) ≤ a := by
    linarith
  have hmul : (1 - 1 / (J : ℝ)) *
      ((1 / 2 : ℝ) * (∫ x, f (latentFromIntensity false a x)
          ∂tiltedSide a J D (!h)) +
        (1 / 2 : ℝ) * (∫ x, f (latentFromIntensity true a x)
          ∂tiltedSide a J D h)) ≤ a := by
    calc
      _ ≤ (1 - 1 / (J : ℝ)) * a := by gcongr
      _ ≤ a := mul_le_of_le_one_left ha.le hscale1
  simpa using hmul

lemma oneCellPrior_integral_centered_latentIntensity_sq_le
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∫ z, (latentIntensity z -
      ∫ y, latentIntensity y ∂oneCellPrior a J D h) ^ 2
        ∂oneCellPrior a J D h ≤ 16 / (J : ℝ) + a := by
  let _ := oneCellPrior_isProbabilityMeasure a J D h ha hJ
  have hsq : Integrable (fun z => latentIntensity z ^ 2)
      (oneCellPrior a J D h) :=
    oneCellPrior_integrable_of_stronglyMeasurable_concentration a J D h _
      (latentIntensity_stronglyMeasurable.pow 2)
  have hmem : MemLp latentIntensity 2 (oneCellPrior a J D h) :=
    (memLp_two_iff_integrable_sq
      latentIntensity_stronglyMeasurable.aestronglyMeasurable).2 hsq
  calc
    ∫ z, (latentIntensity z -
        ∫ y, latentIntensity y ∂oneCellPrior a J D h) ^ 2
          ∂oneCellPrior a J D h =
        ProbabilityTheory.variance latentIntensity (oneCellPrior a J D h) :=
      (ProbabilityTheory.variance_eq_integral
        latentIntensity_stronglyMeasurable.measurable.aemeasurable).symm
    _ = (∫ z, latentIntensity z ^ 2 ∂oneCellPrior a J D h) -
        (∫ z, latentIntensity z ∂oneCellPrior a J D h) ^ 2 := by
      simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hmem
    _ ≤ ∫ z, latentIntensity z ^ 2 ∂oneCellPrior a J D h := by
      nlinarith [sq_nonneg
        (∫ z, latentIntensity z ∂oneCellPrior a J D h)]
    _ ≤ 16 / (J : ℝ) + a :=
      oneCellPrior_integral_latentIntensity_sq_le a J D h ha ha1 hJ

lemma oneCellPrior_integral_centered_latentSignedScore_sq_le
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (ha1 : a ≤ 1) (hJ : 1 ≤ J) :
    ∫ z, (latentSignedScore z -
      ∫ y, latentSignedScore y ∂oneCellPrior a J D h) ^ 2
        ∂oneCellPrior a J D h ≤ a := by
  let _ := oneCellPrior_isProbabilityMeasure a J D h ha hJ
  have hsq : Integrable (fun z => latentSignedScore z ^ 2)
      (oneCellPrior a J D h) :=
    oneCellPrior_integrable_of_stronglyMeasurable_concentration a J D h _
      (latentSignedScore_stronglyMeasurable.pow 2)
  have hmem : MemLp latentSignedScore 2 (oneCellPrior a J D h) :=
    (memLp_two_iff_integrable_sq
      latentSignedScore_stronglyMeasurable.aestronglyMeasurable).2 hsq
  calc
    ∫ z, (latentSignedScore z -
        ∫ y, latentSignedScore y ∂oneCellPrior a J D h) ^ 2
          ∂oneCellPrior a J D h =
        ProbabilityTheory.variance latentSignedScore (oneCellPrior a J D h) :=
      (ProbabilityTheory.variance_eq_integral
        latentSignedScore_stronglyMeasurable.measurable.aemeasurable).symm
    _ = (∫ z, latentSignedScore z ^ 2 ∂oneCellPrior a J D h) -
        (∫ z, latentSignedScore z ∂oneCellPrior a J D h) ^ 2 := by
      simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hmem
    _ ≤ ∫ z, latentSignedScore z ^ 2 ∂oneCellPrior a J D h := by
      nlinarith [sq_nonneg
        (∫ z, latentSignedScore z ∂oneCellPrior a J D h)]
    _ ≤ a :=
      oneCellPrior_integral_latentSignedScore_sq_le a J D h ha ha1 hJ

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

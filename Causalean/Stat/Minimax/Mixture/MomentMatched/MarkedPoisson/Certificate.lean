module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Finite signed moment certificates

This module realizes a normalized finite signed moment functional as an atomic
signed measure.  It exposes its total variation, a measurable polar sign, and
the normalized positive and negative Jordan priors, including an orientation
that makes any chosen target separation nonnegative.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- A normalized finite signed moment certificate on [a finite node index set](hyp:ι) through
[a matching degree](hyp:L) consists of distinct real nodes, signed weights of total absolute
mass one, and vanishing algebraic moments through that degree. -/
structure NormalizedFiniteSignedMomentCertificate
    (ι : Type*) [Fintype ι] (L : ℕ) where
  node : ι → ℝ
  weight : ι → ℝ
  node_injective : Function.Injective node
  normalized : ∑ i, |weight i| = 1
  moments_zero : ∀ j, j ≤ L → ∑ i, weight i * node i ^ j = 0

namespace NormalizedFiniteSignedMomentCertificate

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- A [finite signed certificate](hyp:C) induces the [atomic signed measure](goal) that [places
each signed weight at its certificate node](step:1). -/
noncomputable def signedMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) : SignedMeasure ℝ :=
  ∑ i, MeasureTheory.VectorMeasure.dirac (C.node i) (C.weight i)

/-- A [finite signed certificate](hyp:C) induces the [atomic absolute-weight measure](goal) that
[places the absolute value of each weight at its certificate node](step:1). -/
noncomputable def absoluteMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) : Measure ℝ :=
  ∑ i, ENNReal.ofReal |C.weight i| • Measure.dirac (C.node i)

private noncomputable def atomicPolarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) (x : ℝ) : ℝ :=
  ∑ i, if x = C.node i then Real.sign (C.weight i) else 0

private theorem atomicPolarSign_node
    (C : NormalizedFiniteSignedMomentCertificate ι L) (i : ι) :
    atomicPolarSign C (C.node i) = Real.sign (C.weight i) := by
  classical
  unfold atomicPolarSign
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    have hne : C.node i ≠ C.node k := C.node_injective.ne hki.symm
    simp [hne]
  · simp

private theorem measurable_atomicPolarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    Measurable (atomicPolarSign C) := by
  classical
  unfold atomicPolarSign
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.piecewise (measurableSet_singleton (C.node i)) measurable_const

private theorem abs_mul_sign (x : ℝ) : |x| * Real.sign x = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    ring
  · simp
  · rw [abs_of_pos hx, Real.sign_of_pos hx, mul_one]

omit [Fintype ι] in
private theorem finsetSum_signedMeasure_apply (t : Finset ι)
    (μ : ι → SignedMeasure ℝ) (s : Set ℝ) :
    (∑ i ∈ t, μ i) s = ∑ i ∈ t, μ i s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih => simp [Finset.sum_insert, hit, ih]

private theorem integrable_atomicPolarSign_absoluteMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    Integrable (atomicPolarSign C) C.absoluteMeasure := by
  classical
  rw [absoluteMeasure]
  apply integrable_finsetSum_measure.2
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure (by simp)

private theorem signedMeasure_eq_absoluteMeasure_withDensity
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure = C.absoluteMeasure.withDensityᵥ (atomicPolarSign C) := by
  classical
  ext s hs
  rw [withDensityᵥ_apply (integrable_atomicPolarSign_absoluteMeasure C) hs]
  rw [← integral_indicator hs]
  simp only [signedMeasure, absoluteMeasure]
  rw [MeasureTheory.integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp)).smul_measure (by simp))]
  rw [finsetSum_signedMeasure_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmem : C.node i ∈ s
  · simp [VectorMeasure.dirac_apply_of_mem hs hmem, hmem, atomicPolarSign_node,
      abs_mul_sign]
  · simp [VectorMeasure.dirac_apply_of_notMem hmem, hmem]

private theorem abs_atomicPolarSign_ae_absoluteMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    ∀ᵐ x ∂C.absoluteMeasure, |atomicPolarSign C x| = 1 := by
  classical
  rw [absoluteMeasure, ae_finsetSum_measure_iff]
  intro i hi
  by_cases hw : C.weight i = 0
  · simp [hw]
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff]
    · rw [atomicPolarSign_node]
      rcases Real.sign_apply_eq_of_ne_zero (C.weight i) hw with h | h <;> simp [h]
    · exact measurableSet_eq_fun
        (continuous_abs.measurable.comp (measurable_atomicPolarSign C)) measurable_const

/-- The variation of the signed measure represented by [a finite signed certificate](hyp:C)
[equals its atomic absolute-weight measure](goal). -/
theorem variation_eq_absoluteMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure.variation = C.absoluteMeasure := by
  rw [signedMeasure_eq_absoluteMeasure_withDensity,
    Measure.variation_withDensityᵥ (integrable_atomicPolarSign_absoluteMeasure C)]
  calc
    C.absoluteMeasure.withDensity (fun x => ‖atomicPolarSign C x‖ₑ) =
        C.absoluteMeasure.withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [abs_atomicPolarSign_ae_absoluteMeasure C] with x hx
      rw [← ofReal_norm, Real.norm_eq_abs, hx]
      simp
    _ = C.absoluteMeasure := withDensity_one

/-- The signed measure represented by [a finite signed certificate](hyp:C) [has total mass
zero](goal), as required by its degree-zero moment constraint. -/
theorem signedMeasure_univ_eq_zero
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure Set.univ = 0 := by
  rw [signedMeasure]
  rw [finsetSum_signedMeasure_apply]
  simpa using C.moments_zero 0 (Nat.zero_le L)

/-- Integrating the [requested power](hyp:j) against the atomic signed measure of [a finite
signed certificate](hyp:C) [gives zero](goal) whenever [that degree is within the certificate's
matching range](hyp:hj). -/
theorem integral_pow_signedMeasure_eq_zero
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (j : ℕ) (hj : j ≤ L) :
    ∫ᵛ x, x ^ j ∂<•C.signedMeasure = 0 := by
  rw [signedMeasure]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure (fun i _ => by
    change Integrable (fun x : ℝ => x ^ j)
      (VectorMeasure.dirac (C.node i) (C.weight i)).variation
    rw [VectorMeasure.variation_dirac]
    exact (integrable_dirac (by simp)).smul_measure (by simp))]
  simpa using C.moments_zero j hj

/-- The variation measure of [a normalized finite signed certificate](hyp:C) [is a probability
measure](goal), because [its total absolute weight is one](step:1). -/
noncomputable instance variation_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    IsProbabilityMeasure C.signedMeasure.variation := by
  constructor
  rw [variation_eq_absoluteMeasure, absoluteMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _), C.normalized]
  simp

/-- The [atomic polar sign](goal) of [a finite signed certificate](hyp:C) at [an evaluation
point](hyp:x) [equals the sign of the unique weight at a certificate node and is zero away from
all nodes](step:1). -/
noncomputable def polarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) (x : ℝ) : ℝ :=
  ∑ i, if x = C.node i then Real.sign (C.weight i) else 0

/-- The atomic polar sign of [a finite signed certificate](hyp:C) [is Borel measurable](goal). -/
theorem measurable_polarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    Measurable C.polarSign := by
  exact measurable_atomicPolarSign C

/-- The atomic polar sign of [a finite signed certificate](hyp:C) [has absolute value one almost
everywhere under its variation measure](goal). -/
theorem abs_polarSign_ae
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    ∀ᵐ x ∂C.signedMeasure.variation, |C.polarSign x| = 1 := by
  rw [variation_eq_absoluteMeasure]
  exact abs_atomicPolarSign_ae_absoluteMeasure C

/-- The atomic polar sign of [a finite signed certificate](hyp:C) [is integrable against its
variation measure](goal). -/
theorem integrable_polarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    Integrable C.polarSign C.signedMeasure.variation := by
  rw [variation_eq_absoluteMeasure]
  exact integrable_atomicPolarSign_absoluteMeasure C

/-- The atomic signed measure of [a finite signed certificate](hyp:C) [equals its variation
measure weighted by its measurable polar sign](goal). -/
theorem signedMeasure_eq_withDensity_polarSign
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure = C.signedMeasure.variation.withDensityᵥ C.polarSign := by
  rw [variation_eq_absoluteMeasure]
  exact signedMeasure_eq_absoluteMeasure_withDensity C

/-- The [normalized positive Jordan prior](goal) of [a finite signed certificate](hyp:C) is
[obtained by doubling the positive atomic weights](step:1). -/
noncomputable def positivePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (2 * max (C.weight i) 0) • Measure.dirac (C.node i)

/-- The [normalized negative Jordan prior](goal) of [a finite signed certificate](hyp:C) is
[obtained by doubling the magnitudes of the negative atomic weights](step:1). -/
noncomputable def negativePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (2 * max (-C.weight i) 0) • Measure.dirac (C.node i)

private theorem sum_weight_eq_zero
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    ∑ i, C.weight i = 0 := by
  simpa using C.moments_zero 0 (Nat.zero_le L)

private theorem sum_max_weight_eq_half
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    ∑ i, max (C.weight i) 0 = (2 : ℝ)⁻¹ := by
  have habs (x : ℝ) : |x| = 2 * max x 0 - x := by
    rcases le_total x 0 with hx | hx
    · simp [max_eq_right hx, abs_of_nonpos hx]
    · simp [max_eq_left hx, abs_of_nonneg hx]
      ring
  have hsum : ∑ i, |C.weight i| = 2 * ∑ i, max (C.weight i) 0 - ∑ i, C.weight i := by
    calc
      ∑ i, |C.weight i| = ∑ i, (2 * max (C.weight i) 0 - C.weight i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact habs (C.weight i)
      _ = 2 * ∑ i, max (C.weight i) 0 - ∑ i, C.weight i := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [C.normalized, sum_weight_eq_zero C, sub_zero] at hsum
  linarith

private theorem sum_max_neg_weight_eq_half
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    ∑ i, max (-C.weight i) 0 = (2 : ℝ)⁻¹ := by
  have habs (x : ℝ) : |x| = 2 * max (-x) 0 + x := by
    rcases le_total x 0 with hx | hx
    · simp [max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]
      ring
    · simp [max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  have hsum : ∑ i, |C.weight i| = 2 * ∑ i, max (-C.weight i) 0 + ∑ i, C.weight i := by
    calc
      ∑ i, |C.weight i| = ∑ i, (2 * max (-C.weight i) 0 + C.weight i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact habs (C.weight i)
      _ = 2 * ∑ i, max (-C.weight i) 0 + ∑ i, C.weight i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [C.normalized, sum_weight_eq_zero C, add_zero] at hsum
  linarith

private theorem integral_positivePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    ∫ x, f x ∂C.positivePrior = ∑ i, (2 * max (C.weight i) 0) * f (C.node i) := by
  classical
  rw [positivePrior]
  rw [integral_finsetSum_measure (fun i _ => by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (le_max_right _ _))]
  rfl

private theorem integral_negativePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    ∫ x, f x ∂C.negativePrior = ∑ i, (2 * max (-C.weight i) 0) * f (C.node i) := by
  classical
  rw [negativePrior]
  rw [integral_finsetSum_measure (fun i _ => by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (le_max_right _ _))]
  rfl

private theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with hx | hx
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

private theorem prior_integral_sub
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    ∫ x, f x ∂C.positivePrior - ∫ x, f x ∂C.negativePrior =
      2 * ∑ i, C.weight i * f (C.node i) := by
  rw [integral_positivePrior, integral_negativePrior, ← Finset.sum_sub_distrib]
  calc
    ∑ i, (2 * max (C.weight i) 0 * f (C.node i) -
        2 * max (-C.weight i) 0 * f (C.node i)) =
        ∑ i, 2 * (C.weight i * f (C.node i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← sub_mul, ← mul_sub, max_sub_max_neg]
      ring
    _ = 2 * ∑ i, C.weight i * f (C.node i) := by rw [Finset.mul_sum]

omit [Fintype ι] in
private theorem withDensity_finsetSum (t : Finset ι) (μ : ι → Measure ℝ)
    (f : ℝ → ℝ≥0∞) :
    (∑ i ∈ t, μ i).withDensity f = ∑ i ∈ t, (μ i).withDensity f := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih => simp [Finset.sum_insert, hit, ih, withDensity_add_measure]

private theorem ofReal_abs_mul_ofReal_sign (x : ℝ) :
    ENNReal.ofReal |x| * ENNReal.ofReal (Real.sign x) = ENNReal.ofReal (max x 0) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [abs_of_neg hx, Real.sign_of_neg hx, max_eq_right hx.le]
  · simp
  · simp [abs_of_pos hx, Real.sign_of_pos hx, max_eq_left hx.le]

private theorem ofReal_abs_mul_ofReal_neg_sign (x : ℝ) :
    ENNReal.ofReal |x| * ENNReal.ofReal (-Real.sign x) = ENNReal.ofReal (max (-x) 0) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [abs_of_neg hx, Real.sign_of_neg hx, max_eq_left (neg_nonneg.mpr hx.le)]
  · simp
  · simp [abs_of_pos hx, Real.sign_of_pos hx, max_eq_right (neg_nonpos.mpr hx.le)]

private theorem absoluteMeasure_withDensity_pos
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.absoluteMeasure.withDensity (fun x => ENNReal.ofReal (atomicPolarSign C x)) =
      ∑ i, ENNReal.ofReal (max (C.weight i) 0) • Measure.dirac (C.node i) := by
  classical
  rw [absoluteMeasure, withDensity_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [withDensity_smul_measure, dirac_withDensity, smul_smul, atomicPolarSign_node,
    ofReal_abs_mul_ofReal_sign]

private theorem absoluteMeasure_withDensity_neg
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.absoluteMeasure.withDensity (fun x => ENNReal.ofReal (-atomicPolarSign C x)) =
      ∑ i, ENNReal.ofReal (max (-C.weight i) 0) • Measure.dirac (C.node i) := by
  classical
  rw [absoluteMeasure, withDensity_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [withDensity_smul_measure, dirac_withDensity, smul_smul, atomicPolarSign_node,
    ofReal_abs_mul_ofReal_neg_sign]

private theorem half_positivePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    (2 : ℝ≥0∞)⁻¹ • C.positivePrior =
      ∑ i, ENNReal.ofReal (max (C.weight i) 0) • Measure.dirac (C.node i) := by
  classical
  rw [positivePrior, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [← mul_assoc, ENNReal.inv_mul_cancel] <;> norm_num

private theorem half_negativePrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    (2 : ℝ≥0∞)⁻¹ • C.negativePrior =
      ∑ i, ENNReal.ofReal (max (-C.weight i) 0) • Measure.dirac (C.node i) := by
  classical
  rw [negativePrior, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [← mul_assoc, ENNReal.inv_mul_cancel] <;> norm_num

/-- The positive Jordan prior of [a normalized finite signed certificate](hyp:C) [is a
probability measure](goal), because [its doubled positive weights have total mass one](step:1). -/
noncomputable instance positivePrior_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    IsProbabilityMeasure C.positivePrior := by
  constructor
  rw [positivePrior]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    mul_nonneg (by norm_num) (le_max_right _ _))]
  rw [← Finset.mul_sum, sum_max_weight_eq_half C]
  norm_num

/-- The negative Jordan prior of [a normalized finite signed certificate](hyp:C) [is a
probability measure](goal), because [its doubled negative weights have total mass one](step:1). -/
noncomputable instance negativePrior_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    IsProbabilityMeasure C.negativePrior := by
  constructor
  rw [negativePrior]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    mul_nonneg (by norm_num) (le_max_right _ _))]
  rw [← Finset.mul_sum, sum_max_neg_weight_eq_half C]
  norm_num

/-- The positive part of the Jordan decomposition of [a certificate's signed measure](hyp:C)
[is one half of its normalized positive Jordan prior](goal). -/
theorem jordanDecomposition_posPart_eq
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure.toJordanDecomposition.posPart =
      (2 : ℝ≥0∞)⁻¹ • C.positivePrior := by
  have hJ := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := C.signedMeasure) (t := 0) (μ := C.absoluteMeasure)
    (measurable_atomicPolarSign C) (integrable_atomicPolarSign_absoluteMeasure C)
    VectorMeasure.MutuallySingular.zero_left (by
      simpa using signedMeasure_eq_absoluteMeasure_withDensity C)
  have hpos := congrArg JordanDecomposition.posPart hJ
  calc
    C.signedMeasure.toJordanDecomposition.posPart =
        C.absoluteMeasure.withDensity (fun x => ENNReal.ofReal (atomicPolarSign C x)) := by
      simpa [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart] using hpos
    _ = ∑ i, ENNReal.ofReal (max (C.weight i) 0) • Measure.dirac (C.node i) :=
      absoluteMeasure_withDensity_pos C
    _ = (2 : ℝ≥0∞)⁻¹ • C.positivePrior := (half_positivePrior C).symm

/-- The negative part of the Jordan decomposition of [a certificate's signed measure](hyp:C)
[is one half of its normalized negative Jordan prior](goal). -/
theorem jordanDecomposition_negPart_eq
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.signedMeasure.toJordanDecomposition.negPart =
      (2 : ℝ≥0∞)⁻¹ • C.negativePrior := by
  have hJ := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := C.signedMeasure) (t := 0) (μ := C.absoluteMeasure)
    (measurable_atomicPolarSign C) (integrable_atomicPolarSign_absoluteMeasure C)
    VectorMeasure.MutuallySingular.zero_left (by
      simpa using signedMeasure_eq_absoluteMeasure_withDensity C)
  have hneg := congrArg JordanDecomposition.negPart hJ
  calc
    C.signedMeasure.toJordanDecomposition.negPart =
        C.absoluteMeasure.withDensity (fun x => ENNReal.ofReal (-atomicPolarSign C x)) := by
      simpa [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_negPart] using hneg
    _ = ∑ i, ENNReal.ofReal (max (-C.weight i) 0) • Measure.dirac (C.node i) :=
      absoluteMeasure_withDensity_neg C
    _ = (2 : ℝ≥0∞)⁻¹ • C.negativePrior := (half_negativePrior C).symm

/-- The normalized Jordan priors of [a finite signed certificate](hyp:C) [have equal moments at
the requested degree](goal) whenever [that degree](hyp:j) [does not exceed the matching
degree](hyp:hj). -/
theorem jordanPriors_moments_eq
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (j : ℕ) (hj : j ≤ L) :
    ∫ x, x ^ j ∂C.positivePrior = ∫ x, x ^ j ∂C.negativePrior := by
  have h := prior_integral_sub C (fun x => x ^ j)
  rw [C.moments_zero j hj, mul_zero] at h
  linarith

/-- The positive and negative Jordan priors of [a finite signed certificate](hyp:C) [are both
concentrated on its finite set of nodes](goal). -/
theorem jordanPriors_ae_mem_range
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    (∀ᵐ x ∂C.positivePrior, x ∈ Set.range C.node) ∧
      ∀ᵐ x ∂C.negativePrior, x ∈ Set.range C.node := by
  classical
  constructor
  · rw [positivePrior, ae_finsetSum_measure_iff]
    intro i hi
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff (Set.finite_range C.node).measurableSet).2 ⟨i, rfl⟩
  · rw [negativePrior, ae_finsetSum_measure_iff]
    intro i hi
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff (Set.finite_range C.node).measurableSet).2 ⟨i, rfl⟩

/-- The [target-oriented null prior](goal) for [a finite signed certificate](hyp:C) and [a target
function](hyp:f) [chooses the Jordan prior that makes the alternative target mean at least as
large as the null target mean](step:1). -/
noncomputable def orientedPrior0
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) : Measure ℝ :=
  if 0 ≤ ∑ i, C.weight i * f (C.node i) then C.negativePrior else C.positivePrior

/-- The [target-oriented alternative prior](goal) for [a finite signed certificate](hyp:C) and
[a target function](hyp:f) [chooses the opposite Jordan prior from the oriented null, swapping
the pair exactly when the certificate evaluates the target negatively](step:1). -/
noncomputable def orientedPrior1
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) : Measure ℝ :=
  if 0 ≤ ∑ i, C.weight i * f (C.node i) then C.positivePrior else C.negativePrior

/-- The target-oriented null prior built from [a finite signed certificate](hyp:C) and [a target
function](hyp:f) [is a probability measure](goal), because [it selects one of the two Jordan
probability measures](step:1). -/
noncomputable instance orientedPrior0_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    IsProbabilityMeasure (C.orientedPrior0 f) := by
  unfold orientedPrior0
  split <;> infer_instance

/-- The target-oriented alternative prior built from [a finite signed certificate](hyp:C) and
[a target function](hyp:f) [is a probability measure](goal), because [it selects one of the two
Jordan probability measures](step:1). -/
noncomputable instance orientedPrior1_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    IsProbabilityMeasure (C.orientedPrior1 f) := by
  unfold orientedPrior1
  split <;> infer_instance

/-- Orienting the Jordan priors of [a finite signed certificate](hyp:C) for [a target
function](hyp:f) [makes the alternative-minus-null expectation gap equal twice the absolute
signed certificate evaluation](goal). -/
theorem orientedPrior_target_separation
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    ∫ x, f x ∂C.orientedPrior1 f - ∫ x, f x ∂C.orientedPrior0 f =
      2 * |∑ i, C.weight i * f (C.node i)| := by
  by_cases h : 0 ≤ ∑ i, C.weight i * f (C.node i)
  · rw [orientedPrior1, if_pos h, orientedPrior0, if_pos h,
      prior_integral_sub, abs_of_nonneg h]
  · rw [orientedPrior1, if_neg h, orientedPrior0, if_neg h,
      abs_of_neg (lt_of_not_ge h)]
    have hsub := prior_integral_sub C f
    linarith

/-- The priors obtained by orienting [a finite signed certificate](hyp:C) for [a target
function](hyp:f) [retain equal moments at the requested degree](goal) whenever [that
degree](hyp:j) [does not exceed the matching degree](hyp:hj). -/
theorem orientedPriors_moments_eq
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ)
    (j : ℕ) (hj : j ≤ L) :
    ∫ x, x ^ j ∂C.orientedPrior0 f = ∫ x, x ^ j ∂C.orientedPrior1 f := by
  by_cases h : 0 ≤ ∑ i, C.weight i * f (C.node i)
  · rw [orientedPrior0, if_pos h, orientedPrior1, if_pos h]
    exact (jordanPriors_moments_eq C j hj).symm
  · rw [orientedPrior0, if_neg h, orientedPrior1, if_neg h]
    exact jordanPriors_moments_eq C j hj

/-- A [finite alternation moment dual](hyp:D) for [a target function](hyp:f) on an interval with
[lower endpoint](hyp:r) and [upper endpoint](hyp:s) supplies a [normalized finite signed moment
certificate](goal) by [using its nodes, weights, normalization, and moment identities](step:1). -/
noncomputable def ofFiniteMomentDual
    {f : ℝ → ℝ} {r s : ℝ}
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      f r s L) :
    NormalizedFiniteSignedMomentCertificate (Fin (L + 2)) L where
  node := D.nodes
  weight := D.weights
  node_injective := D.nodes_strictMono.injective
  normalized := D.weights_normalized
  moments_zero := D.moments_zero

end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

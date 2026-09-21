module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Certificate
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance

/-!
# Zero-inflated priors from finite signed certificates

The variation probability is tilted by `a / (p + a)` and the missing mass is
placed at zero.  This file records support, moment, and finite i.i.d.-product
identities used by rare-cell constructions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

variable {ι : Type*} [Fintype ι] {L : ℕ}

private theorem measurable_tilt (a : ℝ) :
    Measurable (fun p : ℝ => a / (p + a)) := by
  fun_prop

private theorem tilt_nonneg_ae
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∀ᵐ p ∂C.signedMeasure.variation, 0 ≤ a / (p + a) := by
  filter_upwards [hsupp] with p hp
  have hp0 : 0 < p := lt_of_lt_of_le (div_pos ha hκ) hp.1
  positivity

private theorem tilt_le_one_ae
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∀ᵐ p ∂C.signedMeasure.variation, a / (p + a) ≤ 1 := by
  filter_upwards [hsupp] with p hp
  have hp0 : 0 < p := lt_of_lt_of_le (div_pos ha hκ) hp.1
  exact (div_le_one (add_pos hp0 ha)).2 (le_add_of_nonneg_left hp0.le)

private theorem integrable_tilt
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    Integrable (fun p : ℝ => a / (p + a)) C.signedMeasure.variation := by
  apply Integrable.of_bound (measurable_tilt a).aestronglyMeasurable 1
  filter_upwards [tilt_nonneg_ae C a κ B ha hκ hsupp,
    tilt_le_one_ae C a κ B ha hκ hsupp] with p hp0 hp1
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  exact hp1

/-- The [zero-inflated prior measure](goal) [reweights a certificate's variation measure by the
nonnegative part of the shift-to-shifted-mass ratio and places at zero the nonnegative
part of one minus the integral of that ratio](step:1). It is defined
from [a finite signed certificate](hyp:C) and [a shift parameter](hyp:a).

The shift is an arbitrary real here; the results that need it positive, such as
`zeroInflatedPrior_isProbabilityMeasure`, take that as an explicit hypothesis. -/
noncomputable def zeroInflatedPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a : ℝ) : Measure ℝ :=
  C.signedMeasure.variation.withDensity
      (fun p => ENNReal.ofReal (a / (p + a))) +
    ENNReal.ofReal
      (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation) • Measure.dirac 0

/-- The zero-inflated prior from [a finite signed certificate](hyp:C) [is a probability
measure](goal) when [the shift](hyp:a) [is positive](hyp:ha), [the support ratio](hyp:κ) [is
positive](hyp:hκ), and [the certificate variation is supported between the resulting lower
endpoint and the support bound](hyp:B,hsupp). -/
theorem zeroInflatedPrior_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    IsProbabilityMeasure (C.zeroInflatedPrior a) := by
  let q := ∫ p, a / (p + a) ∂C.signedMeasure.variation
  have hq0 : 0 ≤ q := integral_nonneg_of_ae (tilt_nonneg_ae C a κ B ha hκ hsupp)
  have hq1 : q ≤ 1 := by
    simpa [q] using integral_mono_ae (integrable_tilt C a κ B ha hκ hsupp)
      (integrable_const 1) (tilt_le_one_ae C a κ B ha hκ hsupp)
  constructor
  rw [zeroInflatedPrior, Measure.add_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ 0), smul_eq_mul, mul_one,
    setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tilt C a κ B ha hκ hsupp)
      (tilt_nonneg_ae C a κ B ha hκ hsupp)]
  change ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1
  rw [← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1)]
  simp

/-- The zero-inflated prior from [a finite signed certificate](hyp:C) [is supported on zero
together with the certificate's compact support interval](goal) when [the shift](hyp:a) [is
positive](hyp:ha), [the support ratio](hyp:κ) [is positive](hyp:hκ), and [the variation measure
is supported below the stated upper bound](hyp:B,hsupp). -/
theorem zeroInflatedPrior_support
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∀ᵐ p ∂C.zeroInflatedPrior a, p = 0 ∨ p ∈ Set.Icc (a / κ) B := by
  rw [zeroInflatedPrior, ae_add_measure_iff]
  constructor
  · exact (withDensity_absolutelyContinuous _ _).ae_le (hsupp.mono fun p hp => Or.inr hp)
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff]
    · exact Or.inl rfl
    · exact (measurableSet_singleton 0).union (measurableSet_Icc)

private theorem integrable_id_zeroInflatedPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    Integrable (fun p : ℝ => p) (C.zeroInflatedPrior a) := by
  letI := zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  apply Integrable.of_bound measurable_id.aestronglyMeasurable |B|
  filter_upwards [zeroInflatedPrior_support C a κ B ha hκ hsupp] with p hp
  rcases hp with rfl | hp
  · simp
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hp.2.trans (le_abs_self B)
    · exact (div_pos ha hκ).le.trans hp.1

private theorem integrable_sq_zeroInflatedPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    Integrable (fun p : ℝ => p ^ 2) (C.zeroInflatedPrior a) := by
  letI := zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  apply Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable (|B| ^ 2)
  filter_upwards [zeroInflatedPrior_support C a κ B ha hκ hsupp] with p hp
  rcases hp with rfl | hp
  · norm_num
    positivity
  · change |p ^ 2| ≤ |B| ^ 2
    rw [abs_of_nonneg (pow_nonneg (le_of_lt ((div_pos ha hκ).trans_le hp.1)) 2)]
    have hpB : |p| ≤ |B| := by
      rw [abs_of_nonneg ((div_pos ha hκ).le.trans hp.1)]
      exact hp.2.trans (le_abs_self B)
    nlinarith [abs_nonneg p, abs_nonneg B, sq_abs p]

/-- For [a finite signed moment certificate](hyp:C), [a positive
shift](hyp:a,ha), [a positive support ratio](hyp:κ,hκ), [a support upper
bound](hyp:B), and [variation supported on the corresponding compact
interval](hyp:hsupp), [the zero-inflated prior's first moment equals the shift
times the variation expectation of the tilted coordinate](goal). -/
theorem integral_id_zeroInflatedPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∫ p, p ∂C.zeroInflatedPrior a =
      a * ∫ p, p / (p + a) ∂C.signedMeasure.variation := by
  have hprior := integrable_id_zeroInflatedPrior C a κ B ha hκ hsupp
  have hleft : Integrable (fun p : ℝ => p)
      (C.signedMeasure.variation.withDensity (fun p => ENNReal.ofReal (a / (p + a)))) :=
    by
      simpa [zeroInflatedPrior] using
        hprior.mono_measure (Measure.le_add_right (μ :=
          C.signedMeasure.variation.withDensity
            (fun p => ENNReal.ofReal (a / (p + a)))) le_rfl)
  have hright : Integrable (fun p : ℝ => p)
      (ENNReal.ofReal (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation) •
        Measure.dirac 0) :=
    by
      simpa [zeroInflatedPrior] using
        hprior.mono_measure (Measure.le_add_left (μ :=
          ENNReal.ofReal (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation) •
            Measure.dirac (0 : ℝ)) le_rfl)
  rw [zeroInflatedPrior, integral_add_measure hleft hright,
    integral_withDensity_eq_integral_toReal_smul (measurable_tilt a).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun p : ℝ => p),
    integral_smul_measure, integral_dirac]
  simp only [smul_eq_mul, mul_zero, add_zero]
  calc
    ∫ p, (ENNReal.ofReal (a / (p + a))).toReal * p ∂C.signedMeasure.variation =
        ∫ p, (a / (p + a)) * p ∂C.signedMeasure.variation := by
      apply integral_congr_ae
      filter_upwards [tilt_nonneg_ae C a κ B ha hκ hsupp] with p hp
      rw [ENNReal.toReal_ofReal hp]
    _ = ∫ p, a * (p / (p + a)) ∂C.signedMeasure.variation := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by ring
    _ = a * ∫ p, p / (p + a) ∂C.signedMeasure.variation := by
      rw [integral_const_mul]

/-- For [a finite signed moment certificate](hyp:C), [a positive
shift](hyp:a,ha), [a positive support ratio](hyp:κ,hκ), [a support upper
bound](hyp:B), and [variation supported on the corresponding compact
interval](hyp:hsupp), [the zero-inflated prior's second moment is at most the
support upper bound times its first moment](goal). -/
theorem integral_sq_zeroInflatedPrior_le
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∫ p, p ^ 2 ∂C.zeroInflatedPrior a ≤ B * ∫ p, p ∂C.zeroInflatedPrior a := by
  have hid := integrable_id_zeroInflatedPrior C a κ B ha hκ hsupp
  have hsq := integrable_sq_zeroInflatedPrior C a κ B ha hκ hsupp
  rw [← integral_const_mul]
  apply integral_mono_ae hsq (hid.const_mul B)
  filter_upwards [zeroInflatedPrior_support C a κ B ha hκ hsupp] with p hp
  rcases hp with rfl | hp
  · simp
  · have hp0 : 0 ≤ p := (div_pos ha hκ).le.trans hp.1
    simpa [pow_two] using mul_le_mul_of_nonneg_right hp.2 hp0

/-- The [finite-product zero-inflated prior measure](goal) [takes the product of the scalar
zero-inflated prior measures across the coordinates](step:1). It is built from [a finite signed
certificate](hyp:C), [a shift parameter](hyp:a), and [a coordinate count](hyp:k).

As for the scalar version, the shift is an arbitrary real; positivity is a hypothesis of the
results that need it. -/
noncomputable def zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a : ℝ)
    (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => C.zeroInflatedPrior a

/-- The [finite-coordinate product](hyp:k) of the zero-inflated prior from [a finite signed
certificate](hyp:C) [is a probability measure](goal) when [the shift](hyp:a) [is
positive](hyp:ha), [the support ratio](hyp:κ) [is positive](hyp:hκ), and [the certificate
variation has the stated support bound](hyp:B,hsupp). -/
theorem zeroInflatedProductPrior_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    IsProbabilityMeasure (C.zeroInflatedProductPrior a k) := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  change IsProbabilityMeasure (Measure.pi fun _ : Fin k => C.zeroInflatedPrior a)
  exact inferInstance

/-- Every coordinate in the [finite product](hyp:k) of the zero-inflated prior from [a finite
signed certificate](hyp:C) [lies almost surely at zero or in the certificate's compact support
interval](goal) when [the shift](hyp:a) [is positive](hyp:ha), [the support ratio](hyp:κ) [is
positive](hyp:hκ), and [the variation measure has the stated support bound](hyp:B,hsupp). -/
theorem zeroInflatedProductPrior_support
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∀ᵐ w ∂C.zeroInflatedProductPrior a k,
      ∀ i, w i = 0 ∨ w i ∈ Set.Icc (a / κ) B := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  rw [zeroInflatedProductPrior, ae_all_iff]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => C.zeroInflatedPrior a)).eventually
    (zeroInflatedPrior_support C a κ B ha hκ hsupp)

/-- A selected [coordinate](hyp:i) of the [finite product](hyp:k) from [a finite signed
certificate](hyp:C) [has the scalar zero-inflated first moment](goal) when [the shift](hyp:a)
[is positive](hyp:ha), [the support ratio](hyp:κ) [is positive](hyp:hκ), and [the variation
measure has the stated support bound](hyp:B,hsupp). -/
theorem integral_coordinate_zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (i : Fin k) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∫ w, w i ∂C.zeroInflatedProductPrior a k =
      a * ∫ p, p / (p + a) ∂C.signedMeasure.variation := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  rw [zeroInflatedProductPrior,
    integral_comp_eval (μ := fun _ : Fin k => C.zeroInflatedPrior a)
      (f := fun p : ℝ => p) measurable_id.aestronglyMeasurable]
  exact integral_id_zeroInflatedPrior C a κ B ha hκ hsupp

/-- A selected [coordinate](hyp:i) of the [finite product](hyp:k) from [a finite signed
certificate](hyp:C) [has the scalar zero-inflated second moment](goal) when [the shift](hyp:a)
[is positive](hyp:ha), [the support ratio](hyp:κ) [is positive](hyp:hκ), and [the variation
measure has the stated support bound](hyp:B,hsupp). -/
theorem integral_coordinate_sq_zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (i : Fin k) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∫ w, (w i) ^ 2 ∂C.zeroInflatedProductPrior a k =
      ∫ p, p ^ 2 ∂C.zeroInflatedPrior a := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  rw [zeroInflatedProductPrior,
    integral_comp_eval (μ := fun _ : Fin k => C.zeroInflatedPrior a)
      (f := fun p : ℝ => p ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable]

/-- A selected [coordinate](hyp:i) of the [finite product](hyp:k) from [a finite signed
certificate](hyp:C) [has the same variance as the scalar zero-inflated prior](goal) when [the
shift](hyp:a) [is positive](hyp:ha), [the support ratio](hyp:κ) [is positive](hyp:hκ), and [the
variation measure has the stated support bound](hyp:B,hsupp). -/
theorem variance_coordinate_zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (i : Fin k) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    variance (fun w : Fin k → ℝ => w i) (C.zeroInflatedProductPrior a k) =
      variance id (C.zeroInflatedPrior a) := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  change variance (id ∘ Function.eval i)
      (Measure.pi fun _ : Fin k => C.zeroInflatedPrior a) =
    variance id (C.zeroInflatedPrior a)
  calc
    _ = variance id (Measure.map (Function.eval i)
        (Measure.pi fun _ : Fin k => C.zeroInflatedPrior a)) :=
      (variance_map measurable_id.aemeasurable (measurable_pi_apply i).aemeasurable).symm
    _ = variance id (C.zeroInflatedPrior a) := by
      rw [(measurePreserving_eval (fun _ : Fin k => C.zeroInflatedPrior a) i).map_eq]

/-- The sum over the [finite product coordinates](hyp:k) from [a finite signed
certificate](hyp:C) [has expectation equal to the coordinate count times the scalar
zero-inflated first moment](goal) when [the shift](hyp:a) [is positive](hyp:ha), [the support
ratio](hyp:κ) [is positive](hyp:hκ), and [the variation measure has the stated support
bound](hyp:B,hsupp). -/
theorem integral_sum_zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    ∫ w, ∑ i, w i ∂C.zeroInflatedProductPrior a k =
      k * (a * ∫ p, p / (p + a) ∂C.signedMeasure.variation) := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  rw [zeroInflatedProductPrior]
  calc
    (∫ w, ∑ i, w i ∂Measure.pi fun _ : Fin k => C.zeroInflatedPrior a) =
        ∑ i, ∫ w, w i ∂Measure.pi fun _ : Fin k => C.zeroInflatedPrior a := by
      simpa using (integral_finsetSum Finset.univ (μ :=
          Measure.pi fun _ : Fin k => C.zeroInflatedPrior a) (f :=
          fun (i : Fin k) (w : Fin k → ℝ) => w i) (fun i _ =>
            integrable_comp_eval (μ := fun _ : Fin k => C.zeroInflatedPrior a)
              (integrable_id_zeroInflatedPrior C a κ B ha hκ hsupp)))
    _ = k * (a * ∫ p, p / (p + a) ∂C.signedMeasure.variation) := by
      simp_rw [integral_comp_eval (μ := fun _ : Fin k => C.zeroInflatedPrior a)
        (f := fun p : ℝ => p) measurable_id.aestronglyMeasurable,
        integral_id_zeroInflatedPrior C a κ B ha hκ hsupp, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The sum over the [finite product coordinates](hyp:k) from [a finite signed
certificate](hyp:C) [has variance equal to the coordinate count times the scalar zero-inflated
variance](goal) when [the shift](hyp:a) [is positive](hyp:ha), [the support ratio](hyp:κ) [is
positive](hyp:hκ), and [the variation measure has the stated support bound](hyp:B,hsupp). -/
theorem variance_sum_zeroInflatedProductPrior
    (C : NormalizedFiniteSignedMomentCertificate ι L) (a κ B : ℝ)
    (k : ℕ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    variance (fun w : Fin k → ℝ => ∑ i, w i) (C.zeroInflatedProductPrior a k) =
      k * variance id (C.zeroInflatedPrior a) := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    zeroInflatedPrior_isProbabilityMeasure C a κ B ha hκ hsupp
  rw [zeroInflatedProductPrior]
  have hfun : (fun w : Fin k → ℝ => ∑ i, w i) =
      ∑ i, fun w : Fin k → ℝ => w i := by
    funext w
    simp
  rw [hfun]
  have hmem : MemLp id 2 (C.zeroInflatedPrior a) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (integrable_sq_zeroInflatedPrior C a κ B ha hκ hsupp)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (variance_sum_pi (μ := fun _ : Fin k => C.zeroInflatedPrior a)
      (X := fun _ => id) (fun _ => hmem))

end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

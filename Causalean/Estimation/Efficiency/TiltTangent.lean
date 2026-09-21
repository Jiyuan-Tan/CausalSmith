/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ATETangent
public import Causalean.Estimation.Efficiency.PathwiseGradient
public import Causalean.Estimation.Efficiency.ExponentialTilt
public import Causalean.Mathlib.MeasureTheory.BoundedCenteredDense

/-!
# Bounded exponential tilts generate the nonparametric tangent space

This module realizes every bounded measurable mean-zero function as the score
of the normalized exponential tilt through a probability law. It proves the
derivative of tilted expectations, proves the DQM square-root-density expansion,
shows that the closed linear span of these tilt scores is all of `L²₀`, and
identifies the generated tangent space with that mean-zero subspace. The final
specialization identifies this space with the ATE layer's `Tfull`. The regular
submodel construction plays the score-realization role of van der Vaart (1998),
Example 25.16, using normalized exponential tilts instead of its bounded-link
paths; the later tangent-space and efficient-influence-function results are
proved separately here.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open MeasureTheory Real Filter Topology Asymptotics
open Causalean.Mathlib.MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

variable {Z : Type*} [MeasurableSpace Z]

/-- For [a probability law `P`](hyp:P), the [bounded exponential-tilt score set](goal) consists
of L² classes that have an everywhere measurable, everywhere bounded,
mean-zero representative whose L² class is the specified vector. -/
def tiltScoreSet (P : Measure Z) [IsProbabilityMeasure P] : Set (Lp ℝ 2 P) :=
  {f | ∃ (g : Z → ℝ) (M : ℝ) (hg : MemLp g 2 P), Measurable g ∧
    (∀ z, |g z| ≤ M) ∧ (∫ z, g z ∂P) = 0 ∧ hg.toLp g = f}

/-- Given [a probability law `P`](hyp:P), [a measurable function `g`](hyp:g,hg_meas)
[bounded in absolute value by `M`](hyp:M,hgM),
and [a perturbation `t`](hyp:t), the [L² exponential half-density](goal) is represented by
`z ↦ exp(t g(z)/2)`. -/
noncomputable def expHalfLp (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) (M : ℝ) (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (t : ℝ) : Lp ℝ 2 P :=
  (MemLp.of_bound ((hg_meas.const_mul t).div_const 2 |>.exp.aestronglyMeasurable)
    (Real.exp (|t| * |M|)) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        t * g z / 2 ≤ |t * g z / 2| := le_abs_self _
        _ ≤ |t| * |M| := by
          rw [abs_div, abs_mul]
          have hgM' : |g z| ≤ |M| := (hgM z).trans (le_abs_self M)
          nlinarith [abs_nonneg t, abs_nonneg M]
    )).toLp (fun z => Real.exp (t * g z / 2))

private theorem norm_toLp_sq_eq_integral_sq {P : Measure Z} {f : Z → ℝ}
    (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ z, f z ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  simp only [hz, Real.inner_apply, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs, sq_abs]

/-- For [a probability law `P`](hyp:P), a [measurable function `g`](hyp:g,hg_meas)
[bounded by `M`](hyp:M,hgM), and [its L² certificate](hyp:hg), [the exponential
half-density curve has L² derivative `g/2` at zero](goal). -/
theorem hasDerivAt_expHalfLp
    (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) (M : ℝ) (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg : MemLp g 2 P) :
    HasDerivAt (expHalfLp P g M hg_meas hgM)
      ((2 : ℝ)⁻¹ • hg.toLp g) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  let h : Z → ℝ := fun z => (2 : ℝ)⁻¹ * g z
  have hh : MemLp h 2 P := by
    change MemLp ((2 : ℝ)⁻¹ • g) 2 P
    exact hg.const_smul (2 : ℝ)⁻¹
  let r : ℝ → Z → ℝ := fun t z => Real.exp (t * g z / 2) - 1 - t * h z
  have he (t : ℝ) : MemLp (fun z => Real.exp (t * g z / 2)) 2 P := by
    exact MemLp.of_bound
      ((hg_meas.const_mul t).div_const 2 |>.exp.aestronglyMeasurable)
      (Real.exp (|t| * |M|)) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          t * g z / 2 ≤ |t * g z / 2| := le_abs_self _
          _ ≤ |t| * |M| := by
            rw [abs_div, abs_mul]
            have hgM' : |g z| ≤ |M| := (hgM z).trans (le_abs_self M)
            nlinarith [abs_nonneg t, abs_nonneg M])
  have hr (t : ℝ) : MemLp (r t) 2 P := by
    exact ((he t).sub (memLp_const (1 : ℝ))).sub (hh.const_smul t)
  have hremainder (t : ℝ) :
      expHalfLp P g M hg_meas hgM t - expHalfLp P g M hg_meas hgM 0 -
          t • ((2 : ℝ)⁻¹ • hg.toLp g) = (hr t).toLp (r t) := by
    change (he t).toLp (fun z => Real.exp (t * g z / 2)) -
        (he 0).toLp (fun z => Real.exp (0 * g z / 2)) -
        t • ((2 : ℝ)⁻¹ • hg.toLp g) = _
    have hone : (he 0).toLp (fun z => Real.exp (0 * g z / 2)) =
        (memLp_const (1 : ℝ)).toLp (fun _ : Z => (1 : ℝ)) := by
      apply MemLp.toLp_congr
      exact ae_of_all _ fun z => by simp
    rw [hone]
    have hhLp : hh.toLp h = (2 : ℝ)⁻¹ • hg.toLp g := by
      change (hg.const_smul (2 : ℝ)⁻¹).toLp ((2 : ℝ)⁻¹ • g) = _
      exact MemLp.toLp_const_smul (2 : ℝ)⁻¹ hg
    rw [← hhLp, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    exact ae_of_all _ fun z => by
      simp [r, h, Pi.smul_apply, smul_eq_mul]
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * |M| ≤ 1 := by
    by_cases hM : |M| = 0
    · simp [hM]
    · apply Metric.eventually_nhds_iff.mpr
      have hMpos : 0 < |M| := lt_of_le_of_ne (abs_nonneg M) (Ne.symm hM)
      refine ⟨|M|⁻¹, inv_pos.mpr hMpos, ?_⟩
      intro t ht
      rw [Real.dist_eq, sub_zero] at ht
      exact le_of_lt <| calc
        |t| * |M| < |M|⁻¹ * |M| := mul_lt_mul_of_pos_right ht hMpos
        _ = 1 := inv_mul_cancel₀ hM
  have hnorm : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖expHalfLp P g M hg_meas hgM t - expHalfLp P g M hg_meas hgM 0 -
          t • ((2 : ℝ)⁻¹ • hg.toLp g)‖ ≤ |M| ^ 2 * ‖t ^ 2‖ := by
    filter_upwards [hlocal] with t ht
    rw [hremainder]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
    rw [norm_toLp_sq_eq_integral_sq]
    have hrint : Integrable (fun z => r t z ^ 2) P := by
      have hi := (memLp_two_iff_integrable_sq_norm (hr t).1).1 (hr t)
      simpa only [Real.norm_eq_abs, sq_abs] using hi
    calc
      (∫ z, r t z ^ 2 ∂P) ≤ ∫ _z, ((|t| * |M|) ^ 2) ^ 2 ∂P := by
        apply integral_mono
        · exact hrint
        · exact integrable_const _
        · intro z
          dsimp only
          rw [← sq_abs (r t z)]
          apply (sq_le_sq₀ (abs_nonneg _) (sq_nonneg _)).2
          dsimp only [r, h]
          have hx : t * ((2 : ℝ)⁻¹ * g z) = t * g z / 2 := by ring
          rw [hx]
          have harg : |t * g z / 2| ≤ |t| * |M| := by
            rw [abs_div, abs_mul]
            have hgM' : |g z| ≤ |M| := (hgM z).trans (le_abs_self M)
            nlinarith [abs_nonneg t, abs_nonneg M]
          exact (Real.abs_exp_sub_one_sub_id_le (harg.trans ht)).trans
            (by
              rw [sq_le_sq, abs_of_nonneg (mul_nonneg (abs_nonneg t) (abs_nonneg M))]
              exact harg)
      _ = ((|t| * |M|) ^ 2) ^ 2 := by simp
      _ = (|M| ^ 2 * ‖t ^ 2‖) ^ 2 := by
        rw [Real.norm_eq_abs, abs_sq]
        congr 1
        rw [mul_pow, sq_abs, sq_abs]
        ring
  have hbig :
      (fun t => expHalfLp P g M hg_meas hgM t - expHalfLp P g M hg_meas hgM 0 -
        t • ((2 : ℝ)⁻¹ • hg.toLp g)) =O[𝓝 0] fun t : ℝ => t ^ 2 :=
    Asymptotics.IsBigO.of_bound (|M| ^ 2) hnorm
  simpa only [zero_add] using
    hbig.trans_isLittleO (isLittleO_pow_id (by norm_num : 1 < 2))

/-- For [a probability law `P`](hyp:P) and [a real function `g`](hyp:g), [the exponential tilt
passes through `P` at parameter zero](goal). -/
@[simp] theorem tiltMeasure_zero (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) :
    tiltMeasure P g 0 = P := by
  rw [tiltMeasure, tiltNorm_zero]
  simp

/-- For [a probability law `P`](hyp:P), a [measurable score `g`](hyp:g,hg_meas)
[bounded by `M`](hyp:M,hgM), and [a perturbation `t`](hyp:t), [the L² square-root
Radon--Nikodym density of the normalized tilt](goal) is the exponential
half-density scaled by the inverse square root of its normalizer. -/
theorem rnSqrtDensityLp_tiltMeasure
    (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) (M t : ℝ) (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M) :
    (let _ : IsProbabilityMeasure (tiltMeasure P g t) :=
      isProbabilityMeasure_tiltMeasure hg_meas hgM
    rnSqrtDensityLp P (tiltMeasure P g t)) =
      (Real.sqrt (tiltNorm P g t))⁻¹ • expHalfLp P g M hg_meas hgM t := by
  letI : IsProbabilityMeasure (tiltMeasure P g t) :=
    isProbabilityMeasure_tiltMeasure hg_meas hgM
  change rnSqrtDensityLp P (tiltMeasure P g t) = _
  have hc : 0 < tiltNorm P g t := tiltNorm_pos hg_meas hgM
  have hrn : (tiltMeasure P g t).rnDeriv P =ᵐ[P] fun z =>
      ENNReal.ofReal (Real.exp (t * g z) / tiltNorm P g t) := by
    rw [tiltMeasure_eq_withDensity_div P g M t hg_meas hgM]
    exact Measure.rnDeriv_withDensity P (by fun_prop)
  have hexp_ae : (expHalfLp P g M hg_meas hgM t : Z → ℝ) =ᵐ[P]
      fun z => Real.exp (t * g z / 2) := by
    unfold expHalfLp
    exact MemLp.coeFn_toLp _
  have hsmul_ae := Lp.coeFn_smul (Real.sqrt (tiltNorm P g t))⁻¹
    (expHalfLp P g M hg_meas hgM t)
  apply Lp.ext
  filter_upwards [(rnSqrtDensity_memLp P (tiltMeasure P g t)).coeFn_toLp,
    hrn, hexp_ae, hsmul_ae] with z hz hrnz hexpz hsmulz
  rw [show rnSqrtDensityLp P (tiltMeasure P g t) z =
    rnSqrtDensity P (tiltMeasure P g t) z from hz]
  simp only [rnSqrtDensity, hrnz]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hc.le)]
  rw [Real.sqrt_div (Real.exp_pos _).le, ← Real.exp_half]
  rw [hsmulz, Pi.smul_apply, smul_eq_mul, hexpz]
  simp [div_eq_mul_inv, mul_comm]

/-- For [a probability law `P`](hyp:P), a [measurable bounded mean-zero score
`g`](hyp:g,hg_meas,hgM,hg_mean), and [its L² certificate](hyp:hg), [the L²
square-root density curve of the normalized exponential tilt has derivative
`g/2` at zero](goal). -/
theorem hasDerivAt_rnSqrtDensityLp_tiltMeasure
    (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) (M : ℝ) (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0) (hg : MemLp g 2 P) :
    HasDerivAt (fun t =>
      letI := isProbabilityMeasure_tiltMeasure (P := P) (t := t) hg_meas hgM
      rnSqrtDensityLp P (tiltMeasure P g t))
      ((2 : ℝ)⁻¹ • hg.toLp g) 0 := by
  have hc : HasDerivAt (fun t => tiltNorm P g t) 0 0 := by
    have h := hasDerivAt_tilt_numerator (P := P) (s := g)
      (φ := fun _ => (1 : ℝ)) hg_meas hgM
      aestronglyMeasurable_const (integrable_const (1 : ℝ))
    simpa [tiltNorm, hg_mean] using h
  have hsqrt : HasDerivAt (fun t => Real.sqrt (tiltNorm P g t)) 0 0 := by
    simpa using hc.sqrt (by simp)
  have hinv := hsqrt.inv (by simp)
  have hexp := hasDerivAt_expHalfLp P g M hg_meas hgM hg
  have hprod := hinv.smul hexp
  have hcurve :
      (fun t =>
        letI := isProbabilityMeasure_tiltMeasure (P := P) (t := t) hg_meas hgM
        rnSqrtDensityLp P (tiltMeasure P g t)) =
      ((fun t => Real.sqrt (tiltNorm P g t))⁻¹ •
        expHalfLp P g M hg_meas hgM) := by
    funext t
    letI : IsProbabilityMeasure (tiltMeasure P g t) :=
      isProbabilityMeasure_tiltMeasure hg_meas hgM
    change rnSqrtDensityLp P (tiltMeasure P g t) =
      (Real.sqrt (tiltNorm P g t))⁻¹ • expHalfLp P g M hg_meas hgM t
    exact rnSqrtDensityLp_tiltMeasure P g M t hg_meas hgM
  rw [hcurve]
  apply hprod.congr_deriv
  simp

/-- The [normalized exponential tilt is a regular submodel with the prescribed
square-integrable score](goal) for [a probability law](hyp:P) and [a measurable
score](hyp:g,hg_meas) that is [bounded](hyp:M,hgM), [mean
zero](hyp:hg_mean), and [square-integrable](hyp:hg).

This supplies the bounded-score path-realization ingredient associated with van der Vaart
(1998), Example 25.16, using a normalized exponential tilt rather than its bounded-link path. -/
noncomputable def tiltRegularSubmodel (P : Measure Z) [IsProbabilityMeasure P]
    (g : Z → ℝ) (M : ℝ) (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0) (hg : MemLp g 2 P) :
    RegularSubmodel P where
  path := fun t => tiltMeasure P g t
  path_probability := fun t => isProbabilityMeasure_tiltMeasure hg_meas hgM
  path_zero := by simp
  path_ac := fun t => by
    rw [tiltMeasure_eq_withDensity_div P g M t hg_meas hgM]
    exact withDensity_absolutelyContinuous _ _
  score := hg.toLp g
  score_meanZero := by
    rw [meanZeroLp, Submodule.mem_orthogonal_singleton_iff_inner_left,
      inner_lpOne_eq_integral]
    rw [integral_congr_ae hg.coeFn_toLp]
    exact hg_mean
  dqm := by
    have hd := hasDerivAt_rnSqrtDensityLp_tiltMeasure P g M
      hg_meas hgM hg_mean hg
    have hslope := hd.tendsto_slope_zero
    simpa [dqmQuotient, tiltMeasure_zero] using hslope

/-- For [a probability law `P`](hyp:P), the [bounded exponential-tilt submodel
family](goal) consists exactly of the regular submodels constructed from
measurable bounded mean-zero scores. -/
def boundedTiltSubmodels (P : Measure Z) [IsProbabilityMeasure P] :
    Set (RegularSubmodel P) :=
  {m | ∃ (g : Z → ℝ) (M : ℝ) (hg_meas : Measurable g)
      (hgM : ∀ z, |g z| ≤ M) (hg_mean : ∫ z, g z ∂P = 0)
      (hg : MemLp g 2 P), m = tiltRegularSubmodel P g M hg_meas hgM hg_mean hg}

/-- Along the normalized exponential tilt of [a probability law `P`](hyp:P) by a
[measurable](hyp:hg_meas), [bounded](hyp:hgM), [mean-zero score `g`](hyp:g,hg_mean), the
expectation of a fixed [almost-everywhere strongly measurable](hyp:hφ_meas) and
[integrable test function `φ`](hyp:φ,hφ_int) is [differentiable at zero with derivative
`∫ φ g dP`](goal). -/
theorem hasDerivAt_integral_tiltMeasure {P : Measure Z} [IsProbabilityMeasure P]
    {g φ : Z → ℝ} {M : ℝ}
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0)
    (hφ_meas : AEStronglyMeasurable φ P) (hφ_int : Integrable φ P) :
    HasDerivAt (fun t => ∫ z, φ z ∂(tiltMeasure P g t))
      (∫ z, φ z * g z ∂P) 0 := by
  have hfun : (fun t => ∫ z, φ z ∂(tiltMeasure P g t)) = tiltExp P g φ := by
    funext t
    exact integral_tiltMeasure hg_meas hgM
  rw [hfun]
  exact hasDerivAt_tiltExp hg_meas hgM hg_mean hφ_meas hφ_int

/-- Along the normalized exponential tilt of [a probability law `P`](hyp:P) by a
[measurable](hyp:hg_meas), [bounded](hyp:hgM), [mean-zero score `g`](hyp:g,hg_mean), the
expectation of every [square-integrable test function `φ`](hyp:φ,hφ) is [differentiable at zero
with derivative `∫ φ g dP`](goal). -/
theorem hasDerivAt_integral_tiltMeasure_of_memLp
    {P : Measure Z} [IsProbabilityMeasure P] {g φ : Z → ℝ} {M : ℝ}
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0) (hφ : MemLp φ 2 P) :
    HasDerivAt (fun t => ∫ z, φ z ∂(tiltMeasure P g t))
      (∫ z, φ z * g z ∂P) 0 :=
  hasDerivAt_integral_tiltMeasure hg_meas hgM hg_mean hφ.1
    (hφ.integrable (by norm_num))

/-- For [a probability law `P`](hyp:P), [the closed linear span of bounded exponential-tilt
scores is exactly the mean-zero subspace of `L²(P)`](goal). -/
theorem tiltScoreSpan_eq_meanZeroLp (P : Measure Z) [IsProbabilityMeasure P] :
    (Submodule.span ℝ (tiltScoreSet P)).topologicalClosure = meanZeroLp P := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro f ⟨g, _M, hg, _hg_meas, _hgM, hg_mean, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      rw [inner_lpOne_eq_integral]
      rw [integral_congr_ae hg.coeFn_toLp]
      exact hg_mean
    · exact Submodule.isClosed_orthogonal (ℝ ∙ lpOne P)
  · rw [← boundedCenteredLp_topologicalClosure]
    apply Submodule.topologicalClosure_mono
    intro f hf
    apply Submodule.subset_span
    exact mem_boundedCenteredLp_exists P f hf

/-- For [a probability law `P`](hyp:P), [every bounded exponential-tilt score is a score in the
efficiency layer's abstract regular-submodel score set](goal). -/
theorem tiltScoreSet_subset_scoreSet (P : Measure Z) [IsProbabilityMeasure P] :
    tiltScoreSet P ⊆ scoreSet P (boundedTiltSubmodels P) := by
  rintro f ⟨g, M, hg, hg_meas, hgM, hg_mean, hgf⟩
  refine ⟨tiltRegularSubmodel P g M hg_meas hgM hg_mean hg, ?_, ?_⟩
  · exact ⟨g, M, hg_meas, hgM, hg_mean, hg, rfl⟩
  · simpa [tiltRegularSubmodel] using hgf

/-- For [a probability law `P`](hyp:P), [the score set of the bounded-tilt
submodel family is the set of bounded centered L² scores](goal). -/
theorem scoreSet_boundedTiltSubmodels_eq_tiltScoreSet
    (P : Measure Z) [IsProbabilityMeasure P] :
    scoreSet P (boundedTiltSubmodels P) = tiltScoreSet P := by
  apply Set.Subset.antisymm
  · rintro f ⟨m, ⟨g, M, hg_meas, hgM, hg_mean, hg, rfl⟩, rfl⟩
    exact ⟨g, M, hg, hg_meas, hgM, hg_mean, rfl⟩
  · exact tiltScoreSet_subset_scoreSet P

/-- For [a probability law `P`](hyp:P), [the tangent space generated by bounded
exponential tilts is all of `L²₀(P)`](goal). -/
theorem tangentSpace_boundedTiltSubmodels_eq_meanZeroLp
    (P : Measure Z) [IsProbabilityMeasure P] :
    tangentSpace P (boundedTiltSubmodels P) = meanZeroLp P := by
  rw [tangentSpace, scoreSet_boundedTiltSubmodels_eq_tiltScoreSet,
    tiltScoreSpan_eq_meanZeroLp]

/-- For [a probability law `P`](hyp:P), [the abstract tangent space generated by all regular
submodels equals the full mean-zero subspace of `L²(P)`](goal); bounded exponential tilts already
generate the reverse inclusion. -/
theorem tangentSpace_eq_meanZeroLp (P : Measure Z) [IsProbabilityMeasure P] :
    tangentSpace P Set.univ = meanZeroLp P := by
  apply le_antisymm
  · rw [tangentSpace]
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro f ⟨m, _, rfl⟩
      exact m.score_meanZero
    · exact Submodule.isClosed_orthogonal (ℝ ∙ lpOne P)
  · rw [← tiltScoreSpan_eq_meanZeroLp]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_mono
    intro f hf
    rcases tiltScoreSet_subset_scoreSet P hf with ⟨m, _hm, rfl⟩
    exact ⟨m, Set.mem_univ m, rfl⟩

/-- **Nonparametric efficient-influence-function recipe.** Given [a probability
law `P`](hyp:P), [a law functional `ψ`](hyp:ψ), and [a mean-zero L² candidate
`φ`](hyp:φ,hφ), suppose [for every measurable bounded mean-zero score `g`, the
derivative of `ψ` along the normalized exponential tilt equals `⟪φ,g⟫`](hyp:hderiv).
Then [`φ` is the efficient influence function of `ψ` in the nonparametric
model generated by bounded tilts](goal).

To use this theorem, the user checks only three items: the candidate is in
`L²₀(P)`; each bounded centered tilt derivative exists; and that derivative is
the displayed covariance pairing. Tilt DQM and density of their scores are
already proved by this module. -/
theorem isEfficientInfluenceFunction_of_hasDerivAt_tilt
    (P : Measure Z) [IsProbabilityMeasure P]
    (ψ : Measure Z → ℝ) (φ : Lp ℝ 2 P)
    (hφ : φ ∈ meanZeroLp P)
    (hderiv : ∀ (g : Z → ℝ) (M : ℝ) (hg : MemLp g 2 P),
      Measurable g → (∀ z, |g z| ≤ M) → (∫ z, g z ∂P) = 0 →
        HasDerivAt (fun t => ψ (tiltMeasure P g t)) ⟪φ, hg.toLp g⟫_ℝ 0) :
    IsEfficientInfluenceFunction P ψ φ (boundedTiltSubmodels P) := by
  constructor
  · intro m hm
    rcases hm with ⟨g, M, hg_meas, hgM, hg_mean, hg, rfl⟩
    simpa [tiltRegularSubmodel] using hderiv g M hg hg_meas hgM hg_mean
  · rw [tangentSpace_boundedTiltSubmodels_eq_meanZeroLp]
    exact hφ

/-- The [square-integrable class represented by a candidate function is the
efficient influence function of a law functional in the nonparametric
bounded-tilt model](goal) when [the underlying law is a probability
law](hyp:P), [the functional is real-valued](hyp:ψ), [the candidate is
square-integrable](hyp:φ,hφ) with [mean zero](hyp:hφ_mean), and [its pairing
with every measurable bounded mean-zero exponential-tilt score gives the
functional's derivative along that tilt](hyp:hderiv).

Boundedness and measurability automatically put each score `g` in L², so users do not
need to supply a redundant square-integrability certificate for the tilt direction. -/
theorem isEfficientInfluenceFunction_of_hasDerivAt_tilt'
    (P : Measure Z) [IsProbabilityMeasure P]
    (ψ : Measure Z → ℝ) (φ : Z → ℝ)
    (hφ : MemLp φ 2 P) (hφ_mean : ∫ z, φ z ∂P = 0)
    (hderiv : ∀ (g : Z → ℝ) (M : ℝ),
      Measurable g → (∀ z, |g z| ≤ M) → (∫ z, g z ∂P) = 0 →
        HasDerivAt (fun t => ψ (tiltMeasure P g t)) (∫ z, φ z * g z ∂P) 0) :
    IsEfficientInfluenceFunction P ψ (hφ.toLp φ) (boundedTiltSubmodels P) := by
  have hφ0 : hφ.toLp φ ∈ meanZeroLp P := by
    rw [meanZeroLp, Submodule.mem_orthogonal_singleton_iff_inner_left,
      inner_lpOne_eq_integral, integral_congr_ae hφ.coeFn_toLp]
    exact hφ_mean
  apply isEfficientInfluenceFunction_of_hasDerivAt_tilt P ψ (hφ.toLp φ) hφ0
  intro g M hg hg_meas hgM hg_mean
  have hcoef : ⟪hφ.toLp φ, hg.toLp g⟫_ℝ = ∫ z, φ z * g z ∂P := by
    rw [Causalean.Stat.FWLInstanceL2.inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp, hg.coeFn_toLp] with z hφz hgz
    rw [hφz, hgz]
  rw [hcoef]
  exact hderiv g M hg_meas hgM hg_mean

/-- The [centered outcome is the efficient influence function of the mean
functional in the nonparametric bounded-tilt model](goal) whenever [a
probability law on the real line](hyp:P) has a [square-integrable identity
variable](hyp:hY). -/
theorem mean_isEfficientInfluenceFunction
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hY : MemLp (fun y : ℝ => y) 2 P) :
    IsEfficientInfluenceFunction P (fun Q => ∫ y, y ∂Q)
      ((hY.sub (memLp_const (∫ y, y ∂P))).toLp
        (fun y => y - ∫ x, x ∂P))
      (boundedTiltSubmodels P) := by
  let μ : ℝ := ∫ y, y ∂P
  have hcenter : MemLp (fun y : ℝ => y - μ) 2 P := hY.sub (memLp_const μ)
  apply isEfficientInfluenceFunction_of_hasDerivAt_tilt' P
    (fun Q => ∫ y, y ∂Q) (fun y => y - μ) hcenter
  · rw [integral_sub (hY.integrable (by norm_num)) (integrable_const μ),
      integral_const, probReal_univ, one_smul]
    dsimp [μ]
    ring
  · intro g M hg_meas hgM hg_mean
    have hg : MemLp g 2 P := MemLp.of_bound hg_meas.aestronglyMeasurable M
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hgM z)
    have hg_int : Integrable g P := hg.integrable (by norm_num)
    have hYg : Integrable (fun y : ℝ => y * g y) P := by
      have h := (hY.integrable (by norm_num)).bdd_mul hg_meas.aestronglyMeasurable
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hgM z)
      exact h.congr (ae_of_all _ fun z => by ring)
    have hμg : Integrable (fun y : ℝ => μ * g y) P := hg_int.const_mul μ
    have hcoef : (∫ y, (y - μ) * g y ∂P) = ∫ y, y * g y ∂P := by
      calc
        (∫ y, (y - μ) * g y ∂P) =
            ∫ y, y * g y - μ * g y ∂P := by
              apply integral_congr_ae
              filter_upwards with y
              ring
        _ = (∫ y, y * g y ∂P) - ∫ y, μ * g y ∂P := integral_sub hYg hμg
        _ = ∫ y, y * g y ∂P := by rw [integral_const_mul, hg_mean, mul_zero, sub_zero]
    rw [hcoef]
    exact hasDerivAt_integral_tiltMeasure_of_memLp hg_meas hgM hg_mean hY

namespace ATE.BackdoorEstimationSystem

open Causalean.PO

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- For [a backdoor ATE estimation system `S`](hyp:S), [the abstract tangent space at its
observed-data law equals the ATE layer's full mean-zero tangent space `Tfull`](goal). -/
theorem tangentSpace_eq_Tfull (S : ATE.BackdoorEstimationSystem P γ) :
    tangentSpace S.P_Z (boundedTiltSubmodels S.P_Z) = S.Tfull := by
  change tangentSpace S.P_Z (boundedTiltSubmodels S.P_Z) = meanZeroLp S.P_Z
  exact tangentSpace_boundedTiltSubmodels_eq_meanZeroLp S.P_Z

end ATE.BackdoorEstimationSystem

end Causalean.Estimation.Efficiency

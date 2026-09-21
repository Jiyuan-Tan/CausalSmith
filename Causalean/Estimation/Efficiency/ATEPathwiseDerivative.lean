/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ArmMeanEfficientIF

/-!
# Pathwise derivative of the observed-law average treatment effect

This module combines the exact doubly robust expansion with the first-order
tilt bounds.  Under bounded outcomes and strict overlap, the expansion's two
product terms are quadratic in the tilt parameter.  The remaining fixed-AIPW
expectation is differentiated by the bounded-tilt theorem, yielding Hahn's
covariance derivative without assuming it.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory Real Asymptotics Topology
open Causalean.Mathlib.MeasureTheory
open _root_.Causalean.Estimation.ATE.BackdoorEstimationSystem
open scoped InnerProductSpace RealInnerProductSpace

variable {γ : Type*} [MeasurableSpace γ]

/-- **Exact ATE expansion along an exponential tilt.** Given [a measurable uniformly bounded
tilt score](hyp:hg_meas,hgM), [a nonnegative outcome bound and positive overlap level](hyp:hB,hε),
[bounded outcomes](hyp:hY), and [strict base arm propensities](hyp:hoverlap), [the change in the observed-law ATE
minus the tilted mean of the base-law AIPW function is exactly the sum of the treated
and control products of propensity and regression errors](goal). -/
theorem observedATE_tilt_exact_expansion
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    observedATE (tiltMeasure P g t) - observedATE P -
        ∫ z, observedAIPW P z ∂(tiltMeasure P g t) =
      -(∫ z, (observedPropensity (tiltMeasure P g t) true z -
          observedPropensity P true z) / observedPropensity P true z *
        (observedArmRegression (tiltMeasure P g t) true z -
          observedArmRegression P true z) ∂(tiltMeasure P g t)) +
      ∫ z, (observedPropensity (tiltMeasure P g t) false z -
          observedPropensity P false z) / observedPropensity P false z *
        (observedArmRegression (tiltMeasure P g t) false z -
          observedArmRegression P false z) ∂(tiltMeasure P g t) := by
  let Pt := tiltMeasure P g t
  let _ : IsProbabilityMeasure Pt := isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hYt : ∀ᵐ z ∂Pt, |projY z| ≤ B := by
    exact (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hY
  have hp0P (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap d] with z hz
    exact hε.trans_le hz
  have hp0 (d : Bool) : ∀ᵐ z ∂Pt, 0 < observedPropensity P d z :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (hp0P d)
  have hpP (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity Pt d z := by
    dsimp [Pt]
    exact observedPropensity_tilt_pos_ae P g M t d hg_meas hgM (hp0P d)
  have hp (d : Bool) : ∀ᵐ z ∂Pt, 0 < observedPropensity Pt d z :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (hpP d)
  have hYint : Integrable (projY : γ × Bool × ℝ → ℝ) Pt :=
    Integrable.of_bound measurable_snd.snd.aestronglyMeasurable B
      (by simpa [Real.norm_eq_abs] using hYt)
  have hμ0 (d : Bool) : Integrable (observedArmRegression P d) Pt := by
    apply Integrable.of_bound (measurable_observedArmRegression P d).aestronglyMeasurable B
    have hbP := observedArmRegression_abs_le P d B hB hY (hp0P d)
    exact (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Real.norm_eq_abs] using hbP)
  have hμ1 (d : Bool) : Integrable (observedArmRegression Pt d) Pt :=
    integrable_observedArmRegression_of_bounded Pt d B hB hYt (hp d)
  have hinv (d : Bool) : ∀ᵐ z ∂Pt,
      |(observedPropensity P d z)⁻¹| ≤ ε⁻¹ := by
    have hbase := (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (hoverlap d)
    filter_upwards [hbase] with z hz
    have hpz : 0 < observedPropensity P d z := hε.trans_le hz
    rw [abs_of_pos (inv_pos.mpr hpz)]
    exact (inv_le_inv₀ hpz hε).2 hz
  have hres (d : Bool) : Integrable (fun z =>
      observedArmIndicator d z / observedPropensity P d z *
        (projY z - observedArmRegression P d z)) Pt := by
    apply Integrable.of_bound
      (((measurable_observedArmIndicator d).div
        (measurable_observedPropensity P d)).mul
        (measurable_snd.snd.sub (measurable_observedArmRegression P d))).aestronglyMeasurable
      (ε⁻¹ * (B + B))
    have hμbP := observedArmRegression_abs_le P d B hB hY (hp0P d)
    have hμb := (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hμbP
    filter_upwards [hYt, hμb, hinv d] with z hYz hμz hinvz
    change |(observedArmIndicator d z / observedPropensity P d z) *
      (projY z - observedArmRegression P d z)| ≤ ε⁻¹ * (B + B)
    rw [abs_mul, abs_div]
    have hI : |observedArmIndicator d z| ≤ 1 := by
      by_cases hz : projA z = d <;> simp [observedArmIndicator, hz]
    have hfrac : |observedArmIndicator d z| / |observedPropensity P d z| ≤ ε⁻¹ := by
      rw [div_eq_mul_inv, ← abs_inv]
      exact (mul_le_of_le_one_left (abs_nonneg _) hI).trans hinvz
    calc
      |observedArmIndicator d z| / |observedPropensity P d z| *
          |projY z - observedArmRegression P d z| ≤
        ε⁻¹ * (|projY z| + |observedArmRegression P d z|) :=
          mul_le_mul hfrac (abs_sub _ _) (abs_nonneg _) (by positivity)
      _ ≤ ε⁻¹ * (B + B) := by gcongr
  have hprod (d : Bool) : Integrable (fun z =>
      (observedPropensity Pt d z - observedPropensity P d z) /
        observedPropensity P d z *
      (observedArmRegression Pt d z - observedArmRegression P d z)) Pt := by
    have hpI := observedPropensity_mem_Icc_ae Pt d
    have hp0I := (ae_tiltMeasure_iff P g M t hg_meas hgM).2
      (observedPropensity_mem_Icc_ae P d)
    have hμ0b := (ae_tiltMeasure_iff P g M t hg_meas hgM).2
      (observedArmRegression_abs_le P d B hB hY (hp0P d))
    have hμ1b := observedArmRegression_abs_le Pt d B hB hYt (hp d)
    apply Integrable.of_bound
      ((((measurable_observedPropensity Pt d).sub
        (measurable_observedPropensity P d)).div
        (measurable_observedPropensity P d)).mul
        ((measurable_observedArmRegression Pt d).sub
          (measurable_observedArmRegression P d))).aestronglyMeasurable
      (ε⁻¹ * (2 * (2 * B)))
    filter_upwards [hpI, hp0I, hμ0b, hμ1b, hinv d]
      with z hpIz hp0Iz hμ0z hμ1z hinvz
    change |((observedPropensity Pt d z - observedPropensity P d z) /
      observedPropensity P d z) *
      (observedArmRegression Pt d z - observedArmRegression P d z)| ≤
        ε⁻¹ * (2 * (2 * B))
    rw [abs_mul, abs_div, div_eq_mul_inv, ← abs_inv]
    have hpropdiff : |observedPropensity Pt d z - observedPropensity P d z| ≤ 2 :=
      (abs_sub _ _).trans (by
        rw [abs_of_nonneg hpIz.1, abs_of_nonneg hp0Iz.1]
        linarith [hpIz.2, hp0Iz.2])
    have hμdiff : |observedArmRegression Pt d z - observedArmRegression P d z| ≤ 2 * B :=
      (abs_sub _ _).trans (by linarith)
    calc
      |observedPropensity Pt d z - observedPropensity P d z| *
          |(observedPropensity P d z)⁻¹| *
          |observedArmRegression Pt d z - observedArmRegression P d z| ≤
        2 * ε⁻¹ * (2 * B) := by
          exact mul_le_mul (mul_le_mul hpropdiff hinvz (abs_nonneg _) (by norm_num))
            hμdiff (abs_nonneg _) (by positivity)
      _ = ε⁻¹ * (2 * (2 * B)) := by ring
  simpa only [Pt] using observedATE_sub_integral_observedAIPW_eq_product
    P Pt (fun _ => ε⁻¹) hYint hμ0 hμ1 hinv hp0 hp hres hprod

/-- Under [a measurable bounded tilt score](hyp:hg_meas,hgM), [nonnegative tilt and outcome
bounds and a positive overlap level](hyp:hM,hB,hε), [bounded outcomes](hyp:hY), [strict
overlap](hyp:hoverlap), and a [local tilt satisfying `|t|M ≤ 1`](hyp:ht), [the exact ATE remainder is bounded by
the product of the two first-order nuisance bounds](goal), hence is quadratic in the
tilt size. -/
theorem observedATE_tilt_remainder_bound
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z)
    (ht : |t| * M ≤ 1) :
    |observedATE (tiltMeasure P g t) - observedATE P -
        ∫ z, observedAIPW P z ∂(tiltMeasure P g t)| ≤
      2 * (ε⁻¹ * (4 * (|t| * M) / Real.exp (-|t| * M)) *
        (4 * B * (|t| * M) / Real.exp (-|t| * M))) := by
  let Pt := tiltMeasure P g t
  let Cp := 4 * (|t| * M) / Real.exp (-|t| * M)
  let Cμ := 4 * B * (|t| * M) / Real.exp (-|t| * M)
  let K := ε⁻¹ * Cp * Cμ
  let _ : IsProbabilityMeasure Pt := isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hp0P (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap d] with z hz
    exact hε.trans_le hz
  have hinv (d : Bool) : ∀ᵐ z ∂Pt,
      |(observedPropensity P d z)⁻¹| ≤ ε⁻¹ := by
    have hb := (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (hoverlap d)
    filter_upwards [hb] with z hz
    have hpz := hε.trans_le hz
    rw [abs_of_pos (inv_pos.mpr hpz)]
    exact (inv_le_inv₀ hpz hε).2 hz
  have hpropP (d : Bool) := observedPropensity_tilt_firstOrder P g M t d
    hg_meas hgM hM ht
  have hprop (d : Bool) : ∀ᵐ z ∂Pt,
      |observedPropensity Pt d z - observedPropensity P d z| ≤ Cp := by
    exact (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Pt, Cp] using hpropP d)
  have hμP (d : Bool) := observedArmRegression_tilt_firstOrder P g M B t d
    hg_meas hgM hM hB hY (hp0P d) ht
  have hμ (d : Bool) : ∀ᵐ z ∂Pt,
      |observedArmRegression Pt d z - observedArmRegression P d z| ≤ Cμ := by
    exact (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Pt, Cμ] using hμP d)
  have hterm (d : Bool) :
      |∫ z, (observedPropensity Pt d z - observedPropensity P d z) /
          observedPropensity P d z *
        (observedArmRegression Pt d z - observedArmRegression P d z) ∂Pt| ≤ K := by
    have hpoint : ∀ᵐ z ∂Pt,
        ‖(observedPropensity Pt d z - observedPropensity P d z) /
            observedPropensity P d z *
          (observedArmRegression Pt d z - observedArmRegression P d z)‖ ≤ K := by
      filter_upwards [hprop d, hμ d, hinv d] with z hpz hμz hinvz
      rw [Real.norm_eq_abs, abs_mul, abs_div, div_eq_mul_inv, ← abs_inv]
      have hCp : 0 ≤ Cp := by
        dsimp [Cp]
        positivity
      have hCμ : 0 ≤ Cμ := by
        dsimp [Cμ]
        positivity
      have hfirst : |observedPropensity Pt d z - observedPropensity P d z| *
          |(observedPropensity P d z)⁻¹| ≤ Cp * ε⁻¹ :=
        mul_le_mul hpz hinvz (abs_nonneg _) hCp
      have hall := mul_le_mul hfirst hμz (abs_nonneg _)
        (mul_nonneg hCp (inv_nonneg.mpr hε.le))
      calc
        _ ≤ (Cp * ε⁻¹) * Cμ := hall
        _ = K := by dsimp [K]; ring
    simpa [K] using norm_integral_le_of_norm_le_const hpoint
  have hexact := observedATE_tilt_exact_expansion P g M B ε t hg_meas hgM
    hB hε hY hoverlap
  rw [hexact]
  calc
    |-(∫ z, (observedPropensity Pt true z - observedPropensity P true z) /
          observedPropensity P true z *
        (observedArmRegression Pt true z - observedArmRegression P true z) ∂Pt) +
      ∫ z, (observedPropensity Pt false z - observedPropensity P false z) /
          observedPropensity P false z *
        (observedArmRegression Pt false z - observedArmRegression P false z) ∂Pt| ≤
        |(∫ z, (observedPropensity Pt true z - observedPropensity P true z) /
          observedPropensity P true z *
        (observedArmRegression Pt true z - observedArmRegression P true z) ∂Pt)| +
        |(∫ z, (observedPropensity Pt false z - observedPropensity P false z) /
          observedPropensity P false z *
        (observedArmRegression Pt false z - observedArmRegression P false z) ∂Pt)| := by
          simpa only [abs_neg] using abs_add_le
            (-(∫ z, (observedPropensity Pt true z - observedPropensity P true z) /
              observedPropensity P true z *
              (observedArmRegression Pt true z - observedArmRegression P true z) ∂Pt))
            (∫ z, (observedPropensity Pt false z - observedPropensity P false z) /
              observedPropensity P false z *
              (observedArmRegression Pt false z - observedArmRegression P false z) ∂Pt)
    _ ≤ K + K := add_le_add (hterm true) (hterm false)
    _ = 2 * (ε⁻¹ * (4 * (|t| * M) / Real.exp (-|t| * M)) *
        (4 * B * (|t| * M) / Real.exp (-|t| * M))) := by
      simp only [K, Cp, Cμ]
      ring

/-- Under [a measurable bounded tilt score](hyp:hg_meas,hgM), [nonnegative tilt and outcome
bounds and a positive overlap level](hyp:hM,hB,hε), [bounded outcomes and strict overlap](hyp:hY,hoverlap),
and [a local tilt](hyp:ht), the [ATE remainder is bounded by an explicit constant times `t²`](goal). -/
theorem observedATE_tilt_remainder_quadratic
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z)
    (ht : |t| * M ≤ 1) :
    |observedATE (tiltMeasure P g t) - observedATE P -
        ∫ z, observedAIPW P z ∂(tiltMeasure P g t)| ≤
      (32 * ε⁻¹ * B * M ^ 2 * Real.exp 2) * t ^ 2 := by
  have hraw := observedATE_tilt_remainder_bound P g M B ε t hg_meas hgM
    hM hB hε hY hoverlap ht
  let x := |t| * M
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hrecip : (Real.exp (-x))⁻¹ ≤ Real.exp 1 := by
    rw [← Real.exp_neg]
    simp only [neg_neg]
    exact Real.exp_le_exp.mpr ht
  have hp : 4 * x / Real.exp (-x) ≤ 4 * x * Real.exp 1 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip (by positivity)
  have hμ : 4 * B * x / Real.exp (-x) ≤ 4 * B * x * Real.exp 1 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip (by positivity)
  calc
    |observedATE (tiltMeasure P g t) - observedATE P -
        ∫ z, observedAIPW P z ∂(tiltMeasure P g t)| ≤
      2 * (ε⁻¹ * (4 * x / Real.exp (-x)) *
        (4 * B * x / Real.exp (-x))) := by simpa [x] using hraw
    _ ≤ 2 * (ε⁻¹ * (4 * x * Real.exp 1) *
        (4 * B * x * Real.exp 1)) := by
      gcongr
    _ = (32 * ε⁻¹ * B * M ^ 2 * Real.exp 2) * t ^ 2 := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by
        simpa only [one_add_one_eq_two] using Real.exp_add 1 1]
      dsimp [x]
      ring_nf
      rw [sq_abs]
      ring

/-- Given [a probability observed-data law `P`](hyp:P), [a measurable score
`g`](hyp:g,hg_meas) that is [bounded by a nonnegative constant
`M`](hyp:M,hgM,hM) and [has mean zero](hyp:hg_mean), [a nonnegative outcome
bound `B`](hyp:B,hB,hY), and [strict arm overlap at level
`ε`](hyp:ε,hε,hoverlap), [the observed-law ATE along the normalized exponential
tilt has derivative equal to the AIPW covariance with `g`](goal). The result is
the treated-arm derivative minus the control-arm derivative. -/
theorem hasDerivAt_observedATE_tilt
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B ε : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    HasDerivAt (fun t => observedATE (tiltMeasure P g t))
      (∫ z, observedAIPW P z * g z ∂P) 0 := by
  have hp (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap d] with z hz
    exact hε.trans_le hz
  have hμ (d : Bool) : Integrable (observedArmRegression P d) P :=
    integrable_observedArmRegression_of_bounded P d B hB hY (hp d)
  have hfun : (fun t => observedATE (tiltMeasure P g t)) = fun t =>
      observedArmMean (tiltMeasure P g t) true -
        observedArmMean (tiltMeasure P g t) false := by
    funext t
    let Pt := tiltMeasure P g t
    let _ : IsProbabilityMeasure Pt := isProbabilityMeasure_tiltMeasure hg_meas hgM
    have hYt : ∀ᵐ z ∂Pt, |projY z| ≤ B :=
      (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hY
    apply observedATE_eq_observedArmMean_sub
    intro d
    have hptP : ∀ᵐ z ∂P, 0 < observedPropensity Pt d z := by
      dsimp [Pt]
      exact observedPropensity_tilt_pos_ae P g M t d hg_meas hgM (hp d)
    have hpt : ∀ᵐ z ∂Pt, 0 < observedPropensity Pt d z :=
      (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hptP
    exact integrable_observedArmRegression_of_bounded Pt d B hB hYt hpt
  have hd (d : Bool) := hasDerivAt_observedArmMean_tilt P d g M B ε
    hg_meas hgM hg_mean hM hB hε hY (hoverlap d)
  have hφ (d : Bool) := memLp_observedArmEIF P d B ε hB hε hY (hoverlap d)
  have hint (d : Bool) : Integrable (fun z => observedArmEIF P d z * g z) P := by
    have h := (hφ d).integrable (by norm_num) |>.bdd_mul
      hg_meas.aestronglyMeasurable
        (ae_of_all P fun z => by simpa [Real.norm_eq_abs] using hgM z)
    exact h.congr (ae_of_all P fun z => by ring)
  have hcoef :
      (∫ z, observedArmEIF P true z * g z ∂P) -
        ∫ z, observedArmEIF P false z * g z ∂P =
      ∫ z, observedAIPW P z * g z ∂P := by
    rw [← integral_sub (hint true) (hint false)]
    apply integral_congr_ae
    filter_upwards with z
    rw [observedAIPW_eq_armEIF_sub P hμ]
    ring
  rw [hfun]
  change HasDerivAt
    ((fun t => observedArmMean (tiltMeasure P g t) true) -
      fun t => observedArmMean (tiltMeasure P g t) false)
    (∫ z, observedAIPW P z * g z ∂P) 0
  simpa only [hcoef] using (hd true).sub (hd false)

end Causalean.Estimation.Efficiency

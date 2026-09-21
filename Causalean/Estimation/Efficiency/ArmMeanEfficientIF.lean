/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ATETiltNuisance
public import Causalean.Estimation.Efficiency.TiltTangent
public import Causalean.Estimation.Efficiency.VonMises

/-!
# Efficient influence function for a treatment-specific mean

For an observed law on `(X,D,Y)`, this module studies the arm functional
`ψ_d(P)=E_P[μ_d(X)]`. It proves its exact doubly robust expansion, an explicit
quadratic remainder along bounded exponential tilts, and the standard efficient
influence function

`1{D=d}(Y-μ_d(X))/e_d(X) + μ_d(X) - ψ_d(P)`.

The average-treatment-effect result is obtained downstream by subtracting the
two arm derivatives. Reference: Kennedy (2024), *Semiparametric doubly robust
targeted double machine learning: a review*.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory Real Topology
open _root_.Causalean.Estimation.ATE.BackdoorEstimationSystem

variable {γ : Type*} [MeasurableSpace γ]

/-- **Exact per-arm expansion along an exponential tilt.** Given [a probability
observed-data law `P`](hyp:P), [an arm `d`](hyp:d), [a measurable score `g` bounded
by `M`](hyp:g,M,hg_meas,hgM), [a nonnegative outcome bound `B`](hyp:B,hB), [a positive
overlap level `ε`](hyp:ε,hε), [bounded outcomes](hyp:hY), and [strict overlap in arm
`d`](hyp:hoverlap), [the arm-mean change minus the tilted mean of its base-law EIF is
exactly minus the product of the propensity and regression changes](goal). -/
theorem observedArmMean_tilt_exact_expansion
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    observedArmMean (tiltMeasure P g t) d - observedArmMean P d -
        ∫ z, observedArmEIF P d z ∂(tiltMeasure P g t) =
      -(∫ z, (observedPropensity (tiltMeasure P g t) d z -
          observedPropensity P d z) / observedPropensity P d z *
        (observedArmRegression (tiltMeasure P g t) d z -
          observedArmRegression P d z) ∂(tiltMeasure P g t)) := by
  let Pt := tiltMeasure P g t
  let _ : IsProbabilityMeasure Pt := isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hYt : ∀ᵐ z ∂Pt, |projY z| ≤ B :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hY
  have hp0P : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap] with z hz
    exact hε.trans_le hz
  have hp0 : ∀ᵐ z ∂Pt, 0 < observedPropensity P d z :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hp0P
  have hpP : ∀ᵐ z ∂P, 0 < observedPropensity Pt d z := by
    dsimp [Pt]
    exact observedPropensity_tilt_pos_ae P g M t d hg_meas hgM hp0P
  have hp : ∀ᵐ z ∂Pt, 0 < observedPropensity Pt d z :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hpP
  have hYint : Integrable (projY : γ × Bool × ℝ → ℝ) Pt :=
    Integrable.of_bound measurable_snd.snd.aestronglyMeasurable B
      (by simpa [Real.norm_eq_abs] using hYt)
  have hμ0 : Integrable (observedArmRegression P d) Pt := by
    apply Integrable.of_bound (measurable_observedArmRegression P d).aestronglyMeasurable B
    exact (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Real.norm_eq_abs] using
        observedArmRegression_abs_le P d B hB hY hp0P)
  have hμ1 : Integrable (observedArmRegression Pt d) Pt :=
    integrable_observedArmRegression_of_bounded Pt d B hB hYt hp
  have hinv : ∀ᵐ z ∂Pt, |(observedPropensity P d z)⁻¹| ≤ ε⁻¹ := by
    have hbase := (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hoverlap
    filter_upwards [hbase] with z hz
    have hpz : 0 < observedPropensity P d z := hε.trans_le hz
    rw [abs_of_pos (inv_pos.mpr hpz)]
    exact (inv_le_inv₀ hpz hε).2 hz
  have hres : Integrable (fun z =>
      observedArmIndicator d z / observedPropensity P d z *
        (projY z - observedArmRegression P d z)) Pt := by
    apply Integrable.of_bound
      (((measurable_observedArmIndicator d).div
        (measurable_observedPropensity P d)).mul
        (measurable_snd.snd.sub (measurable_observedArmRegression P d))).aestronglyMeasurable
      (ε⁻¹ * (B + B))
    have hμb := (ae_tiltMeasure_iff P g M t hg_meas hgM).2
      (observedArmRegression_abs_le P d B hB hY hp0P)
    filter_upwards [hYt, hμb, hinv] with z hYz hμz hinvz
    change |observedArmIndicator d z / observedPropensity P d z *
      (projY z - observedArmRegression P d z)| ≤ ε⁻¹ * (B + B)
    rw [abs_mul, abs_div]
    have hI : |observedArmIndicator d z| ≤ 1 := by
      by_cases hz : projA z = d <;> simp [observedArmIndicator, hz]
    have hfrac : |observedArmIndicator d z| / |observedPropensity P d z| ≤ ε⁻¹ := by
      rw [div_eq_mul_inv, ← abs_inv]
      exact (mul_le_of_le_one_left (abs_nonneg _) hI).trans hinvz
    exact (mul_le_mul hfrac (abs_sub _ _) (abs_nonneg _) (by positivity)).trans (by
      gcongr)
  have hprod : Integrable (fun z =>
      (observedPropensity Pt d z - observedPropensity P d z) /
        observedPropensity P d z *
      (observedArmRegression Pt d z - observedArmRegression P d z)) Pt := by
    have hpI := observedPropensity_mem_Icc_ae Pt d
    have hp0I := (ae_tiltMeasure_iff P g M t hg_meas hgM).2
      (observedPropensity_mem_Icc_ae P d)
    have hμ0b := (ae_tiltMeasure_iff P g M t hg_meas hgM).2
      (observedArmRegression_abs_le P d B hB hY hp0P)
    have hμ1b := observedArmRegression_abs_le Pt d B hB hYt hp
    apply Integrable.of_bound
      ((((measurable_observedPropensity Pt d).sub
        (measurable_observedPropensity P d)).div
        (measurable_observedPropensity P d)).mul
        ((measurable_observedArmRegression Pt d).sub
          (measurable_observedArmRegression P d))).aestronglyMeasurable
      (ε⁻¹ * (2 * (2 * B)))
    filter_upwards [hpI, hp0I, hμ0b, hμ1b, hinv]
      with z hpIz hp0Iz hμ0z hμ1z hinvz
    change |(observedPropensity Pt d z - observedPropensity P d z) /
      observedPropensity P d z *
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
      _ ≤ 2 * ε⁻¹ * (2 * B) := by
        exact mul_le_mul (mul_le_mul hpropdiff hinvz (abs_nonneg _) (by norm_num))
          hμdiff (abs_nonneg _) (by positivity)
      _ = ε⁻¹ * (2 * (2 * B)) := by ring
  simpa only [Pt] using observedArmMean_sub_integral_observedArmEIF_eq_product
    P Pt d ε⁻¹ hYint hμ0 hμ1 hinv hp0 hp hres hprod

/-- Under [a measurable bounded tilt score](hyp:hg_meas,hgM), [nonnegative score and
outcome bounds](hyp:hM,hB), [a positive overlap level](hyp:hε), [bounded outcomes](hyp:hY),
[strict arm overlap](hyp:hoverlap), and [the local condition `|t|M ≤ 1`](hyp:ht),
[the treatment-specific-mean von Mises remainder is bounded by the product of the two
first-order nuisance bounds](goal). -/
theorem observedArmMean_tilt_remainder_bound
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z)
    (ht : |t| * M ≤ 1) :
    |observedArmMean (tiltMeasure P g t) d - observedArmMean P d -
        ∫ z, observedArmEIF P d z ∂(tiltMeasure P g t)| ≤
      ε⁻¹ * (4 * (|t| * M) / Real.exp (-|t| * M)) *
        (4 * B * (|t| * M) / Real.exp (-|t| * M)) := by
  let Pt := tiltMeasure P g t
  let Cp := 4 * (|t| * M) / Real.exp (-|t| * M)
  let Cμ := 4 * B * (|t| * M) / Real.exp (-|t| * M)
  let K := ε⁻¹ * Cp * Cμ
  let _ : IsProbabilityMeasure Pt := isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hp0P : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap] with z hz
    exact hε.trans_le hz
  have hinv : ∀ᵐ z ∂Pt, |(observedPropensity P d z)⁻¹| ≤ ε⁻¹ := by
    have hb := (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hoverlap
    filter_upwards [hb] with z hz
    have hpz := hε.trans_le hz
    rw [abs_of_pos (inv_pos.mpr hpz)]
    exact (inv_le_inv₀ hpz hε).2 hz
  have hpropP := observedPropensity_tilt_firstOrder P g M t d hg_meas hgM hM ht
  have hprop : ∀ᵐ z ∂Pt,
      |observedPropensity Pt d z - observedPropensity P d z| ≤ Cp :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Pt, Cp] using hpropP)
  have hμP := observedArmRegression_tilt_firstOrder P g M B t d
    hg_meas hgM hM hB hY hp0P ht
  have hμ : ∀ᵐ z ∂Pt,
      |observedArmRegression Pt d z - observedArmRegression P d z| ≤ Cμ :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 (by
      simpa [Pt, Cμ] using hμP)
  have hpoint : ∀ᵐ z ∂Pt,
      ‖(observedPropensity Pt d z - observedPropensity P d z) /
          observedPropensity P d z *
        (observedArmRegression Pt d z - observedArmRegression P d z)‖ ≤ K := by
    filter_upwards [hprop, hμ, hinv] with z hpz hμz hinvz
    rw [Real.norm_eq_abs, abs_mul, abs_div, div_eq_mul_inv, ← abs_inv]
    have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
    have hCμ : 0 ≤ Cμ := by dsimp [Cμ]; positivity
    have hfirst := mul_le_mul hpz hinvz (abs_nonneg _) hCp
    exact (mul_le_mul hfirst hμz (abs_nonneg _)
      (mul_nonneg hCp (inv_nonneg.mpr hε.le))).trans_eq (by dsimp [K]; ring)
  have hexact := observedArmMean_tilt_exact_expansion P d g M B ε t
    hg_meas hgM hB hε hY hoverlap
  rw [hexact, abs_neg]
  simpa [K, Cp, Cμ] using norm_integral_le_of_norm_le_const hpoint

/-- Under [a measurable bounded tilt score](hyp:hg_meas,hgM), [nonnegative score and
outcome bounds](hyp:hM,hB), [a positive overlap level](hyp:hε), [bounded outcomes](hyp:hY),
[strict arm overlap](hyp:hoverlap), and [the local condition `|t|M ≤ 1`](hyp:ht),
[the treatment-specific-mean remainder is bounded by an explicit constant times `t²`](goal). -/
theorem observedArmMean_tilt_remainder_quadratic
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (g : γ × Bool × ℝ → ℝ) (M B ε t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z)
    (ht : |t| * M ≤ 1) :
    |observedArmMean (tiltMeasure P g t) d - observedArmMean P d -
        ∫ z, observedArmEIF P d z ∂(tiltMeasure P g t)| ≤
      (16 * ε⁻¹ * B * M ^ 2 * Real.exp 2) * t ^ 2 := by
  have hraw := observedArmMean_tilt_remainder_bound P d g M B ε t
    hg_meas hgM hM hB hε hY hoverlap ht
  let x := |t| * M
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
    _ ≤ ε⁻¹ * (4 * x / Real.exp (-x)) *
        (4 * B * x / Real.exp (-x)) := by simpa [x] using hraw
    _ ≤ ε⁻¹ * (4 * x * Real.exp 1) * (4 * B * x * Real.exp 1) := by gcongr
    _ = (16 * ε⁻¹ * B * M ^ 2 * Real.exp 2) * t ^ 2 := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by
        simpa only [one_add_one_eq_two] using Real.exp_add 1 1]
      dsimp [x]
      ring_nf
      rw [sq_abs]
      ring

/-- Given [a probability observed-data law `P`](hyp:P), [an arm `d`](hyp:d),
[a nonnegative outcome bound `B`](hyp:B,hB), [bounded outcomes](hyp:hY), and
[positive arm propensity](hyp:hp), [the absolute arm mean is at most `B`](goal). -/
theorem observedArmMean_abs_le
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (B : ℝ) (hB : 0 ≤ B)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hp : ∀ᵐ z ∂P, 0 < observedPropensity P d z) :
    |observedArmMean P d| ≤ B := by
  rw [observedArmMean]
  have hb : ∀ᵐ z ∂P, ‖observedArmRegression P d z‖ ≤ B := by
    simpa [Real.norm_eq_abs] using
      observedArmRegression_abs_le P d B hB hY hp
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb

/-- Given [a probability observed-data law `P`](hyp:P), [an arm `d`](hyp:d),
[a nonnegative outcome bound `B`](hyp:B,hB), [a positive overlap level
`ε`](hyp:ε,hε), [bounded outcomes](hyp:hY), and [strict arm overlap](hyp:hoverlap),
[the treatment-specific-mean influence function belongs to L²(P)](goal). -/
theorem memLp_observedArmEIF
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    MemLp (observedArmEIF P d) 2 P := by
  have hp : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap] with z hz
    exact hε.trans_le hz
  have hμ := observedArmRegression_abs_le P d B hB hY hp
  have hψ := observedArmMean_abs_le P d B hB hY hp
  apply MemLp.of_bound
    (((measurable_observedArmIndicator d).div
      (measurable_observedPropensity P d) |>.mul
      (measurable_snd.snd.sub (measurable_observedArmRegression P d)) |>.add
      (measurable_observedArmRegression P d) |>.sub measurable_const).aestronglyMeasurable)
    (ε⁻¹ * (B + B) + B + B)
  filter_upwards [hY, hμ, hoverlap] with z hYz hμz hez
  rw [Real.norm_eq_abs]
  change |observedArmIndicator d z / observedPropensity P d z *
      (projY z - observedArmRegression P d z) +
      observedArmRegression P d z - observedArmMean P d| ≤
    ε⁻¹ * (B + B) + B + B
  have hpz : 0 < observedPropensity P d z := hε.trans_le hez
  have hinv : |(observedPropensity P d z)⁻¹| ≤ ε⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hpz)]
    exact (inv_le_inv₀ hpz hε).2 hez
  have hI : |observedArmIndicator d z| ≤ 1 := by
    by_cases hz : projA z = d <;> simp [observedArmIndicator, hz]
  have hfrac : |observedArmIndicator d z / observedPropensity P d z| ≤ ε⁻¹ := by
    rw [div_eq_mul_inv, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hI).trans hinv
  have hdiff : |projY z - observedArmRegression P d z| ≤ B + B :=
    (abs_sub _ _).trans (by linarith)
  have hres : |observedArmIndicator d z / observedPropensity P d z *
      (projY z - observedArmRegression P d z)| ≤ ε⁻¹ * (B + B) := by
    rw [abs_mul]
    exact mul_le_mul hfrac hdiff (abs_nonneg _) (by positivity)
  have hcenter : |observedArmRegression P d z - observedArmMean P d| ≤ B + B :=
    (abs_sub _ _).trans (by linarith)
  calc
    _ = |observedArmIndicator d z / observedPropensity P d z *
          (projY z - observedArmRegression P d z) +
          (observedArmRegression P d z - observedArmMean P d)| := by ring_nf
    _ ≤ |observedArmIndicator d z / observedPropensity P d z *
          (projY z - observedArmRegression P d z)| +
          |observedArmRegression P d z - observedArmMean P d| := abs_add_le _ _
    _ ≤ ε⁻¹ * (B + B) + (B + B) := add_le_add hres hcenter
    _ = ε⁻¹ * (B + B) + B + B := by ring

/-- Given [a probability observed-data law `P`](hyp:P), [an arm `d`](hyp:d),
[a nonnegative outcome bound `B`](hyp:B,hB), [a positive overlap level
`ε`](hyp:ε,hε), [bounded outcomes](hyp:hY), and [strict arm overlap](hyp:hoverlap),
[the treatment-specific-mean influence function has mean zero](goal). -/
theorem integral_observedArmEIF_eq_zero
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    ∫ z, observedArmEIF P d z ∂P = 0 := by
  have h := observedArmMean_tilt_exact_expansion P d (fun _ => 0) 0 B ε 0
    measurable_const (fun _ => by simp) hB hε hY hoverlap
  simpa [tiltMeasure_zero] using h

/-- Given [a probability observed-data law `P`](hyp:P), [an arm `d`](hyp:d),
[a measurable score `g` bounded by a nonnegative constant `M`](hyp:g,M,hg_meas,hgM,hM),
[a nonnegative outcome bound `B`](hyp:B,hB), [a positive overlap level
`ε`](hyp:ε,hε), [bounded outcomes](hyp:hY), [strict arm overlap](hyp:hoverlap), and
[a mean-zero score](hyp:hg_mean), [the arm mean along its exponential tilt has
derivative equal to the covariance with the arm EIF](goal). -/
theorem hasDerivAt_observedArmMean_tilt
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (g : γ × Bool × ℝ → ℝ) (M B ε : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hg_mean : ∫ z, g z ∂P = 0)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    HasDerivAt (fun t => observedArmMean (tiltMeasure P g t) d)
      (∫ z, observedArmEIF P d z * g z ∂P) 0 := by
  have hφ := memLp_observedArmEIF P d B ε hB hε hY hoverlap
  have hφ_mean := integral_observedArmEIF_eq_zero P d B ε hB hε hY hoverlap
  let C : ℝ := 16 * ε⁻¹ * B * M ^ 2 * Real.exp 2
  apply hasDerivAt_tilt_of_quadratic_vonMises_remainder P
    (fun Q => observedArmMean Q d) (observedArmEIF P d) g M C
    hφ hg_meas hgM hg_mean
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * M ≤ 1 := by
    rcases hM.eq_or_lt with rfl | hMpos
    · simp
    · apply Metric.eventually_nhds_iff.mpr
      refine ⟨M⁻¹, inv_pos.mpr hMpos, ?_⟩
      intro t ht
      rw [Real.dist_eq, sub_zero] at ht
      exact le_of_lt <| calc
        |t| * M < M⁻¹ * M := mul_lt_mul_of_pos_right ht hMpos
        _ = 1 := inv_mul_cancel₀ hMpos.ne'
  filter_upwards [ht] with t ht
  simpa [C, hφ_mean] using observedArmMean_tilt_remainder_quadratic
    P d g M B ε t hg_meas hgM hM hB hε hY hoverlap ht

/-- **Treatment-specific-mean bounded-tilt EIF (Kennedy (2024)).** Given [a probability
observed-data law `P`](hyp:P), [an arm `d`](hyp:d), [a nonnegative outcome bound
`B`](hyp:B,hB), [a positive overlap level `ε`](hyp:ε,hε), [bounded
outcomes](hyp:hY), and [strict arm overlap](hyp:hoverlap), [the usual inverse-
propensity residual plus centered arm regression is efficient for the arm mean
relative to the bounded-tilt submodel class](goal), whose tangent space is the
full nonparametric L²₀(P) space. -/
theorem observedArmEIF_isEfficientInfluenceFunction
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (d : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    IsEfficientInfluenceFunction P (fun Q => observedArmMean Q d)
      ((memLp_observedArmEIF P d B ε hB hε hY hoverlap).toLp
        (observedArmEIF P d)) (boundedTiltSubmodels P) := by
  let hφ := memLp_observedArmEIF P d B ε hB hε hY hoverlap
  apply isEfficientInfluenceFunction_of_hasDerivAt_tilt' P
    (fun Q => observedArmMean Q d) (observedArmEIF P d) hφ
    (integral_observedArmEIF_eq_zero P d B ε hB hε hY hoverlap)
  intro g M hg_meas hgM hg_mean
  exact hasDerivAt_observedArmMean_tilt P d g |M| B ε hg_meas
    (fun z => (hgM z).trans (le_abs_self M)) hg_mean
    (abs_nonneg M) hB hε hY hoverlap

/-- Given [a probability observed-data law `P`](hyp:P), [a nonnegative outcome
bound `B`](hyp:B,hB), [a positive overlap level `ε`](hyp:ε,hε), [bounded
outcomes](hyp:hY), and [strict overlap in both arms](hyp:hoverlap), [the observed-
law AIPW influence function belongs to L²(P)](goal). -/
theorem memLp_observedAIPW
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    MemLp (observedAIPW P) 2 P := by
  have hp (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap d] with z hz
    exact hε.trans_le hz
  have hμ (d : Bool) : Integrable (observedArmRegression P d) P :=
    integrable_observedArmRegression_of_bounded P d B hB hY (hp d)
  have hsub := (memLp_observedArmEIF P true B ε hB hε hY (hoverlap true)).sub
    (memLp_observedArmEIF P false B ε hB hε hY (hoverlap false))
  exact (memLp_congr_ae (ae_of_all P fun z =>
    observedAIPW_eq_armEIF_sub P hμ z)).2 hsub

/-- Given [a probability observed-data law `P`](hyp:P), [a nonnegative outcome
bound `B`](hyp:B,hB), [a positive overlap level `ε`](hyp:ε,hε), [bounded
outcomes](hyp:hY), and [strict overlap in both arms](hyp:hoverlap), [the observed-
law AIPW influence function has mean zero](goal). -/
theorem integral_observedAIPW_eq_zero
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    ∫ z, observedAIPW P z ∂P = 0 := by
  have hp (d : Bool) : ∀ᵐ z ∂P, 0 < observedPropensity P d z := by
    filter_upwards [hoverlap d] with z hz
    exact hε.trans_le hz
  have hμ (d : Bool) : Integrable (observedArmRegression P d) P :=
    integrable_observedArmRegression_of_bounded P d B hB hY (hp d)
  have htrue := integral_observedArmEIF_eq_zero P true B ε
    hB hε hY (hoverlap true)
  have hfalse := integral_observedArmEIF_eq_zero P false B ε
    hB hε hY (hoverlap false)
  have hint (d : Bool) :=
    (memLp_observedArmEIF P d B ε hB hε hY (hoverlap d)).integrable (by norm_num)
  calc
    _ = ∫ z, observedArmEIF P true z - observedArmEIF P false z ∂P := by
      apply integral_congr_ae
      filter_upwards with z
      rw [observedAIPW_eq_armEIF_sub P hμ]
    _ = (∫ z, observedArmEIF P true z ∂P) -
        ∫ z, observedArmEIF P false z ∂P := integral_sub (hint true) (hint false)
    _ = 0 := by rw [htrue, hfalse, sub_zero]

end Causalean.Estimation.Efficiency

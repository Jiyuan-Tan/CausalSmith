/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ObservedLawExpansion
public import Causalean.Estimation.Efficiency.ExponentialTilt
public import Causalean.Mathlib.MeasureTheory.CondExpWithDensity
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# First-order control of observed-law nuisances along bounded tilts

This module combines the conditional Bayes formula with elementary uniform
bounds for exponential weights.  It identifies the propensity and arm
regressions recomputed from a tilted observed law and bounds their changes by
an explicit multiple of the perturbation size.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory Real
open Causalean.Mathlib.MeasureTheory
open _root_.Causalean.Estimation.ATE.BackdoorEstimationSystem
open scoped ENNReal

variable {Z : Type*} [mZ : MeasurableSpace Z]

/-- If [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm) and
[two integrable functions `f` and `h`](hyp:hf,hh) satisfy [nonnegativity of
`h`](hyp:hhnonneg) and [the pointwise domination `|f| ≤ K h`](hyp:hdom), then
[the conditional expectation of `f` is dominated by `K` times the conditional
expectation of `h`](goal). -/
lemma abs_condExp_le_mul_condExp_of_abs_le
    {m₀ : MeasurableSpace Z} {P : @Measure Z m₀} [IsFiniteMeasure P]
    {m : MeasurableSpace Z} (hm : m ≤ m₀) {f h : Z → ℝ} {K : ℝ}
    (hf : Integrable f P) (hh : Integrable h P)
    (hhnonneg : ∀ᵐ z ∂P, 0 ≤ h z)
    (hdom : ∀ᵐ z ∂P, |f z| ≤ K * h z) :
    ∀ᵐ z ∂P, |P[f | m] z| ≤ K * P[h | m] z := by
  have hnorm := norm_condExp_le (μ := P) (m := m) f
  have hmono : P[fun w => ‖f w‖ | m] ≤ᵐ[P] P[K • h | m] :=
    condExp_mono (m := m) hf.norm (hh.smul K) (by
    filter_upwards [hdom] with z hz
    simpa [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hz)
  have hsmul := condExp_smul (μ := P) K h m
  filter_upwards [hnorm, hmono, hsmul] with z hn hz hs
  rw [show |P[f | m] z| = ‖P[f | m] z‖ by rfl]
  calc
    ‖P[f | m] z‖ ≤ P[fun w => ‖f w‖ | m] z := hn
    _ ≤ P[K • h | m] z := hz
    _ = K * P[h | m] z := by
      simpa [Pi.smul_apply, smul_eq_mul] using hs

/-- A [bounded score `g`](hyp:g,hgM) at a [local perturbation satisfying
`|t|M ≤ 1`](hyp:ht) gives an exponential weight whose [distance from one is at most
`2|t|M`](goal). -/
lemma abs_exp_score_sub_one_le
    (g : Z → ℝ) (M t : ℝ) (hgM : ∀ z, |g z| ≤ M)
    (ht : |t| * M ≤ 1) (z : Z) :
    |Real.exp (t * g z) - 1| ≤ 2 * (|t| * M) := by
  have harg : |t * g z| ≤ |t| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgM z) (abs_nonneg t)
  exact (Real.abs_exp_sub_one_le (harg.trans ht)).trans
    (mul_le_mul_of_nonneg_left harg (by norm_num))

/-- A [bounded score `g`](hyp:g,hgM) gives an exponential weight bounded
[below by `exp(-|t|M)`](goal). -/
lemma exp_neg_abs_mul_le_exp_score
    (g : Z → ℝ) (M t : ℝ) (hgM : ∀ z, |g z| ≤ M) (z : Z) :
    Real.exp (-|t| * M) ≤ Real.exp (t * g z) := by
  apply Real.exp_le_exp.mpr
  calc
    -|t| * M = -(|t| * M) := by ring
    _ ≤ -|t * g z| := neg_le_neg (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgM z) (abs_nonneg t))
    _ ≤ t * g z := neg_abs_le _

/-- Under [a conditioning σ-algebra contained in the ambient σ-algebra](hyp:hm) and
[a bounded exponential tilt](hyp:g,hg_meas,hgM), [the conditional expectation
of an integrable target](hyp:hf) is [the ratio of the base-law conditional expectations
weighted by the unnormalized exponential](goal). -/
lemma condExp_tiltMeasure_ae_eq_div_exp
    (P : Measure Z) [IsProbabilityMeasure P]
    {m : MeasurableSpace Z} (hm : m ≤ mZ)
    (g f : Z → ℝ) (M t : ℝ)
    (hg_meas : @Measurable Z ℝ mZ _ g) (hgM : ∀ z, |g z| ≤ M)
    (hf : Integrable f (@tiltMeasure Z mZ P g t)) :
    @condExp Z ℝ m mZ _ _ (@tiltMeasure Z mZ P g t) f =ᵐ[P]
      fun z => P[fun y => f y * Real.exp (t * g y) | m] z /
        P[fun y => Real.exp (t * g y) | m] z := by
  let c := ∫ y, Real.exp (t * g y) ∂P
  have hc : 0 < c := by
    simpa [c, tiltNorm] using
      (@tiltNorm_pos Z mZ P _ g M t hg_meas hgM)
  have hP : @tiltMeasure Z mZ P g t = P.withDensity (fun z => ENNReal.ofReal
      (Real.exp (t * g z) / c)) := by
    simpa [c] using
      (@tiltMeasure_eq_withDensity_div Z mZ P _ g M t hg_meas hgM)
  have hf' : Integrable f (P.withDensity (fun z => ENNReal.ofReal
      (Real.exp (t * g z) / c))) := by simpa [hP] using hf
  have hbayes := @condExp_expTilt_ae_eq_div Z mZ P _ m hm g f t
    hg_meas ⟨M, hgM⟩ hf'
  have hnum := condExp_smul (μ := P) (c⁻¹)
    (fun y => f y * Real.exp (t * g y)) m
  have hden := condExp_smul (μ := P) (c⁻¹)
    (fun y => Real.exp (t * g y)) m
  rw [hP]
  filter_upwards [hbayes, hnum, hden] with z hb hn hd
  rw [hb]
  change P[fun y => f y * (Real.exp (t * g y) / c) | m] z /
      P[fun y => Real.exp (t * g y) / c | m] z = _
  have hnum_eq : P[fun y => f y * (Real.exp (t * g y) / c) | m] z =
      c⁻¹ * P[fun y => f y * Real.exp (t * g y) | m] z := by
    calc
      _ = P[c⁻¹ • fun y => f y * Real.exp (t * g y) | m] z := by
        congr 2
        funext y
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      _ = (c⁻¹ • P[fun y => f y * Real.exp (t * g y) | m]) z := hn
      _ = _ := by simp only [Pi.smul_apply, smul_eq_mul]
  have hden_eq : P[fun y => Real.exp (t * g y) / c | m] z =
      c⁻¹ * P[fun y => Real.exp (t * g y) | m] z := by
    calc
      _ = P[c⁻¹ • fun y => Real.exp (t * g y) | m] z := by
        congr 2
        funext y
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      _ = (c⁻¹ • P[fun y => Real.exp (t * g y) | m]) z := hd
      _ = _ := by simp only [Pi.smul_apply, smul_eq_mul]
  rw [hnum_eq, hden_eq]
  field_simp

/-- Under [a measurable bounded score](hyp:hg_meas,hgM), a property holds [almost everywhere
under an exponential tilt exactly when it holds almost everywhere under the base probability
law](goal), because the
normalized exponential density is everywhere strictly positive. -/
lemma ae_tiltMeasure_iff
    (P : Measure Z) [IsProbabilityMeasure P] (g : Z → ℝ) (M t : ℝ)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M) {p : Z → Prop} :
    (∀ᵐ z ∂tiltMeasure P g t, p z) ↔ ∀ᵐ z ∂P, p z := by
  rw [tiltMeasure_eq_withDensity_div P g M t hg_meas hgM]
  have hdens_meas : Measurable (fun z => ENNReal.ofReal
      (Real.exp (t * g z) / ∫ y, Real.exp (t * g y) ∂P)) := by
    fun_prop
  rw [ae_withDensity_iff hdens_meas]
  have hc : 0 < ∫ y, Real.exp (t * g y) ∂P := by
    simpa [tiltNorm] using tiltNorm_pos (P := P) (s := g) (t := t) hg_meas hgM
  constructor
  · intro hp
    filter_upwards [hp] with z hz
    exact hz (ENNReal.ofReal_ne_zero_iff.mpr (div_pos (Real.exp_pos _) hc))
  · intro hp
    filter_upwards [hp] with z hz _
    exact hz

/-- If [two numerator-denominator pairs are first-order close](hyp:hAt,hpt), [the base
denominator is positive](hyp:hp), [the retained fraction, envelope constant, and perturbation
size have the required signs](hyp:ha,hK,hδ), [the perturbed denominator retains a fraction
`a` of it](hyp:hpt_lower), and [the base numerator is controlled by the base denominator](hyp:hA),
then [their ratios differ by at most `2 K δ / a`](goal). -/
lemma abs_div_sub_div_le_of_relative_bounds
    {A At p pt K δ a : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hpt_lower : a * p ≤ pt) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hA : |A| ≤ K * p) (hAt : |At - A| ≤ K * δ * p)
    (hpt : |pt - p| ≤ δ * p) :
    |At / pt - A / p| ≤ 2 * K * δ / a := by
  have hpt_pos : 0 < pt := (mul_pos ha hp).trans_le hpt_lower
  have hnum : |At * p - A * pt| ≤ 2 * K * δ * p ^ 2 := by
    calc
      |At * p - A * pt| = |(At - A) * p + A * (p - pt)| := by ring_nf
      _ ≤ |At - A| * |p| + |A| * |p - pt| := by
        simpa only [abs_mul] using
          abs_add_le ((At - A) * p) (A * (p - pt))
      _ ≤ (K * δ * p) * p + (K * p) * (δ * p) := by
        rw [abs_of_pos hp, abs_sub_comm p pt]
        exact add_le_add
          (mul_le_mul_of_nonneg_right hAt hp.le)
          (mul_le_mul hA hpt (abs_nonneg _) (mul_nonneg hK hp.le))
      _ = 2 * K * δ * p ^ 2 := by ring
  rw [div_sub_div At A hpt_pos.ne' hp.ne']
  have hmul : At * p - pt * A = At * p - A * pt := by ring
  rw [hmul, abs_div,
    abs_of_pos (mul_pos hpt_pos hp)]
  apply (div_le_iff₀ (mul_pos hpt_pos hp)).2
  calc
    |At * p - A * pt| ≤ 2 * K * δ * p ^ 2 := hnum
    _ ≤ (2 * K * δ / a) * (pt * p) := by
      have hfac : 0 ≤ 2 * K * δ / a := by positivity
      have := mul_le_mul_of_nonneg_right hpt_lower hp.le
      calc
        2 * K * δ * p ^ 2 = (2 * K * δ / a) * ((a * p) * p) := by
          field_simp
          <;> ring
        _ ≤ (2 * K * δ / a) * (pt * p) :=
          mul_le_mul_of_nonneg_left this hfac

/-- If [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm), [two
functions are integrable](hyp:hf,hh), [the weight is measurable](hyp:hu_meas), [the envelope
constant and perturbation size are nonnegative](hyp:hK,hδ), [the conditioning function is
nonnegative](hyp:hhnonneg), [a target `f` is dominated by `K h`](hyp:hdom), and [a weight `u`
differs from one by at most `δ`](hyp:hu_bound), then [weighting changes the conditional
expectation of `f` by at most `K δ` times the conditional expectation of `h`](goal). -/
lemma abs_condExp_mul_sub_condExp_le
    {m₀ : MeasurableSpace Z} {P : @Measure Z m₀} [IsFiniteMeasure P]
    {m : MeasurableSpace Z} (hm : m ≤ m₀) {f h u : Z → ℝ} {K δ : ℝ}
    (hf : Integrable f P) (hh : Integrable h P)
    (hu_meas : @Measurable Z ℝ m₀ _ u)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hhnonneg : ∀ᵐ z ∂P, 0 ≤ h z)
    (hdom : ∀ᵐ z ∂P, |f z| ≤ K * h z)
    (hu_bound : ∀ z, |u z - 1| ≤ δ) :
    ∀ᵐ z ∂P, |P[fun y => f y * u y | m] z - P[f | m] z| ≤
      K * δ * P[h | m] z := by
  have hdiff : Integrable (fun z => f z * (u z - 1)) P :=
    hf.mul_bdd (hu_meas.sub measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hu_bound z)
  have hfu : Integrable (fun z => f z * u z) P := by
    refine (hdiff.add hf).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hce_sub := condExp_sub hfu hf m
  have hce_congr : P[(fun z => f z * u z) - f | m] =ᵐ[P]
      P[fun z => f z * (u z - 1) | m] := by
    apply condExp_congr_ae
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  have hdiff_dom : ∀ᵐ z ∂P, |f z * (u z - 1)| ≤ (K * δ) * h z := by
    filter_upwards [hdom, hhnonneg] with z hfz hhz
    rw [abs_mul]
    calc
      |f z| * |u z - 1| ≤ (K * h z) * δ :=
        mul_le_mul hfz (hu_bound z) (abs_nonneg _) (mul_nonneg hK hhz)
      _ = (K * δ) * h z := by ring
  have hbound := abs_condExp_le_mul_condExp_of_abs_le hm hdiff hh hhnonneg hdiff_dom
  filter_upwards [hce_sub, hce_congr, hbound] with z hsub hcongr hboundz
  change P[(fun z => f z * u z) - f | m] z =
    P[fun z => f z * u z | m] z - P[f | m] z at hsub
  rw [← hsub, hcongr]
  exact hboundz

/-- Suppose [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm),
[the numerator and conditioning weight are integrable](hyp:hf,hh), [the envelope constant
and retained fraction have the required signs](hyp:hK,hδ,ha), [a nonnegative conditioning
weight `h`](hyp:hhnonneg) has [positive conditional mean](hyp:hp), [a numerator `f` is
bounded by `K h`](hyp:hdom), and [a measurable perturbation weight `u` within `δ` of one
and at least `a`](hyp:hu_meas,hu_bound,hu_lower). Then [the corresponding conditional ratios differ by at
most `2 K δ / a`](goal). -/
lemma abs_condExp_ratio_mul_sub_le
    {m₀ : MeasurableSpace Z} {P : @Measure Z m₀} [IsFiniteMeasure P]
    {m : MeasurableSpace Z} (hm : m ≤ m₀) {f h u : Z → ℝ} {K δ a : ℝ}
    (hf : Integrable f P) (hh : Integrable h P)
    (hu_meas : @Measurable Z ℝ m₀ _ u)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (ha : 0 < a)
    (hhnonneg : ∀ᵐ z ∂P, 0 ≤ h z)
    (hp : ∀ᵐ z ∂P, 0 < P[h | m] z)
    (hdom : ∀ᵐ z ∂P, |f z| ≤ K * h z)
    (hu_bound : ∀ z, |u z - 1| ≤ δ) (hu_lower : ∀ z, a ≤ u z) :
    ∀ᵐ z ∂P,
      |P[fun y => f y * u y | m] z / P[fun y => h y * u y | m] z -
        P[f | m] z / P[h | m] z| ≤ 2 * K * δ / a := by
  have hu_norm : ∀ z, |u z| ≤ δ + 1 := by
    intro z
    calc
      |u z| = |(u z - 1) + 1| := by ring_nf
      _ ≤ |u z - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ δ + 1 := by simpa using add_le_add_right (hu_bound z) 1
  have hhu : Integrable (fun z => h z * u z) P :=
    hh.mul_bdd hu_meas.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hu_norm z)
  have hfu : Integrable (fun z => f z * u z) P :=
    hf.mul_bdd hu_meas.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hu_norm z)
  have hAt := abs_condExp_mul_sub_condExp_le hm hf hh hu_meas hK hδ
    hhnonneg hdom hu_bound
  have hhdom : ∀ᵐ z ∂P, |h z| ≤ (1 : ℝ) * h z := by
    filter_upwards [hhnonneg] with z hz
    simp [abs_of_nonneg hz]
  have hpt := abs_condExp_mul_sub_condExp_le hm hh hh hu_meas
    (show 0 ≤ (1 : ℝ) by norm_num) hδ hhnonneg hhdom hu_bound
  have hA := abs_condExp_le_mul_condExp_of_abs_le hm hf hh hhnonneg hdom
  have hlower_raw : P[a • h | m] ≤ᵐ[P] P[fun z => h z * u z | m] :=
    condExp_mono (hh.smul a) hhu (by
      filter_upwards [hhnonneg] with z hz
      simp only [Pi.smul_apply, smul_eq_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hu_lower z) hz)
  have hsmul := condExp_smul (μ := P) a h m
  filter_upwards [hp, hAt, hpt, hA, hlower_raw, hsmul]
    with z hpz hAtz hptz hAz hlowerz hsmulz
  have hlower : a * P[h | m] z ≤ P[fun y => h y * u y | m] z := by
    calc
      a * P[h | m] z = (a • P[h | m]) z := by
        simp only [Pi.smul_apply, smul_eq_mul]
      _ = P[a • h | m] z := hsmulz.symm
      _ ≤ P[fun y => h y * u y | m] z := hlowerz
  apply abs_div_sub_div_le_of_relative_bounds hpz ha hlower hK hδ hAz hAtz
  simpa using hptz

section ObservedLaw

variable {γ : Type*} [MeasurableSpace γ]

/-- For [a probability law `P`](hyp:P) and [a bounded measurable tilt score
`g`](hyp:g,hg_meas,hgM), [the propensity recomputed under the tilted law is the
conditional ratio of unnormalized exponentially weighted arm indicators](goal). -/
lemma observedPropensity_tilt_ae_eq_expRatio
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M t : ℝ) (d : Bool)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M) :
    observedPropensity (tiltMeasure P g t) d =ᵐ[P] fun z =>
      P[fun y => observedArmIndicator d y * Real.exp (t * g y) |
        observedCovariateSigma] z /
      P[fun y => Real.exp (t * g y) | observedCovariateSigma] z := by
  let _ : IsProbabilityMeasure (tiltMeasure P g t) :=
    isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hi : Integrable (observedArmIndicator d) (tiltMeasure P g t) :=
    integrable_observedArmIndicator _ d
  simpa only [observedPropensity] using
    condExp_tiltMeasure_ae_eq_div_exp P observedCovariateSigma_le g
      (observedArmIndicator d) M t hg_meas hgM hi

/-- If [the observed outcome is bounded by `B`](hyp:hY), then under [a bounded
measurable tilt](hyp:g,hg_meas,hgM), [the arm regression recomputed under the tilted
law is the ratio of the unnormalized weighted outcome-arm and arm conditional
expectations](goal). -/
lemma observedArmRegression_tilt_ae_eq_expRatio
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B t : ℝ) (d : Bool)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B) :
    observedArmRegression (tiltMeasure P g t) d =ᵐ[P] fun z =>
      P[fun y => projY y * observedArmIndicator d y * Real.exp (t * g y) |
        observedCovariateSigma] z /
      P[fun y => observedArmIndicator d y * Real.exp (t * g y) |
        observedCovariateSigma] z := by
  let _ : IsProbabilityMeasure (tiltMeasure P g t) :=
    isProbabilityMeasure_tiltMeasure hg_meas hgM
  have hi : Integrable (observedArmIndicator d) (tiltMeasure P g t) :=
    integrable_observedArmIndicator _ d
  have hYt : ∀ᵐ z ∂tiltMeasure P g t, |projY z| ≤ B :=
    (ae_tiltMeasure_iff P g M t hg_meas hgM).2 hY
  have hyi : Integrable (fun z => projY z * observedArmIndicator d z)
      (tiltMeasure P g t) := by
    apply Integrable.of_bound
      ((measurable_snd.snd.mul (measurable_observedArmIndicator d)).aestronglyMeasurable) B
    filter_upwards [hYt] with z hYz
    change |projY z * observedArmIndicator d z| ≤ B
    rw [abs_mul]
    by_cases hz : projA z = d
    · simpa [observedArmIndicator, hz] using hYz
    · have hB : 0 ≤ B := (abs_nonneg (projY z)).trans hYz
      simpa [observedArmIndicator, hz] using hB
  have hi_bayes := condExp_tiltMeasure_ae_eq_div_exp P observedCovariateSigma_le g
    (observedArmIndicator d) M t hg_meas hgM hi
  have hyi_bayes := condExp_tiltMeasure_ae_eq_div_exp P observedCovariateSigma_le g
    (fun z => projY z * observedArmIndicator d z) M t hg_meas hgM hyi
  let u : γ × Bool × ℝ → ℝ := fun z => Real.exp (t * g z)
  have hu_int : Integrable u P := tilt_exp_integrable hg_meas hgM
  have hlower : ∀ z, Real.exp (-|t| * M) ≤ u z :=
    exp_neg_abs_mul_le_exp_score g M t hgM
  have hce_lower : (fun _ => Real.exp (-|t| * M)) ≤ᵐ[P]
      P[u | observedCovariateSigma] := by
    have hmono := condExp_mono (m := observedCovariateSigma)
      (integrable_const (Real.exp (-|t| * M))) hu_int (Eventually.of_forall hlower)
    simpa [condExp_const observedCovariateSigma_le] using hmono
  filter_upwards [hi_bayes, hyi_bayes, hce_lower] with z hi_z hyi_z hlower_z
  change (tiltMeasure P g t)[fun w => projY w * observedArmIndicator d w |
      observedCovariateSigma] z /
    (tiltMeasure P g t)[observedArmIndicator d | observedCovariateSigma] z = _
  rw [hi_z, hyi_z]
  change ((P[fun y => projY y * observedArmIndicator d y * u y |
      observedCovariateSigma] z / P[u | observedCovariateSigma] z) /
    (P[fun y => observedArmIndicator d y * u y | observedCovariateSigma] z /
      P[u | observedCovariateSigma] z)) = _
  have hden : P[u | observedCovariateSigma] z ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans_le hlower_z)
  field_simp
  simp only [u]

/-- Along [a bounded measurable exponential tilt](hyp:g,hg_meas,hgM) with [a nonnegative
bound and local perturbation](hyp:hM,ht), [the recomputed arm propensity changes by at most a constant times
`|t|M`](goal).  This is the first-order propensity control used in the ATE
remainder. -/
theorem observedPropensity_tilt_firstOrder
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M t : ℝ) (d : Bool)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M) (hM : 0 ≤ M)
    (ht : |t| * M ≤ 1) :
    ∀ᵐ z ∂P, |observedPropensity (tiltMeasure P g t) d z -
      observedPropensity P d z| ≤
        4 * (|t| * M) / Real.exp (-|t| * M) := by
  let u : γ × Bool × ℝ → ℝ := fun z => Real.exp (t * g z)
  let δ := 2 * (|t| * M)
  let a := Real.exp (-|t| * M)
  have hδ : 0 ≤ δ := by positivity
  have ha : 0 < a := Real.exp_pos _
  have hi := integrable_observedArmIndicator P d
  have hone : Integrable (fun _ : γ × Bool × ℝ => (1 : ℝ)) P := integrable_const _
  have hratio := abs_condExp_ratio_mul_sub_le observedCovariateSigma_le
    hi hone (hg_meas.const_mul t).exp (show 0 ≤ (1 : ℝ) by norm_num) hδ ha
    (Eventually.of_forall fun _ => zero_le_one)
    (Eventually.of_forall fun z => by
      simp [condExp_const observedCovariateSigma_le])
    (Eventually.of_forall fun z => by
      by_cases hz : projA z = d <;> simp [observedArmIndicator, hz])
    (fun z => by simpa [u, δ] using abs_exp_score_sub_one_le g M t hgM ht z)
    (fun z => by simpa [u, a] using exp_neg_abs_mul_le_exp_score g M t hgM z)
  have hbayes := observedPropensity_tilt_ae_eq_expRatio P g M t d hg_meas hgM
  filter_upwards [hratio, hbayes] with z hz hbayes_z
  rw [hbayes_z]
  simp only [u, observedPropensity, condExp_const observedCovariateSigma_le] at hz ⊢
  convert hz using 1 <;> ring

/-- If [the base arm propensity is positive](hyp:hp) and [the tilt score is measurable and
bounded](hyp:hg_meas,hgM), then [the arm propensity recomputed under that exponential tilt
remains positive](goal). -/
theorem observedPropensity_tilt_pos_ae
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M t : ℝ) (d : Bool)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hp : ∀ᵐ z ∂P, 0 < observedPropensity P d z) :
    ∀ᵐ z ∂P, 0 < observedPropensity (tiltMeasure P g t) d z := by
  let u : γ × Bool × ℝ → ℝ := fun z => Real.exp (t * g z)
  let a := Real.exp (-|t| * M)
  have ha : 0 < a := Real.exp_pos _
  have hu : Integrable u P := tilt_exp_integrable hg_meas hgM
  have hI : Integrable (observedArmIndicator d) P :=
    integrable_observedArmIndicator P d
  have hIu : Integrable (fun z => observedArmIndicator d z * u z) P := by
    apply hI.mul_bdd (by dsimp [u]; fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgM z) (abs_nonneg t)))
  have hden_lower : (fun _ => a) ≤ᵐ[P] P[u | observedCovariateSigma] := by
    have hmono := condExp_mono (m := observedCovariateSigma) (integrable_const a) hu
      (Eventually.of_forall fun z => by
        simpa [u, a] using exp_neg_abs_mul_le_exp_score g M t hgM z)
    simpa [condExp_const observedCovariateSigma_le] using hmono
  have hnum_lower : (fun z => a * observedPropensity P d z) ≤ᵐ[P]
      P[fun z => observedArmIndicator d z * u z | observedCovariateSigma] := by
    have hmono := condExp_mono (m := observedCovariateSigma) (hI.smul a) hIu (by
      filter_upwards with z
      simp only [Pi.smul_apply, smul_eq_mul]
      have hl := exp_neg_abs_mul_le_exp_score g M t hgM z
      have hInonneg : 0 ≤ observedArmIndicator d z := by
        by_cases hz : projA z = d <;> simp [observedArmIndicator, hz]
      simpa [u, a, mul_comm] using mul_le_mul_of_nonneg_left hl hInonneg)
    have hsmul := condExp_smul (μ := P) a (observedArmIndicator d)
      observedCovariateSigma
    filter_upwards [hmono, hsmul] with z hz hs
    simpa [observedPropensity, Pi.smul_apply, smul_eq_mul] using hs.symm.le.trans hz
  have hbayes := observedPropensity_tilt_ae_eq_expRatio P g M t d hg_meas hgM
  filter_upwards [hp, hden_lower, hnum_lower, hbayes]
    with z hpz hdenz hnumz hbayesz
  rw [hbayesz]
  exact div_pos ((mul_pos ha hpz).trans_le hnumz) (ha.trans_le hdenz)

/-- If [the outcome bound and tilt bound are nonnegative](hyp:hB,hM), [the outcome is
bounded](hyp:hY), and [the base arm propensity is strictly positive](hyp:hp), then along
[a bounded measurable exponential tilt](hyp:g,hg_meas,hgM) with [a local perturbation](hyp:ht),
[the recomputed arm regression changes by at most a constant times
`|t|M`](goal). -/
theorem observedArmRegression_tilt_firstOrder
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (g : γ × Bool × ℝ → ℝ) (M B t : ℝ) (d : Bool)
    (hg_meas : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hp : ∀ᵐ z ∂P, 0 < observedPropensity P d z)
    (ht : |t| * M ≤ 1) :
    ∀ᵐ z ∂P, |observedArmRegression (tiltMeasure P g t) d z -
      observedArmRegression P d z| ≤
        4 * B * (|t| * M) / Real.exp (-|t| * M) := by
  let u : γ × Bool × ℝ → ℝ := fun z => Real.exp (t * g z)
  let δ := 2 * (|t| * M)
  let a := Real.exp (-|t| * M)
  let I : γ × Bool × ℝ → ℝ := observedArmIndicator d
  let f : γ × Bool × ℝ → ℝ := fun z => projY z * I z
  have hδ : 0 ≤ δ := by positivity
  have ha : 0 < a := Real.exp_pos _
  have hI : Integrable I P := integrable_observedArmIndicator P d
  have hf : Integrable f P := by
    apply Integrable.of_bound
      ((measurable_snd.snd.mul (measurable_observedArmIndicator d)).aestronglyMeasurable) B
    filter_upwards [hY] with z hYz
    dsimp [f, I]
    change |projY z * observedArmIndicator d z| ≤ B
    rw [abs_mul]
    by_cases hz : projA z = d
    · simpa [observedArmIndicator, hz] using hYz
    · simpa [observedArmIndicator, hz] using hB
  have hdom : ∀ᵐ z ∂P, |f z| ≤ B * I z := by
    filter_upwards [hY] with z hYz
    dsimp [f, I]
    rw [abs_mul]
    by_cases hz : projA z = d
    · simpa [observedArmIndicator, hz] using hYz
    · simp [observedArmIndicator, hz, hB]
  have hratio := abs_condExp_ratio_mul_sub_le observedCovariateSigma_le
    hf hI (hg_meas.const_mul t).exp hB hδ ha
    (Eventually.of_forall fun z => by
      dsimp [I]
      by_cases hz : projA z = d <;> simp [observedArmIndicator, hz])
    (by simpa [I, observedPropensity] using hp) hdom
    (fun z => by simpa [u, δ] using abs_exp_score_sub_one_le g M t hgM ht z)
    (fun z => by simpa [u, a] using exp_neg_abs_mul_le_exp_score g M t hgM z)
  have hbayes := observedArmRegression_tilt_ae_eq_expRatio P g M B t d
    hg_meas hgM hY
  filter_upwards [hratio, hbayes] with z hz hbayes_z
  rw [hbayes_z]
  simp only [f, I, u, observedArmRegression, observedArmNumerator,
    observedPropensity] at hz ⊢
  convert hz using 1 <;> ring

/-- If [the outcome bound is nonnegative](hyp:hB), [the outcome is bounded by
`B`](hyp:hY), and [an arm propensity is positive](hyp:hp), then [the observed
arm regression is bounded by `B`](goal). -/
lemma observedArmRegression_abs_le
    (Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q] (d : Bool) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ᵐ z ∂Q, |projY z| ≤ B)
    (hp : ∀ᵐ z ∂Q, 0 < observedPropensity Q d z) :
    ∀ᵐ z ∂Q, |observedArmRegression Q d z| ≤ B := by
  have hI : Integrable (observedArmIndicator d) Q :=
    integrable_observedArmIndicator Q d
  have hYI : Integrable (fun z => projY z * observedArmIndicator d z) Q := by
    apply Integrable.of_bound
      ((measurable_snd.snd.mul (measurable_observedArmIndicator d)).aestronglyMeasurable) B
    filter_upwards [hY] with z hYz
    change |projY z * observedArmIndicator d z| ≤ B
    rw [abs_mul]
    by_cases hz : projA z = d
    · simpa [observedArmIndicator, hz] using hYz
    · simpa [observedArmIndicator, hz] using hB
  have hdom : ∀ᵐ z ∂Q,
      |projY z * observedArmIndicator d z| ≤ B * observedArmIndicator d z := by
    filter_upwards [hY] with z hYz
    rw [abs_mul]
    by_cases hz : projA z = d
    · simpa [observedArmIndicator, hz] using hYz
    · simp [observedArmIndicator, hz]
  have hnum := abs_condExp_le_mul_condExp_of_abs_le observedCovariateSigma_le
    hYI hI (Eventually.of_forall fun z => by
      by_cases hz : projA z = d <;> simp [observedArmIndicator, hz]) hdom
  filter_upwards [hnum, hp] with z hnumz hpz
  change 0 < Q[observedArmIndicator d | observedCovariateSigma] z at hpz
  rw [observedArmRegression, observedArmNumerator, observedPropensity, abs_div,
    abs_of_pos hpz]
  exact (div_le_iff₀ hpz).2 hnumz

/-- Under [a nonnegative outcome bound](hyp:hB), [bounded outcomes](hyp:hY), and
[a positive arm propensity](hyp:hp), [the corresponding observed arm regression
is integrable](goal). -/
lemma integrable_observedArmRegression_of_bounded
    (Q : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure Q] (d : Bool) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ᵐ z ∂Q, |projY z| ≤ B)
    (hp : ∀ᵐ z ∂Q, 0 < observedPropensity Q d z) :
    Integrable (observedArmRegression Q d) Q :=
  Integrable.of_bound (measurable_observedArmRegression Q d).aestronglyMeasurable B
    (by simpa [Real.norm_eq_abs] using
      observedArmRegression_abs_le Q d B hB hY hp)

end ObservedLaw

end Causalean.Estimation.Efficiency

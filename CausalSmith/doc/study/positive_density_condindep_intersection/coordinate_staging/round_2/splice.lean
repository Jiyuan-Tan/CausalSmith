/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Basic

/-!
# Splicing positive density factorizations

This module isolates the analytic heart of graphoid intersection.  Strict positivity on a product
support lets two factorizations with different conditioning blocks be compared along product
fibres and spliced into the factorization for the union block.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.CondIndep.PositiveDensityIntersection

universe uX uY uV uZ

private theorem factors_pos_lt_top {a b d : ℝ≥0∞} (h : d = a * b)
    (hp : 0 < d) (hf : d < ∞) : 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ := by
  subst d
  have hp' := ENNReal.mul_pos_iff.mp hp
  rcases ENNReal.mul_lt_top_iff.mp hf with hf' | ha | hb
  · exact ⟨hp'.1, hf'.1, hp'.2, hf'.2⟩
  · exact (hp'.1.ne' ha).elim
  · exact (hp'.2.ne' hb).elim

private theorem div_eq_div_of_mul_eq_mul
    {a c A C b e : ℝ≥0∞}
    (h : a * b = c * e) (hI : A * b = C * e)
    (hA0 : A ≠ 0) (hAt : A ≠ ∞) (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (he0 : e ≠ 0) (het : e ≠ ∞) : a / A = c / C := by
  apply (ENNReal.div_eq_div_iff hC0 hCt hA0 hAt).2
  apply (ENNReal.mul_left_inj he0 het).mp
  calc
    C * a * e = a * (C * e) := by ac_rfl
    _ = a * (A * b) := by rw [hI]
    _ = A * (a * b) := by ac_rfl
    _ = A * (c * e) := by rw [h]
    _ = A * c * e := by ac_rfl

private theorem commonFactor_of_ae_eq
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    (muX : Measure X) (muY : Measure Y) (muV : Measure V) (muZ : Measure Z)
    [SigmaFinite muX] [SigmaFinite muY] [SigmaFinite muV] [SigmaFinite muZ]
    (hmuV : muV ≠ 0)
    {p : X × (V × Z) → ℝ≥0∞} {q : X × (Y × Z) → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q)
    (hpq : ∀ᵐ w ∂muX.prod (muY.prod (muV.prod muZ)),
      p (w.1, (w.2.2.1, w.2.2.2)) = q (w.1, (w.2.1, w.2.2.2))) :
    ∃ r : X × Z → ℝ≥0∞, Measurable r ∧
      ∀ᵐ w ∂muX.prod (muY.prod (muV.prod muZ)),
        p (w.1, (w.2.2.1, w.2.2.2)) = r (w.1, w.2.2.2) := by
  let _ : NeZero muV := ⟨hmuV⟩
  let rhoV := muV.toFinite
  let r : X × Z → ℝ≥0∞ := fun xz ↦ ∫⁻ v, p (xz.1, (v, xz.2)) ∂rhoV
  have hr : Measurable r := by
    apply Measurable.lintegral_prod_right
    fun_prop
  refine ⟨r, hr, ?_⟩
  have hnested : ∀ᵐ x ∂muX, ∀ᵐ y ∂muY, ∀ᵐ v ∂muV, ∀ᵐ z ∂muZ,
      p (x, (v, z)) = r (x, z) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpq] with x hx
    filter_upwards [Measure.ae_ae_of_ae_prod hx] with y hy
    have hy' := Measure.ae_ae_of_ae_prod hy
    have hy_swap : ∀ᵐ z ∂muZ, ∀ᵐ v ∂muV,
        p (x, (v, z)) = q (x, (y, z)) := by
      rw [← Measure.ae_ae_comm]
      · exact hy'
      · exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hrq : ∀ᵐ z ∂muZ, r (x, z) = q (x, (y, z)) := by
      filter_upwards [hy_swap] with z hz
      have hz0 : (fun v ↦ p (x, (v, z))) =ᵐ[muV] (fun _ ↦ q (x, (y, z))) := hz
      have hz' : (fun v ↦ p (x, (v, z))) =ᵐ[rhoV] (fun _ ↦ q (x, (y, z))) := by
        rw [show ae rhoV = ae muV by simp [rhoV]]
        exact hz0
      change (∫⁻ v, p (x, (v, z)) ∂rhoV) = q (x, (y, z))
      rw [lintegral_congr_ae hz']
      simp [rhoV]
    filter_upwards [hy', ae_of_all muV fun _ ↦ hrq] with v hv hz
    filter_upwards [hv, hz] with z hvz hrqz
    exact hvz.trans hrqz.symm
  refine (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2 ?_
  filter_upwards [hnested] with x hx
  refine (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2 ?_
  filter_upwards [hx] with y hy
  exact (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2 hy

/-- [Four sigma-finite reference measures](hyp:μX,μY,μV,μZ), [a measurable density](hyp:hd),
[its strict positivity almost everywhere](hyp:hpos), and [its two changing-conditioning
factorizations](hyp:hXY,hXV) [yield the factorization for the joint second-and-third block
conditioned on the fourth](goal). -/
theorem positiveDensity_factorization_splice
    {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
    {d : FourBlock X Y V Z → ℝ≥0∞}
    (hd : Measurable d)
    [IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d)]
    (hpos : ∀ᵐ q ∂fourBlockReference μX μY μV μZ, 0 < d q)
    (hXY : FactorsXYGivenZV μX μY μV μZ d)
    (hXV : FactorsXVGivenZY μX μY μV μZ d) :
    FactorsXYVGivenZ μX μY μV μZ d := by
  /- Proof plan: finiteness of `withDensity d` and `ae_lt_top` make `d` finite a.e.; positivity
  makes the premise factors nonzero on almost every product fibre.  Use Tonelli/Fubini to obtain
  simultaneous fibrewise versions of both factorizations, cancel along the `Y` and `V` fibres,
  and construct measurable `(X,Z)` and `(Y,V,Z)` factors from fibre integrals. -/
  by_cases hX : μX = 0
  · refine ⟨0, 0, measurable_const, measurable_const, ?_⟩
    rw [show fourBlockReference μX μY μV μZ = 0 by simp [fourBlockReference, hX]]
    rw [ae_zero]
    exact Filter.eventually_bot
  by_cases hY : μY = 0
  · refine ⟨0, 0, measurable_const, measurable_const, ?_⟩
    rw [show fourBlockReference μX μY μV μZ = 0 by simp [fourBlockReference, hY]]
    rw [ae_zero]
    exact Filter.eventually_bot
  by_cases hV : μV = 0
  · refine ⟨0, 0, measurable_const, measurable_const, ?_⟩
    rw [show fourBlockReference μX μY μV μZ = 0 by simp [fourBlockReference, hV]]
    rw [ae_zero]
    exact Filter.eventually_bot
  by_cases hZ : μZ = 0
  · refine ⟨0, 0, measurable_const, measurable_const, ?_⟩
    rw [show fourBlockReference μX μY μV μZ = 0 by simp [fourBlockReference, hZ]]
    rw [ae_zero]
    exact Filter.eventually_bot
  let _ : NeZero μX := ⟨hX⟩
  rcases hXY with ⟨a, b, ha, hb, hab⟩
  rcases hXV with ⟨c, e, hc, he, hce⟩
  let ν := μY.prod (μV.prod μZ)
  let D : Y × (V × Z) → ℝ≥0∞ := fun w ↦ ∫⁻ x, d (x, w) ∂μX
  let A : V × Z → ℝ≥0∞ := fun vz ↦ ∫⁻ x, a (x, vz) ∂μX
  let C : Y × Z → ℝ≥0∞ := fun yz ↦ ∫⁻ x, c (x, yz) ∂μX
  have hD : Measurable D := hd.lintegral_prod_left'
  have hA : Measurable A := ha.lintegral_prod_left'
  have hC : Measurable C := hc.lintegral_prod_left'
  have hdInt : ∫⁻ w, d w ∂fourBlockReference μX μY μV μZ ≠ ∞ := by
    have h := measure_ne_top
      ((fourBlockReference μX μY μV μZ).withDensity d) Set.univ
    simpa [withDensity_apply] using h
  have hdFinite : ∀ᵐ w ∂fourBlockReference μX μY μV μZ, d w < ∞ :=
    ae_lt_top hd hdInt
  have hDInt : ∫⁻ w, D w ∂ν ≠ ∞ := by
    rw [← lintegral_prod_symm d hd.aemeasurable]
    exact hdInt
  have hDFinite : ∀ᵐ w ∂ν, D w < ∞ := ae_lt_top hD hDInt
  have hgood : ∀ᵐ w ∂fourBlockReference μX μY μV μZ,
      0 < d w ∧ d w < ∞ ∧
      d w = a (w.1, (w.2.2.1, w.2.2.2)) * b (w.2.1, (w.2.2.1, w.2.2.2)) ∧
      d w = c (w.1, (w.2.1, w.2.2.2)) * e (w.2.2.1, (w.2.1, w.2.2.2)) := by
    filter_upwards [hpos, hdFinite, hab, hce] with w hp hf habw hcew
    exact ⟨hp, hf, habw, hcew⟩
  have hgoodSwap : ∀ᵐ w ∂ν, ∀ᵐ x ∂μX,
      0 < d (x, w) ∧ d (x, w) < ∞ ∧
      d (x, w) = a (x, (w.2.1, w.2.2)) * b (w.1, (w.2.1, w.2.2)) ∧
      d (x, w) = c (x, (w.1, w.2.2)) * e (w.2.1, (w.1, w.2.2)) := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact Measure.ae_ae_of_ae_prod hgood
  have hrest : ∀ᵐ w ∂ν,
      A (w.2.1, w.2.2) * b (w.1, (w.2.1, w.2.2)) =
          C (w.1, w.2.2) * e (w.2.1, (w.1, w.2.2)) ∧
      0 < A (w.2.1, w.2.2) ∧ A (w.2.1, w.2.2) < ∞ ∧
      0 < C (w.1, w.2.2) ∧ C (w.1, w.2.2) < ∞ := by
    filter_upwards [hDFinite, hgoodSwap] with w hDf hw
    have haSec : Measurable (fun x ↦ a (x, (w.2.1, w.2.2))) := by fun_prop
    have hcSec : Measurable (fun x ↦ c (x, (w.1, w.2.2))) := by fun_prop
    have hDab : D w = A (w.2.1, w.2.2) * b (w.1, (w.2.1, w.2.2)) := by
      change (∫⁻ x, d (x, w) ∂μX) = _
      rw [lintegral_congr_ae (hw.mono fun x hx ↦ hx.2.2.1), lintegral_mul_const]
      exact haSec
    have hDce : D w = C (w.1, w.2.2) * e (w.2.1, (w.1, w.2.2)) := by
      change (∫⁻ x, d (x, w) ∂μX) = _
      rw [lintegral_congr_ae (hw.mono fun x hx ↦ hx.2.2.2), lintegral_mul_const]
      exact hcSec
    have hapos : ∀ᵐ x ∂μX, 0 < a (x, (w.2.1, w.2.2)) :=
      hw.mono fun x hx ↦ (factors_pos_lt_top hx.2.2.1 hx.1 hx.2.1).1
    have hcpos : ∀ᵐ x ∂μX, 0 < c (x, (w.1, w.2.2)) :=
      hw.mono fun x hx ↦ (factors_pos_lt_top hx.2.2.2 hx.1 hx.2.1).1
    have hApos : 0 < A (w.2.1, w.2.2) := by
      change 0 < ∫⁻ x, a (x, (w.2.1, w.2.2)) ∂μX
      simpa using lintegral_strict_mono hX haSec.aemeasurable (by simp) hapos
    have hCpos : 0 < C (w.1, w.2.2) := by
      change 0 < ∫⁻ x, c (x, (w.1, w.2.2)) ∂μX
      simpa using lintegral_strict_mono hX hcSec.aemeasurable (by simp) hcpos
    obtain ⟨x0, hx0⟩ := hw.exists
    have hbf := factors_pos_lt_top hx0.2.2.1 hx0.1 hx0.2.1
    have hef := factors_pos_lt_top hx0.2.2.2 hx0.1 hx0.2.1
    have hbpos : 0 < b (w.1, (w.2.1, w.2.2)) := hbf.2.2.1
    have hepos : 0 < e (w.2.1, (w.1, w.2.2)) := hef.2.2.1
    have hAfin : A (w.2.1, w.2.2) < ∞ := by
      have hmul : A (w.2.1, w.2.2) * b (w.1, (w.2.1, w.2.2)) < ∞ := by
        rwa [← hDab]
      rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
      · exact h.1
      · exact (hApos.ne' h).elim
      · exact (hbpos.ne' h).elim
    have hCfin : C (w.1, w.2.2) < ∞ := by
      have hmul : C (w.1, w.2.2) * e (w.2.1, (w.1, w.2.2)) < ∞ := by
        rwa [← hDce]
      rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
      · exact h.1
      · exact (hCpos.ne' h).elim
      · exact (hepos.ne' h).elim
    exact ⟨hDab.symm.trans hDce, hApos, hAfin, hCpos, hCfin⟩
  let p : X × (V × Z) → ℝ≥0∞ := fun xvz ↦ a xvz / A xvz.2
  let q : X × (Y × Z) → ℝ≥0∞ := fun xyz ↦ c xyz / C xyz.2
  have hp : Measurable p := ha.div (hA.comp measurable_snd)
  have hq : Measurable q := hc.div (hC.comp measurable_snd)
  have hpqRest : ∀ᵐ w ∂ν, ∀ᵐ x ∂μX,
      p (x, (w.2.1, w.2.2)) = q (x, (w.1, w.2.2)) := by
    filter_upwards [hrest, hgoodSwap] with w hr hw
    filter_upwards [hw] with x hx
    have hef := factors_pos_lt_top hx.2.2.2 hx.1 hx.2.1
    exact div_eq_div_of_mul_eq_mul
      (hx.2.2.1.symm.trans hx.2.2.2) hr.1
      hr.2.1.ne' hr.2.2.1.ne hr.2.2.2.1.ne' hr.2.2.2.2.ne
      hef.2.2.1.ne' hef.2.2.2.ne
  have hpqNested : ∀ᵐ x ∂μX, ∀ᵐ w ∂ν,
      p (x, (w.2.1, w.2.2)) = q (x, (w.1, w.2.2)) := by
    apply (Measure.ae_ae_comm (by measurability)).2
    exact hpqRest
  have hpq : ∀ᵐ w ∂μX.prod (μY.prod (μV.prod μZ)),
      p (w.1, (w.2.2.1, w.2.2.2)) = q (w.1, (w.2.1, w.2.2.2)) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    exact hpqNested
  obtain ⟨r, hr, hpr⟩ := commonFactor_of_ae_eq μX μY μV μZ hV hp hq hpq
  let s : (Y × V) × Z → ℝ≥0∞ := fun yvz ↦ A (yvz.1.2, yvz.2) * b (yvz.1.1, (yvz.1.2, yvz.2))
  have hs : Measurable s := by fun_prop
  refine ⟨r, s, hr, hs, ?_⟩
  have hrestNested : ∀ᵐ x ∂μX, ∀ᵐ w ∂ν,
      0 < A (w.2.1, w.2.2) ∧ A (w.2.1, w.2.2) < ∞ :=
    ae_of_all μX fun _ ↦ hrest.mono fun w hw ↦ ⟨hw.2.1, hw.2.2.1⟩
  have hrestFull : ∀ᵐ w ∂fourBlockReference μX μY μV μZ,
      0 < A (w.2.2.1, w.2.2.2) ∧ A (w.2.2.1, w.2.2.2) < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    exact hrestNested
  filter_upwards [hab, hpr, hrestFull] with w hdab hpa hAf
  change d w = r (w.1, w.2.2.2) *
    (A (w.2.2.1, w.2.2.2) * b (w.2.1, (w.2.2.1, w.2.2.2)))
  rw [hdab]
  change a (w.1, (w.2.2.1, w.2.2.2)) * b (w.2.1, (w.2.2.1, w.2.2.2)) = _
  rw [← hpa]
  change _ = (a (w.1, (w.2.2.1, w.2.2.2)) / A (w.2.2.1, w.2.2.2)) *
    (A (w.2.2.1, w.2.2.2) * b (w.2.1, (w.2.2.1, w.2.2.2)))
  rw [← mul_assoc, ENNReal.div_mul_cancel hAf.1.ne' hAf.2.ne]

end Causalean.Mathlib.CondIndep.PositiveDensityIntersection

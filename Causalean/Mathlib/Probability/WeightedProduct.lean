/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Pi
import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound

/-!
# Weighted conditional-mean-zero sums under a finite product law

This module states the finite-product second-moment and expected-absolute-value bounds
for marked observations centered by their design-conditional mean.  The weights may
depend measurably on the complete vector of observed designs.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory
open scoped BigOperators

/-- For [a map assigning each observation a design value](hyp:design) and [a finite sample of
observations](hyp:z), [the design vector](goal) assigns to every sample coordinate the design
value of the observation at that coordinate. -/
def designVector {N : Nat} {Omega D : Type*}
    (design : Omega -> D) (z : Fin N -> Omega) : Fin N -> D :=
  fun i => design (z i)

/-- For [a design map](hyp:design) that is [measurable](hyp:hdesign), [the corresponding
finite-sample vector of design values is measurable](goal). -/
@[fun_prop] theorem measurable_designVector
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (design : Omega -> D) (hdesign : Measurable design) :
    Measurable (designVector (N := N) design) := by
  rw [measurable_pi_iff]
  intro i
  exact hdesign.comp (measurable_pi_apply i)

/-- For [a map assigning each observation a design value](hyp:design), [a real-valued outcome
function](hyp:Y), [a real-valued function of design values](hyp:mD), [weights that may depend on
the complete design vector](hyp:w), and [a finite sample of observations](hyp:z), [the weighted
centered sum](goal) is the sum over sample coordinates of each weight times the outcome minus the
given function evaluated at that coordinate's design value. -/
def weightedCenteredSum {N : Nat} {Omega D : Type*}
    (design : Omega -> D) (Y : Omega -> Real) (mD : D -> Real)
    (w : (Fin N -> D) -> Fin N -> Real) (z : Fin N -> Omega) : Real :=
  ∑ i, w (designVector design z) i * (Y (z i) - mD (design (z i)))

private lemma residual_facts
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design) :
    Integrable Y P ∧ Integrable (mD ∘ design) P ∧
      (0 ≤ᵐ[P] mD ∘ design) ∧ (mD ∘ design ≤ᵐ[P] fun _ => 1) ∧
      P[(fun omega => Y omega - mD (design omega)) |
          MeasurableSpace.comap design inferInstance] =ᵐ[P] 0 := by
  let m := MeasurableSpace.comap design inferInstance
  have hYint : Integrable Y P := by
    apply Integrable.of_bound hY.aestronglyMeasurable 1
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg omega)]
    exact hY_le_one omega
  have hmInt : Integrable (mD ∘ design) P :=
    integrable_condExp.congr hcond
  have hmAS : AEStronglyMeasurable[m] (mD ∘ design) P := by
    apply Measurable.aestronglyMeasurable
    exact hmD.comp (comap_measurable design)
  have hcondM : P[mD ∘ design | m] =ᵐ[P] mD ∘ design :=
    condExp_of_aestronglyMeasurable' hdesign.comap_le hmAS hmInt
  have hm_nonneg : 0 ≤ᵐ[P] mD ∘ design := by
    have hmono := condExp_mono (m := m) (integrable_zero Omega Real P) hYint
      (Filter.Eventually.of_forall hY_nonneg)
    filter_upwards [hmono, hcond] with omega hmono' hcond'
    rw [hcond'] at hmono'
    simpa only [Pi.zero_apply, condExp_zero] using hmono'
  have hm_le_one : mD ∘ design ≤ᵐ[P] fun _ => 1 := by
    have hmono := condExp_mono (m := m) hYint (integrable_const (1 : Real))
      (Filter.Eventually.of_forall hY_le_one)
    filter_upwards [hmono, hcond] with omega hmono' hcond'
    rw [hcond'] at hmono'
    rw [congrFun (condExp_const hdesign.comap_le (1 : Real)) omega] at hmono'
    exact hmono'
  have hcenter :
      P[(fun omega => Y omega - mD (design omega)) | m] =ᵐ[P] 0 := by
    have hsub := condExp_sub hYint hmInt m
    filter_upwards [hsub, hcond, hcondM] with omega hsub' hcond' hcondM'
    change P[(fun omega => Y omega - mD (design omega)) | m] omega =
      P[Y | m] omega - P[mD ∘ design | m] omega at hsub'
    rw [hcond', hcondM'] at hsub'
    simpa using hsub'
  exact ⟨hYint, hmInt, hm_nonneg, hm_le_one, hcenter⟩

private lemma integral_design_weight_mul_residual_eq_zero
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (g : D -> Real) (hg : Measurable g)
    (hprodInt : Integrable
      (fun omega => g (design omega) * (Y omega - mD (design omega))) P) :
    ∫ omega, g (design omega) * (Y omega - mD (design omega)) ∂P = 0 := by
  obtain ⟨hYInt, hmInt, hm_nonneg, hm_le_one, hcenter⟩ :=
    residual_facts P design hdesign Y hY hY_nonneg hY_le_one mD hmD hcond
  let m := MeasurableSpace.comap design inferInstance
  have hrInt : Integrable (fun omega => Y omega - mD (design omega)) P := by
    change Integrable (Y - mD ∘ design) P
    exact hYInt.sub hmInt
  have hgAS : AEStronglyMeasurable[m] (g ∘ design) P :=
    (hg.comp (comap_measurable design)).aestronglyMeasurable
  have hprodInt' : Integrable
      ((g ∘ design) * fun omega => Y omega - mD (design omega)) P := by
    change Integrable
      (fun omega => g (design omega) * (Y omega - mD (design omega))) P
    exact hprodInt
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    (μ := P) (m := m) hgAS hprodInt' hrInt
  calc
    ∫ omega, g (design omega) * (Y omega - mD (design omega)) ∂P =
        ∫ omega, P[((g ∘ design) *
          fun omega => Y omega - mD (design omega)) | m] omega ∂P := by
            rw [integral_condExp hdesign.comap_le]
            rfl
    _ = ∫ omega, (g ∘ design) omega *
        P[(fun omega => Y omega - mD (design omega)) | m] omega ∂P :=
      integral_congr_ae hpull
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hcenter] with omega hcenter'
      rw [hcenter']
      simp

private lemma integral_design_weight_mul_outcome_eq
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (g : D -> Real) (hg : Measurable g) (hgInt : Integrable (g ∘ design) P) :
    ∫ omega, g (design omega) * Y omega ∂P =
      ∫ omega, g (design omega) * mD (design omega) ∂P := by
  obtain ⟨hYInt, hmInt, hm_nonneg, hm_le_one, hcenter⟩ :=
    residual_facts P design hdesign Y hY hY_nonneg hY_le_one mD hmD hcond
  let m := MeasurableSpace.comap design inferInstance
  have hgAS : AEStronglyMeasurable[m] (g ∘ design) P :=
    (hg.comp (comap_measurable design)).aestronglyMeasurable
  have hYBound : ∀ omega, ‖Y omega‖ ≤ (1 : Real) := by
    intro omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg omega)]
    exact hY_le_one omega
  have hprodInt : Integrable ((g ∘ design) * Y) P :=
    by
      apply hgInt.norm.mono'
      · exact ((hg.comp hdesign).mul hY).aestronglyMeasurable
      · filter_upwards with omega
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hYBound omega)
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    (μ := P) (m := m) hgAS hprodInt hYInt
  calc
    ∫ omega, g (design omega) * Y omega ∂P =
        ∫ omega, P[((g ∘ design) * Y) | m] omega ∂P := by
          rw [integral_condExp hdesign.comap_le]
          rfl
    _ = ∫ omega, (g ∘ design) omega * P[Y | m] omega ∂P :=
      integral_congr_ae hpull
    _ = ∫ omega, g (design omega) * mD (design omega) ∂P := by
      apply integral_congr_ae
      filter_upwards [hcond] with omega hcond'
      rw [hcond']
      rfl

private lemma integral_design_weight_mul_residual_sq_le
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (g : D -> Real) (hg : Measurable g) (hg_nonneg : forall d, 0 <= g d)
    (hgInt : Integrable (g ∘ design) P) :
    ∫ omega, g (design omega) * (Y omega - mD (design omega)) ^ 2 ∂P ≤
      (1 / 4 : Real) * ∫ omega, g (design omega) ∂P := by
  obtain ⟨hYInt, hmInt, hm_nonneg, hm_le_one, hcenter⟩ :=
    residual_facts P design hdesign Y hY hY_nonneg hY_le_one mD hmD hcond
  let G : Omega -> Real := g ∘ design
  let M : Omega -> Real := mD ∘ design
  have hGmeas : Measurable G := hg.comp hdesign
  have hMmeas : Measurable M := hmD.comp hdesign
  have hYnorm : forall omega, ‖Y omega‖ ≤ (1 : Real) := by
    intro omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg omega)]
    exact hY_le_one omega
  have hMnorm : ∀ᵐ omega ∂P, ‖M omega‖ ≤ (1 : Real) := by
    filter_upwards [hm_nonneg, hm_le_one] with omega hm0 hm1
    change 0 ≤ M omega at hm0
    change M omega ≤ 1 at hm1
    rw [Real.norm_eq_abs, abs_of_nonneg hm0]
    exact hm1
  have hmul_bounded (F : Omega -> Real) (hF : AEStronglyMeasurable F P)
      (hFnorm : ∀ᵐ omega ∂P, ‖F omega‖ ≤ (1 : Real)) :
      Integrable (G * F) P := by
    apply hgInt.norm.mono'
    · exact hGmeas.aestronglyMeasurable.mul hF
    · filter_upwards [hFnorm] with omega hFnorm'
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hFnorm'
  have hGY : Integrable (G * Y) P :=
    hmul_bounded Y hY.aestronglyMeasurable (Filter.Eventually.of_forall hYnorm)
  have hGYsq : Integrable (G * fun omega => Y omega ^ 2) P := by
    apply hmul_bounded (fun omega => Y omega ^ 2) (hY.pow_const 2).aestronglyMeasurable
    filter_upwards with omega
    rw [norm_pow]
    have hn : 0 ≤ ‖Y omega‖ := norm_nonneg _
    have hs := (sq_le_sq₀ hn (by norm_num)).2 (hYnorm omega)
    simpa using hs
  have hGM : Integrable (G * M) P :=
    hmul_bounded M hMmeas.aestronglyMeasurable hMnorm
  have hGMsq : Integrable (G * fun omega => M omega ^ 2) P := by
    apply hmul_bounded (fun omega => M omega ^ 2) (hMmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [hMnorm] with omega hMnorm'
    rw [norm_pow]
    have hn : 0 ≤ ‖M omega‖ := norm_nonneg _
    have hs := (sq_le_sq₀ hn (by norm_num)).2 hMnorm'
    simpa using hs
  let gM : D -> Real := fun d => g d * mD d
  have hgM : Measurable gM := hg.mul hmD
  have hgMInt : Integrable (gM ∘ design) P := by
    have : gM ∘ design = G * M := by
      funext omega
      rfl
    rw [this]
    exact hGM
  have hgMY : Integrable ((gM ∘ design) * Y) P := by
    apply hgMInt.norm.mono'
    · exact (hgM.comp hdesign).aestronglyMeasurable.mul hY.aestronglyMeasurable
    · filter_upwards with omega
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hYnorm omega)
  have hfirst : ∫ omega, G omega * Y omega ^ 2 ∂P ≤
      ∫ omega, G omega * Y omega ∂P := by
    apply integral_mono_ae hGYsq hGY
    filter_upwards with omega
    have hy2 : Y omega ^ 2 ≤ Y omega := by
      nlinarith [hY_nonneg omega, hY_le_one omega]
    exact mul_le_mul_of_nonneg_left hy2 (hg_nonneg (design omega))
  have hmean := integral_design_weight_mul_outcome_eq P design hdesign Y hY
    hY_nonneg hY_le_one mD hmD hcond g hg hgInt
  have hmeanM := integral_design_weight_mul_outcome_eq P design hdesign Y hY
    hY_nonneg hY_le_one mD hmD hcond gM hgM hgMInt
  have hA : Integrable (fun omega => G omega * Y omega ^ 2) P := by
    change Integrable (G * fun omega => Y omega ^ 2) P
    exact hGYsq
  have hB : Integrable (fun omega => (gM ∘ design) omega * Y omega) P := by
    change Integrable ((gM ∘ design) * Y) P
    exact hgMY
  have hC : Integrable (fun omega => G omega * M omega ^ 2) P := by
    change Integrable (G * fun omega => M omega ^ 2) P
    exact hGMsq
  have hexpand :
      (∫ omega, G omega * (Y omega - M omega) ^ 2 ∂P) =
        (∫ omega, G omega * Y omega ^ 2 ∂P) -
          2 * (∫ omega, (gM ∘ design) omega * Y omega ∂P) +
            ∫ omega, G omega * M omega ^ 2 ∂P := by
    calc
      _ = ∫ omega, (G omega * Y omega ^ 2 -
          2 * ((gM ∘ design) omega * Y omega)) + G omega * M omega ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards with omega
        simp [gM, G, M]
        ring
      _ = _ := by
        change (∫ omega, ((fun x => G x * Y x ^ 2) -
          (fun x => 2 * ((gM ∘ design) x * Y x)) +
          (fun x => G x * M x ^ 2)) omega ∂P) = _
        calc
          _ = (∫ omega, ((fun x => G x * Y x ^ 2) -
                (fun x => 2 * ((gM ∘ design) x * Y x))) omega ∂P) +
              ∫ omega, G omega * M omega ^ 2 ∂P := by
                simpa only [Pi.add_apply] using
                  integral_add (hA.sub (hB.const_mul 2)) hC
          _ = ((∫ omega, G omega * Y omega ^ 2 ∂P) -
                ∫ omega, 2 * ((gM ∘ design) omega * Y omega) ∂P) +
              ∫ omega, G omega * M omega ^ 2 ∂P := by
                have hsubeq := integral_sub hA (hB.const_mul 2)
                have hsubeq' :
                    (∫ omega, ((fun x => G x * Y x ^ 2) -
                      (fun x => 2 * ((gM ∘ design) x * Y x))) omega ∂P) =
                      (∫ omega, G omega * Y omega ^ 2 ∂P) -
                        ∫ omega, 2 * ((gM ∘ design) omega * Y omega) ∂P := by
                  simpa only [Pi.sub_apply] using hsubeq
                rw [hsubeq']
          _ = _ := by rw [integral_const_mul]
  have hmiddle :
      (∫ omega, G omega * (Y omega - M omega) ^ 2 ∂P) ≤
        ∫ omega, G omega * (M omega - M omega ^ 2) ∂P := by
    rw [hexpand]
    have hmean' : (∫ omega, G omega * Y omega ∂P) =
        ∫ omega, G omega * M omega ∂P := by simpa [G, M] using hmean
    have hmeanM' : (∫ omega, (gM ∘ design) omega * Y omega ∂P) =
        ∫ omega, (gM ∘ design) omega * M omega ∂P := by
      simpa [M] using hmeanM
    rw [hmeanM']
    have hBM : Integrable (fun omega => (gM ∘ design) omega * M omega) P := by
      have heq : (fun omega => (gM ∘ design) omega * M omega) =
          fun omega => G omega * M omega ^ 2 := by
        funext omega
        simp [gM, G, M]
        ring
      rw [heq]
      exact hC
    have hcombine :
        (∫ omega, G omega * M omega ∂P) -
            2 * (∫ omega, (gM ∘ design) omega * M omega ∂P) +
              ∫ omega, G omega * M omega ^ 2 ∂P =
          ∫ omega, G omega * (M omega - M omega ^ 2) ∂P := by
      calc
        _ = (∫ omega, G omega * M omega ∂P) -
            ∫ omega, G omega * M omega ^ 2 ∂P := by
              have heq : (∫ omega, (gM ∘ design) omega * M omega ∂P) =
                  ∫ omega, G omega * M omega ^ 2 ∂P := by
                apply integral_congr_ae
                filter_upwards with omega
                simp [gM, G, M]
                ring
              rw [heq]
              ring
        _ = _ := by
          rw [← integral_sub]
          · apply integral_congr_ae
            filter_upwards with omega
            ring
          · change Integrable (G * M) P
            exact hGM
          · exact hC
    calc
      (∫ omega, G omega * Y omega ^ 2 ∂P) -
            2 * (∫ omega, (gM ∘ design) omega * M omega ∂P) +
          ∫ omega, G omega * M omega ^ 2 ∂P ≤
          (∫ omega, G omega * Y omega ∂P) -
            2 * (∫ omega, (gM ∘ design) omega * M omega ∂P) +
          ∫ omega, G omega * M omega ^ 2 ∂P := by linarith
      _ = ∫ omega, G omega * (M omega - M omega ^ 2) ∂P := by
        rw [hmean']
        exact hcombine
  rw [show (∫ omega, g (design omega) * (Y omega - mD (design omega)) ^ 2 ∂P) =
      ∫ omega, G omega * (Y omega - M omega) ^ 2 ∂P by rfl]
  refine hmiddle.trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae
  · have hGM' : Integrable (fun omega => G omega * M omega) P := by
      change Integrable (G * M) P
      exact hGM
    have : Integrable (fun omega => G omega * M omega - G omega * M omega ^ 2) P :=
      hGM'.sub hC
    exact this.congr (Filter.Eventually.of_forall fun omega => by ring)
  · exact hgInt.const_mul (1 / 4 : Real)
  · filter_upwards [hm_nonneg, hm_le_one] with omega hm0 hm1
    change 0 ≤ M omega at hm0
    change M omega ≤ 1 at hm1
    have hquad : M omega - M omega ^ 2 ≤ (1 / 4 : Real) := by
      nlinarith [sq_nonneg (M omega - (1 / 2 : Real))]
    change G omega * (M omega - M omega ^ 2) ≤ (1 / 4 : Real) * G omega
    calc
      G omega * (M omega - M omega ^ 2) ≤ G omega * (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_left hquad (hg_nonneg (design omega))
      _ = (1 / 4 : Real) * G omega := by ring

private lemma product_cross_integral_eq_zero
    {n : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin (n + 1) -> D) -> Fin (n + 1) -> Real) (hw : Measurable w)
    (i j : Fin (n + 1)) (hij : i ≠ j)
    (hInt : Integrable
      (fun z : Fin (n + 1) -> Omega =>
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) *
        (w (designVector design z) j * (Y (z j) - mD (design (z j)))))
      (Measure.pi (fun _ : Fin (n + 1) => P))) :
    (∫ z : Fin (n + 1) -> Omega,
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) *
        (w (designVector design z) j * (Y (z j) - mD (design (z j))))
        ∂(Measure.pi (fun _ : Fin (n + 1) => P))) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Omega) i
  let tailP : Measure (Fin n -> Omega) := Measure.pi fun _ : Fin n => P
  let F : Omega × (Fin n -> Omega) -> Real := fun p =>
    let z := e.symm p
    (w (designVector design z) i * (Y (z i) - mD (design (z i)))) *
      (w (designVector design z) j * (Y (z j) - mD (design (z j))))
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => P) i
  have hFInt : Integrable F (P.prod tailP) := by
    have hc : Integrable (F ∘ e) (Measure.pi (fun _ : Fin (n + 1) => P)) ↔
        Integrable F (P.prod tailP) := by
      dsimp [e, tailP]
      exact hmp.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Omega) i).measurableEmbedding
    apply hc.mp
    have heq : F ∘ e = fun z : Fin (n + 1) -> Omega =>
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) *
        (w (designVector design z) j * (Y (z j) - mD (design (z j)))) := by
      funext z
      simp [F]
    rw [heq]
    exact hInt
  have hinner : ∀ᵐ y ∂tailP, (∫ x, F (x, y) ∂P) = 0 := by
    filter_upwards [hFInt.prod_left_ae] with y hyInt
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    subst j
    let v : D -> (Fin (n + 1) -> D) := fun d =>
      Fin.insertNth i d (fun q => design (y q))
    let g : D -> Real := fun d =>
      w (v d) i *
        (w (v d) (i.succAbove k) * (Y (y k) - mD (design (y k))))
    have hv : Measurable v := by
      rw [measurable_pi_iff]
      intro q
      by_cases hqi : q = i
      · subst q
        simp only [v, Fin.insertNth_apply_same]
        fun_prop
      · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hqi
        subst q
        simp [v]
    have hg : Measurable g := by
      exact (((measurable_pi_apply i).comp (hw.comp hv)).mul
        (((measurable_pi_apply (i.succAbove k)).comp (hw.comp hv)).mul measurable_const))
    have hsection :
        Integrable
          (fun x => g (design x) * (Y x - mD (design x))) P := by
      have hdesignInsert (x : Omega) :
          designVector design (Fin.insertNth i x y) = v (design x) := by
        funext q
        by_cases hqi : q = i
        · subst q
          simp [designVector, v]
        · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hqi
          subst q
          simp [designVector, v]
      have heq : (fun x => g (design x) * (Y x - mD (design x))) =
          fun x => F (x, y) := by
        funext x
        simp [F, e, g, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, hdesignInsert]
        ring
      rw [heq]
      exact hyInt
    have hz := integral_design_weight_mul_residual_eq_zero P design hdesign
      Y hY hY_nonneg hY_le_one mD hmD hcond g hg hsection
    have hdesignInsert (x : Omega) :
        designVector design (Fin.insertNth i x y) = v (design x) := by
      funext q
      by_cases hqi : q = i
      · subst q
        simp [designVector, v]
      · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hqi
        subst q
        simp [designVector, v]
    rw [← hz]
    apply integral_congr_ae
    filter_upwards with x
    simp [F, e, g, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, hdesignInsert]
    ring
  calc
    _ = ∫ p, F p ∂(P.prod tailP) := by
      have ht := hmp.integral_comp' F
      calc
        _ = ∫ z, F (e z) ∂(Measure.pi (fun _ : Fin (n + 1) => P)) := by
          apply integral_congr_ae
          filter_upwards with z
          simp [F]
        _ = _ := by
          dsimp [e, tailP]
          exact ht
    _ = ∫ y, ∫ x, F (x, y) ∂P ∂tailP := integral_prod_symm F hFInt
    _ = 0 := integral_eq_zero_of_ae hinner

private lemma product_diag_integral_le
    {n : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin (n + 1) -> D) -> Fin (n + 1) -> Real) (hw : Measurable w)
    (i : Fin (n + 1))
    (hDiagInt : Integrable
      (fun z : Fin (n + 1) -> Omega =>
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) ^ 2)
      (Measure.pi (fun _ : Fin (n + 1) => P)))
    (hWeightInt : Integrable
      (fun z : Fin (n + 1) -> Omega => (w (designVector design z) i) ^ 2)
      (Measure.pi (fun _ : Fin (n + 1) => P))) :
    (∫ z : Fin (n + 1) -> Omega,
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) ^ 2
        ∂(Measure.pi (fun _ : Fin (n + 1) => P))) ≤
      (1 / 4 : Real) *
        ∫ z : Fin (n + 1) -> Omega, (w (designVector design z) i) ^ 2
          ∂(Measure.pi (fun _ : Fin (n + 1) => P)) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Omega) i
  let tailP : Measure (Fin n -> Omega) := Measure.pi fun _ : Fin n => P
  let F : Omega × (Fin n -> Omega) -> Real := fun p =>
    let z := e.symm p
    (w (designVector design z) i * (Y (z i) - mD (design (z i)))) ^ 2
  let G : Omega × (Fin n -> Omega) -> Real := fun p =>
    let z := e.symm p
    (w (designVector design z) i) ^ 2
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => P) i
  have htransport (H : Omega × (Fin n -> Omega) -> Real)
      (hH : Integrable (H ∘ e) (Measure.pi (fun _ : Fin (n + 1) => P))) :
      Integrable H (P.prod tailP) := by
    have hc : Integrable (H ∘ e) (Measure.pi (fun _ : Fin (n + 1) => P)) ↔
        Integrable H (P.prod tailP) := by
      dsimp [e, tailP]
      exact hmp.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Omega) i).measurableEmbedding
    exact hc.mp hH
  have hFInt : Integrable F (P.prod tailP) := by
    apply htransport F
    have heq : F ∘ e = fun z : Fin (n + 1) -> Omega =>
        (w (designVector design z) i * (Y (z i) - mD (design (z i)))) ^ 2 := by
      funext z
      simp [F]
    rw [heq]
    exact hDiagInt
  have hGInt : Integrable G (P.prod tailP) := by
    apply htransport G
    have heq : G ∘ e = fun z : Fin (n + 1) -> Omega =>
        (w (designVector design z) i) ^ 2 := by
      funext z
      simp [G]
    rw [heq]
    exact hWeightInt
  have hinner : ∀ᵐ y ∂tailP,
      (∫ x, F (x, y) ∂P) ≤ (1 / 4 : Real) * ∫ x, G (x, y) ∂P := by
    filter_upwards [hFInt.prod_left_ae, hGInt.prod_left_ae] with y hyF hyG
    let v : D -> (Fin (n + 1) -> D) := fun d =>
      Fin.insertNth i d (fun q => design (y q))
    let g : D -> Real := fun d => (w (v d) i) ^ 2
    have hv : Measurable v := by
      rw [measurable_pi_iff]
      intro q
      by_cases hqi : q = i
      · subst q
        simp only [v, Fin.insertNth_apply_same]
        fun_prop
      · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hqi
        subst q
        simp [v]
    have hg : Measurable g :=
      ((measurable_pi_apply i).comp (hw.comp hv)).pow_const 2
    have hg0 : forall d, 0 <= g d := fun d => sq_nonneg _
    have hdesignInsert (x : Omega) :
        designVector design (Fin.insertNth i x y) = v (design x) := by
      funext q
      by_cases hqi : q = i
      · subst q
        simp [designVector, v]
      · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hqi
        subst q
        simp [designVector, v]
    have hgSection : Integrable (g ∘ design) P := by
      have heq : (g ∘ design) = fun x => G (x, y) := by
        funext x
        simp [G, e, g, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, hdesignInsert]
      rw [heq]
      exact hyG
    have hone := integral_design_weight_mul_residual_sq_le P design hdesign
      Y hY hY_nonneg hY_le_one mD hmD hcond g hg hg0 hgSection
    have hleft : (∫ x, F (x, y) ∂P) =
        ∫ x, g (design x) * (Y x - mD (design x)) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with x
      simp [F, e, g, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, hdesignInsert]
      ring
    have hright : (∫ x, G (x, y) ∂P) = ∫ x, g (design x) ∂P := by
      apply integral_congr_ae
      filter_upwards with x
      simp [G, e, g, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, hdesignInsert]
    rw [hleft, hright]
    exact hone
  have houterF : Integrable (fun y => ∫ x, F (x, y) ∂P) tailP :=
    hFInt.integral_prod_right
  have houterG : Integrable (fun y => ∫ x, G (x, y) ∂P) tailP :=
    hGInt.integral_prod_right
  have hprodineq : (∫ p, F p ∂(P.prod tailP)) ≤
      (1 / 4 : Real) * ∫ p, G p ∂(P.prod tailP) := by
    rw [integral_prod_symm F hFInt, integral_prod_symm G hGInt,
      ← integral_const_mul]
    exact integral_mono_ae houterF (houterG.const_mul (1 / 4 : Real)) hinner
  have htransF := hmp.integral_comp' F
  have htransG := hmp.integral_comp' G
  calc
    _ = ∫ p, F p ∂(P.prod tailP) := by
      calc
        _ = ∫ z, F (e z) ∂(Measure.pi (fun _ : Fin (n + 1) => P)) := by
          apply integral_congr_ae
          filter_upwards with z
          simp [F]
        _ = _ := by
          dsimp [e, tailP]
          exact htransF
    _ ≤ (1 / 4 : Real) * ∫ p, G p ∂(P.prod tailP) := hprodineq
    _ = (1 / 4 : Real) *
        ∫ z, (w (designVector design z) i) ^ 2
          ∂(Measure.pi (fun _ : Fin (n + 1) => P)) := by
      congr 1
      have ht : (∫ z, G (e z) ∂(Measure.pi (fun _ : Fin (n + 1) => P))) =
          ∫ p, G p ∂(P.prod tailP) := by
        simpa [e, tailP] using htransG
      rw [← ht]
      apply integral_congr_ae
      filter_upwards with z
      simp [G]

/-- For [a one-observation probability law](hyp:P), [a measurable design map](hyp:design,hdesign),
[a measurable outcome confined to the unit interval](hyp:Y,hY,hY_nonneg,hY_le_one), [a
measurable design regression that is its conditional expectation](hyp:mD,hmD,hcond), [a
measurable array of weights depending on the full design vector](hyp:w,hw), and [the two
natural square-integrability conditions](hyp:hweight_sq,hsum_sq), [the second moment of the
weighted centered sum is at most one quarter of the expected sum of squared weights](goal).

The proof derives both vanishing cross terms and the one-quarter conditional-variance bound;
they are not additional assumptions. -/
theorem product_weighted_centered_sq_integral_le
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w)
    (hweight_sq : Integrable
      (fun z : Fin N -> Omega => ∑ i, (w (designVector design z) i) ^ 2)
      (Measure.pi (fun _ : Fin N => P)))
    (hsum_sq : Integrable
      (fun z : Fin N -> Omega =>
        (weightedCenteredSum design Y mD w z) ^ 2)
      (Measure.pi (fun _ : Fin N => P))) :
    (∫ z : Fin N -> Omega,
        (weightedCenteredSum design Y mD w z) ^ 2
        ∂(Measure.pi (fun _ : Fin N => P))) <=
      (1 / 4 : Real) *
        (∫ z : Fin N -> Omega,
          ∑ i, (w (designVector design z) i) ^ 2
          ∂(Measure.pi (fun _ : Fin N => P))) := by
  cases N with
  | zero => simp [weightedCenteredSum]
  | succ n =>
    let μN : Measure (Fin (n + 1) -> Omega) :=
      Measure.pi fun _ : Fin (n + 1) => P
    let W : Fin (n + 1) -> (Fin (n + 1) -> Omega) -> Real :=
      fun i z => w (designVector design z) i
    let R : Fin (n + 1) -> (Fin (n + 1) -> Omega) -> Real :=
      fun i z => Y (z i) - mD (design (z i))
    let X : Fin (n + 1) -> (Fin (n + 1) -> Omega) -> Real :=
      fun i z => W i z * R i z
    have hdesignN : Measurable (designVector (N := n + 1) design) :=
      measurable_designVector design hdesign
    have hWmeas (i : Fin (n + 1)) : Measurable (W i) := by
      exact (measurable_pi_apply i).comp (hw.comp hdesignN)
    have hRmeas (i : Fin (n + 1)) : Measurable (R i) := by
      exact (hY.comp (measurable_pi_apply i)).sub
        (hmD.comp (hdesign.comp (measurable_pi_apply i)))
    have hXmeas (i : Fin (n + 1)) : Measurable (X i) :=
      (hWmeas i).mul (hRmeas i)
    have henergyMeas : Measurable
        (fun z : Fin (n + 1) -> Omega => ∑ i, (W i z) ^ 2) :=
      Finset.measurable_sum _ fun i _ => (hWmeas i).pow_const 2
    obtain ⟨hYInt, hmInt, hm_nonneg, hm_le_one, hcenter⟩ :=
      residual_facts P design hdesign Y hY hY_nonneg hY_le_one mD hmD hcond
    have hRbound (i : Fin (n + 1)) : ∀ᵐ z ∂μN, ‖R i z‖ ≤ (2 : Real) := by
      have hmp := measurePreserving_eval (fun _ : Fin (n + 1) => P) i
      have hm0 := hmp.quasiMeasurePreserving.tendsto_ae.eventually hm_nonneg
      have hm1 := hmp.quasiMeasurePreserving.tendsto_ae.eventually hm_le_one
      filter_upwards [hm0, hm1] with z hz0 hz1
      change 0 ≤ mD (design (z i)) at hz0
      change mD (design (z i)) ≤ 1 at hz1
      rw [Real.norm_eq_abs]
      apply abs_le.2
      constructor <;> linarith [hY_nonneg (z i), hY_le_one (z i)]
    have hWiSq (i : Fin (n + 1)) : Integrable (fun z => (W i z) ^ 2) μN := by
      apply Integrable.mono hweight_sq ((hWmeas i).pow_const 2).aestronglyMeasurable
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun k : Fin (n + 1) => (W k z) ^ 2)
        (fun k _ => sq_nonneg (W k z)) (Finset.mem_univ i)
    have hXiSq (i : Fin (n + 1)) : Integrable (fun z => (X i z) ^ 2) μN := by
      apply (hWiSq i).const_mul 4 |>.mono'
      · exact (hXmeas i).pow_const 2 |>.aestronglyMeasurable
      · filter_upwards [hRbound i] with z hr
        change ‖(X i z) ^ 2‖ ≤ (4 : Real) * (W i z) ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (W i z * R i z) ^ 2 ≤ 4 * W i z ^ 2
        rw [Real.norm_eq_abs] at hr
        have hrsq : (R i z) ^ 2 ≤ 4 := by
          rw [← sq_abs]
          have hs := (sq_le_sq₀ (abs_nonneg (R i z)) (by norm_num)).2 hr
          norm_num at hs ⊢
          exact hs
        rw [mul_pow]
        calc
          W i z ^ 2 * R i z ^ 2 ≤ W i z ^ 2 * 4 :=
            mul_le_mul_of_nonneg_left hrsq (sq_nonneg _)
          _ = 4 * W i z ^ 2 := by ring
    have hcrossInt (i j : Fin (n + 1)) :
        Integrable (fun z => X i z * X j z) μN := by
      apply (hXiSq i).add (hXiSq j) |>.mono'
      · exact (hXmeas i).mul (hXmeas j) |>.aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs]
        have ha : 0 ≤ |X i z| := abs_nonneg _
        have hb : 0 ≤ |X j z| := abs_nonneg _
        have hab : |X i z * X j z| = |X i z| * |X j z| := abs_mul _ _
        rw [hab]
        have hsq := sq_nonneg (|X i z| - |X j z|)
        have hi : (X i z) ^ 2 = |X i z| ^ 2 := (sq_abs _).symm
        have hj : (X j z) ^ 2 = |X j z| ^ 2 := (sq_abs _).symm
        change |X i z| * |X j z| ≤ (X i z) ^ 2 + (X j z) ^ 2
        rw [hi, hj]
        nlinarith [sq_nonneg |X i z|, sq_nonneg |X j z|]
    have hdiag (i : Fin (n + 1)) :
        (∫ z, (X i z) ^ 2 ∂μN) ≤
          (1 / 4 : Real) * ∫ z, (W i z) ^ 2 ∂μN := by
      simpa [μN, X, W, R] using
        product_diag_integral_le P design hdesign Y hY hY_nonneg hY_le_one
          mD hmD hcond w hw i (hXiSq i) (hWiSq i)
    have hcross (i j : Fin (n + 1)) (hij : i ≠ j) :
        (∫ z, X i z * X j z ∂μN) = 0 := by
      simpa [μN, X, W, R] using
        product_cross_integral_eq_zero P design hdesign Y hY hY_nonneg hY_le_one
          mD hmD hcond w hw i j hij (hcrossInt i j)
    have hsquare (z : Fin (n + 1) -> Omega) :
        (weightedCenteredSum design Y mD w z) ^ 2 =
          ∑ i, ∑ j, X i z * X j z := by
      rw [pow_two]
      simp only [weightedCenteredSum, X, W, R]
      rw [Finset.sum_mul_sum]
    have hsumIntegral :
        (∫ z, (weightedCenteredSum design Y mD w z) ^ 2 ∂μN) =
          ∑ i, ∑ j, ∫ z, X i z * X j z ∂μN := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hsquare)]
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ]
        intro j hj
        exact hcrossInt i j
      · intro i hi
        exact integrable_finsetSum Finset.univ fun j _ => hcrossInt i j
    have hcollapse (i : Fin (n + 1)) :
        (∑ j, ∫ z, X i z * X j z ∂μN) = ∫ z, (X i z) ^ 2 ∂μN := by
      rw [Finset.sum_eq_single i]
      · apply integral_congr_ae
        filter_upwards with z
        rw [pow_two]
      · intro j hj hji
        exact hcross i j (Ne.symm hji)
      · simp
    have henergyIntegral :
        (∫ z, ∑ i, (W i z) ^ 2 ∂μN) =
          ∑ i, ∫ z, (W i z) ^ 2 ∂μN := by
      exact integral_finsetSum Finset.univ fun i _ => hWiSq i
    change (∫ z, (weightedCenteredSum design Y mD w z) ^ 2 ∂μN) ≤
      (1 / 4 : Real) * ∫ z, ∑ i, (W i z) ^ 2 ∂μN
    rw [hsumIntegral]
    simp_rw [hcollapse]
    rw [henergyIntegral, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hdiag i

/-- For [a one-observation probability law](hyp:P), [a measurable design map](hyp:design,hdesign),
[a measurable outcome confined to the unit interval](hyp:Y,hY,hY_nonneg,hY_le_one), [a
measurable design regression that is its conditional expectation](hyp:mD,hmD,hcond), [a
measurable array of weights depending on the full design vector](hyp:w,hw), and [the two
natural square-integrability conditions](hyp:hweight_sq,hsum_sq), [the expected absolute
weighted centered sum is at most one half the square root of the expected sum of squared
weights](goal).

Weights may depend on all observed designs, rather than only their own coordinate. -/
theorem product_weighted_centered_l1_le
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : forall omega, 0 <= Y omega)
    (hY_le_one : forall omega, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w)
    (hweight_sq : Integrable
      (fun z : Fin N -> Omega => ∑ i, (w (designVector design z) i) ^ 2)
      (Measure.pi (fun _ : Fin N => P)))
    (hsum_sq : Integrable
      (fun z : Fin N -> Omega =>
        (weightedCenteredSum design Y mD w z) ^ 2)
      (Measure.pi (fun _ : Fin N => P))) :
    (∫ z : Fin N -> Omega,
        abs (weightedCenteredSum design Y mD w z)
        ∂(Measure.pi (fun _ : Fin N => P))) <=
      (1 / 2 : Real) * Real.sqrt
        (∫ z : Fin N -> Omega,
          ∑ i, (w (designVector design z) i) ^ 2
          ∂(Measure.pi (fun _ : Fin N => P))) := by
  let μN : Measure (Fin N -> Omega) := Measure.pi fun _ : Fin N => P
  let S : (Fin N -> Omega) -> Real := weightedCenteredSum design Y mD w
  let A : Real := ∫ z : Fin N -> Omega,
    ∑ i, (w (designVector design z) i) ^ 2 ∂μN
  have hdesignN : Measurable (designVector (N := N) design) :=
    measurable_designVector design hdesign
  have hSmeas : Measurable S := by
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply i).comp (hw.comp hdesignN)).mul
      ((hY.comp (measurable_pi_apply i)).sub
        (hmD.comp (hdesign.comp (measurable_pi_apply i))))
  have hSLp : MemLp S 2 μN := by
    apply (memLp_two_iff_integrable_sq hSmeas.aestronglyMeasurable).2
    simpa [S, μN] using hsum_sq
  have hCS : (∫ z, abs (S z) ∂μN) ≤
      Real.sqrt (∫ z, (S z) ^ 2 ∂μN) := by
    simpa [Real.norm_eq_abs] using
      Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
        μN S hSLp
  have hL2 : (∫ z, (S z) ^ 2 ∂μN) ≤ (1 / 4 : Real) * A := by
    simpa [S, A, μN] using
      product_weighted_centered_sq_integral_le P design hdesign Y hY hY_nonneg
        hY_le_one mD hmD hcond w hw hweight_sq hsum_sq
  have hA0 : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrt : Real.sqrt ((1 / 4 : Real) * A) =
      (1 / 2 : Real) * Real.sqrt A := by
    calc
      Real.sqrt ((1 / 4 : Real) * A) =
          Real.sqrt (((1 / 2 : Real) * Real.sqrt A) ^ 2) := by
        congr 1
        rw [pow_two]
        calc
          (1 / 4 : Real) * A =
              (1 / 4 : Real) * (Real.sqrt A * Real.sqrt A) := by
                rw [Real.mul_self_sqrt hA0]
          _ = (1 / 2 : Real) * Real.sqrt A *
              ((1 / 2 : Real) * Real.sqrt A) := by ring
      _ = (1 / 2 : Real) * Real.sqrt A :=
        Real.sqrt_sq (mul_nonneg (by norm_num) (Real.sqrt_nonneg A))
  change (∫ z, abs (S z) ∂μN) ≤ (1 / 2 : Real) * Real.sqrt A
  calc
    (∫ z, abs (S z) ∂μN) ≤ Real.sqrt (∫ z, (S z) ^ 2 ∂μN) := hCS
    _ ≤ Real.sqrt ((1 / 4 : Real) * A) := Real.sqrt_le_sqrt hL2
    _ = (1 / 2 : Real) * Real.sqrt A := hsqrt

end Causalean.Mathlib.Probability

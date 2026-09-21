/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.ThreeBlockMarginals

/-!
# Three-block conditional-density factorization

This module isolates the generic three-block bridge used by the four-block intersection theorem.
It separates the conditional-independence argument from the purely density-theoretic conversion
between a cross-multiplication identity and a measurable product factorization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.CondIndep.PositiveDensityIntersection

universe uA uB uC

section DensityFactorization

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
variable (muA : Measure A) (muB : Measure B) (muC : Measure C)
variable [SigmaFinite muA] [SigmaFinite muB] [SigmaFinite muC]
variable {d : ThreeBlock A B C → ℝ≥0∞}
variable [IsFiniteMeasure ((threeBlockReference muA muB muC).withDensity d)]

/-- A measurable conditional product factorization of a finite three-block density implies the
cross-multiplied conditional-density identity. -/
theorem threeBlockDensityIdentity_of_factors (hd : Measurable d)
    (hfac : ThreeBlockFactors muA muB muC d) :
    ThreeBlockDensityIdentity muA muB muC d := by
  /- Expand all three marginal densities and use Tonelli to integrate the product factorization.
  Finiteness rules out the `0 * ∞` exceptional cases almost everywhere, after which the target
  is commutativity and associativity of multiplication in `ℝ≥0∞`. -/
  rcases hfac with ⟨a, b, ha, hb, hab⟩
  have hfirstMeas : Measurable (densityFirstConditioning muB d) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (A × C) × B ↦ d (q.1.1, (q.2, q.1.2)))
    fun_prop
  have hsecondMeas : Measurable (densitySecondConditioning muA d) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (B × C) × A ↦ d (q.2, (q.1.1, q.1.2)))
    fun_prop
  have hcondMeas : Measurable (densityConditioning muA muB d) := by
    apply Measurable.lintegral_prod_right
    change Measurable
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB)
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (C × A) × B ↦ d (q.1.2, (q.2, q.1.1)))
    fun_prop
  have habABC : ∀ᵐ x ∂muA, ∀ᵐ y ∂muB, ∀ᵐ z ∂muC,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hab] with x hx
    exact Measure.ae_ae_of_ae_prod hx
  have habACB : ∀ᵐ x ∂muA, ∀ᵐ z ∂muC, ∀ᵐ y ∂muB,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    filter_upwards [habABC] with x hx
    exact (Measure.ae_ae_comm (by measurability)).1 hx
  have habBCA : ∀ᵐ y ∂muB, ∀ᵐ z ∂muC, ∀ᵐ x ∂muA,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    have hswap : ∀ᵐ yz ∂muB.prod muC, ∀ᵐ x ∂muA,
        d (x, yz) = a (x, yz.2) * b yz := by
      apply (Measure.ae_ae_comm (by measurability)).1
      exact Measure.ae_ae_of_ae_prod hab
    exact Measure.ae_ae_of_ae_prod hswap
  have hfirst : ∀ᵐ x ∂muA, ∀ᵐ z ∂muC,
      densityFirstConditioning muB d (x, z) =
        a (x, z) * ∫⁻ y, b (y, z) ∂muB := by
    filter_upwards [habACB] with x hx
    filter_upwards [hx] with z hz
    change (∫⁻ y, d (x, (y, z)) ∂muB) = _
    rw [lintegral_congr_ae hz, lintegral_const_mul]
    fun_prop
  have hsecond : ∀ᵐ y ∂muB, ∀ᵐ z ∂muC,
      densitySecondConditioning muA d (y, z) =
        (∫⁻ x, a (x, z) ∂muA) * b (y, z) := by
    filter_upwards [habBCA] with y hy
    filter_upwards [hy] with z hz
    change (∫⁻ x, d (x, (y, z)) ∂muA) = _
    rw [lintegral_congr_ae hz, lintegral_mul_const]
    fun_prop
  have hfirstCA : ∀ᵐ z ∂muC, ∀ᵐ x ∂muA,
      densityFirstConditioning muB d (x, z) =
        a (x, z) * ∫⁻ y, b (y, z) ∂muB := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact hfirst
  have hcond : ∀ᵐ z ∂muC,
      densityConditioning muA muB d z =
        (∫⁻ x, a (x, z) ∂muA) * (∫⁻ y, b (y, z) ∂muB) := by
    filter_upwards [hfirstCA] with z hz
    have hz' : (fun x ↦ ∫⁻ y, d (x, (y, z)) ∂muB) =ᵐ[muA]
        (fun x ↦ a (x, z) * ∫⁻ y, b (y, z) ∂muB) := by
      filter_upwards [hz] with x hx
      exact hx
    change (∫⁻ x, ∫⁻ y, d (x, (y, z)) ∂muB ∂muA) = _
    rw [lintegral_congr_ae hz', lintegral_mul_const]
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [habABC, hfirst] with x hxy hxfirst
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hxy, hsecond] with y hyz hysecond
  filter_upwards [hyz, hxfirst, hysecond, hcond] with z hdab hfirstz hsecondz hcondz
  rw [hdab, hfirstz, hsecondz, hcondz]
  ac_rfl

/-- For a measurable finite three-block density, the cross-multiplied conditional-density
identity yields a measurable product factorization given the third block. -/
theorem threeBlockFactors_of_densityIdentity (hd : Measurable d)
    (hid : ThreeBlockDensityIdentity muA muB muC d) :
    ThreeBlockFactors muA muB muC d := by
  /- Use `densityFirstConditioning muB d` as the first factor and the ratio of
  `densitySecondConditioning muA d` to `densityConditioning muA muB d` as the second.  On fibres
  where the conditioning marginal vanishes, Tonelli implies that `d` vanishes almost everywhere;
  on the remaining fibres, finiteness permits cancellation in the density identity. -/
  let dAC := densityFirstConditioning muB d
  let dBC := densitySecondConditioning muA d
  let dC := densityConditioning muA muB d
  have hdAC : Measurable dAC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (A × C) × B ↦ d (q.1.1, (q.2, q.1.2)))
    fun_prop
  have hdBC : Measurable dBC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (B × C) × A ↦ d (q.2, (q.1.1, q.1.2)))
    fun_prop
  have hdC : Measurable dC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB)
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (C × A) × B ↦ d (q.1.2, (q.2, q.1.1)))
    fun_prop
  have hdInt : ∫⁻ q, d q ∂threeBlockReference muA muB muC ≠ ∞ := by
    have h := measure_ne_top
      ((threeBlockReference muA muB muC).withDensity d) Set.univ
    simpa [withDensity_apply] using h
  have htotal : (∫⁻ c, dC c ∂muC) =
      ∫⁻ q, d q ∂threeBlockReference muA muB muC := by
    change (∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA ∂muC) = _
    rw [← lintegral_prod
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    rw [lintegral_prod_symm
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    change _ = ∫⁻ q, d q ∂muA.prod (muB.prod muC)
    rw [lintegral_prod d hd.aemeasurable]
    apply lintegral_congr
    intro a
    rw [← lintegral_prod (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [lintegral_prod_symm (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [← lintegral_prod (fun q : B × C ↦ d (a, q)) (by fun_prop)]
  have hdCInt : ∫⁻ c, dC c ∂muC ≠ ∞ := by
    rwa [htotal]
  have hdCFinite : ∀ᵐ c ∂muC, dC c < ∞ := ae_lt_top hdC hdCInt
  have hzeroC : ∀ᵐ c ∂muC, ∀ᵐ a ∂muA, ∀ᵐ b ∂muB,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 := by
    refine ae_of_all muC fun c ↦ ?_
    by_cases hc : dC c = 0
    · have hACzero : (fun a ↦ dAC (a, c)) =ᵐ[muA] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dC, dAC, densityConditioning, densityFirstConditioning] using hc
      filter_upwards [hACzero] with a ha0
      change dAC (a, c) = 0 at ha0
      have hdzero : (fun b ↦ d (a, (b, c))) =ᵐ[muB] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dAC, densityFirstConditioning] using ha0
      filter_upwards [hdzero] with b hb0
      exact fun _ ↦ ⟨ha0, hb0⟩
    · exact ae_of_all muA fun _ ↦ ae_of_all muB fun _ h ↦ (hc h).elim
  have hzeroFlat : ∀ᵐ q ∂muC.prod (muA.prod muB),
      dC q.1 = 0 → dAC (q.2.1, q.1) = 0 ∧ d (q.2.1, (q.2.2, q.1)) = 0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hzeroC] with c hc
    exact (Measure.ae_prod_iff_ae_ae (by measurability)).2 hc
  have hzeroSwap : ∀ᵐ ab ∂muA.prod muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (ab.1, c) = 0 ∧ d (ab.1, (ab.2, c)) = 0 := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact Measure.ae_ae_of_ae_prod hzeroFlat
  have hzeroABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 := by
    exact Measure.ae_ae_of_ae_prod hzeroSwap
  have hidABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
      d (a, (b, c)) * dC c = dAC (a, c) * dBC (b, c) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hid] with a ha
    exact Measure.ae_ae_of_ae_prod ha
  refine ⟨dAC, fun bc ↦ dBC bc / dC bc.2, hdAC, hdBC.div (hdC.comp measurable_snd), ?_⟩
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hidABC, hzeroABC] with a ha hza
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ha, hza] with b hb hzb
  filter_upwards [hb, hzb, hdCFinite] with c hidc hzc hfin
  by_cases hc0 : dC c = 0
  · rw [(hzc hc0).2, (hzc hc0).1]
    simp
  · symm
    calc
      dAC (a, c) * (dBC (b, c) / dC c) =
          (dAC (a, c) * dBC (b, c)) / dC c := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ = (d (a, (b, c)) * dC c) / dC c := by rw [hidc]
      _ = d (a, (b, c)) := ENNReal.mul_div_cancel_right hc0 hfin.ne

/-- [Three sigma-finite reference measures](hyp:muA,muB,muC) and [a measurable density](hyp:hd)
[make conditional product factorization equivalent to the cross-multiplied identity of its three
marginal densities](goal). -/
theorem threeBlockFactors_iff_densityIdentity (hd : Measurable d) :
    ThreeBlockFactors muA muB muC d ↔ ThreeBlockDensityIdentity muA muB muC d :=
  ⟨threeBlockDensityIdentity_of_factors muA muB muC hd,
    threeBlockFactors_of_densityIdentity muA muB muC hd⟩

end DensityFactorization

section ConditionalIndependence

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
variable [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
variable (muA : Measure A) (muB : Measure B) (muC : Measure C)
variable [SigmaFinite muA] [SigmaFinite muB] [SigmaFinite muC]
variable {d : ThreeBlock A B C → ℝ≥0∞}
variable [IsFiniteMeasure ((threeBlockReference muA muB muC).withDensity d)]

private theorem map_thirdFirst_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (fun q ↦ (thirdThreeCoord q, firstThreeCoord q)) =
      (muC.prod muA).withDensity
        (fun ca ↦ densityFirstConditioning muB d (ca.2, ca.1)) := by
  have hmarg : Measurable
      (fun ca : C × A ↦ densityFirstConditioning muB d (ca.2, ca.1)) := by
    unfold densityFirstConditioning
    fun_prop
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [lintegral_map hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hmarg hg,
    lintegral_prod _ (by fun_prop)]
  change (∫⁻ q : A × (B × C), d q * g (q.2.2, q.1) ∂muA.prod (muB.prod muC)) =
    ∫⁻ c, ∫⁻ a, (∫⁻ b, d (a, (b, c)) ∂muB) * g (c, a) ∂muA ∂muC
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, d (a, (b, c)) * g (c, a) ∂muC ∂muB ∂muA := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, d (a, (b, c)) * g (c, a) ∂muB ∂muC ∂muA := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) * g (c, a) ∂muB ∂muA ∂muC := by
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro c
      apply lintegral_congr
      intro a
      rw [lintegral_mul_const (g (c, a)) (by fun_prop)]

private theorem map_thirdSecond_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (fun q ↦ (thirdThreeCoord q, secondThreeCoord q)) =
      (muC.prod muB).withDensity
        (fun cb ↦ densitySecondConditioning muA d (cb.2, cb.1)) := by
  have hmarg : Measurable
      (fun cb : C × B ↦ densitySecondConditioning muA d (cb.2, cb.1)) := by
    unfold densitySecondConditioning
    fun_prop
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [lintegral_map hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hmarg hg,
    lintegral_prod _ (by fun_prop)]
  change (∫⁻ q : A × (B × C), d q * g (q.2.2, q.2.1) ∂muA.prod (muB.prod muC)) =
    ∫⁻ c, ∫⁻ b, (∫⁻ a, d (a, (b, c)) ∂muA) * g (c, b) ∂muB ∂muC
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, d (a, (b, c)) * g (c, b) ∂muC ∂muB ∂muA := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, d (a, (b, c)) * g (c, b) ∂muB ∂muC ∂muA := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) * g (c, b) ∂muB ∂muA ∂muC := by
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ c, ∫⁻ b, ∫⁻ a, d (a, (b, c)) * g (c, b) ∂muA ∂muB ∂muC := by
      apply lintegral_congr
      intro c
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro c
      apply lintegral_congr
      intro b
      rw [lintegral_mul_const (g (c, b)) (by fun_prop)]

private theorem exists_normalizedKernel
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    (muX : Measure X) [SigmaFinite muX]
    (f : C × X → ℝ≥0∞) (z : C → ℝ≥0∞)
    (hf : Measurable f) (hz : Measurable z)
    (hmass : ∀ c, ∫⁻ x, f (c, x) ∂muX = z c)
    [IsFiniteMeasure (muC.withDensity z)] :
    ∃ κ : Kernel C X, IsMarkovKernel κ ∧
      muC.withDensity z ⊗ₘ κ = (muC.prod muX).withDensity f ∧
      κ =ᵐ[muC.withDensity z]
        fun c ↦ muX.withDensity (fun x ↦ f (c, x) / z c) := by
  let good : Set C := {c | z c ≠ 0 ∧ z c ≠ ∞}
  have hgood : MeasurableSet good := by
    exact ((hz (measurableSet_singleton 0)).compl.inter
      (hz (measurableSet_singleton ∞)).compl)
  let fallback : Kernel C X := Kernel.const C (Measure.dirac (Classical.choice inferInstance))
  have hraw : Measurable
      (fun c ↦ muX.withDensity (fun x ↦ f (c, x) / z c)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [withDensity_apply _ hs]
    fun_prop
  let κ : Kernel C X :=
    ⟨fun c ↦ if c ∈ good then muX.withDensity (fun x ↦ f (c, x) / z c) else fallback c,
      hraw.piecewise hgood fallback.measurable⟩
  have hκ_markov : IsMarkovKernel κ := by
    refine ⟨fun c ↦ ⟨?_⟩⟩
    change (if c ∈ good then muX.withDensity (fun x ↦ f (c, x) / z c)
      else fallback c) Set.univ = 1
    split_ifs with hc
    · rw [withDensity_apply' _ Set.univ, Measure.restrict_univ]
      simp only [ENNReal.div_eq_inv_mul]
      rw [lintegral_const_mul, hmass c, ENNReal.inv_mul_cancel hc.1 hc.2]
      fun_prop
    · simp [fallback]
  letI : IsMarkovKernel κ := hκ_markov
  have hzInt : ∫⁻ c, z c ∂muC ≠ ∞ := by
    have h := measure_ne_top (muC.withDensity z) Set.univ
    simpa [withDensity_apply] using h
  have hzFinite : ∀ᵐ c ∂muC, z c ≠ ∞ :=
    (ae_lt_top hz hzInt).mono fun _ h ↦ h.ne
  have hgood_ae : ∀ᵐ c ∂muC.withDensity z, c ∈ good := by
    rw [ae_withDensity_iff hz]
    filter_upwards [hzFinite] with c hcTop hc0
    exact ⟨hc0, hcTop⟩
  have hκ_ae : κ =ᵐ[muC.withDensity z]
      fun c ↦ muX.withDensity (fun x ↦ f (c, x) / z c) := by
    filter_upwards [hgood_ae] with c hc
    change (if c ∈ good then _ else _) = _
    rw [if_pos hc]
  refine ⟨κ, hκ_markov, ?_, hκ_ae⟩
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [Measure.lintegral_compProd hg, lintegral_withDensity_eq_lintegral_mul _ hz (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hf hg, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hzFinite] with c hcTop
  by_cases hc0 : z c = 0
  · have hfzero : (fun x ↦ f (c, x)) =ᵐ[muX] 0 := by
      apply (lintegral_eq_zero_iff (hf.comp (measurable_const.prodMk measurable_id))).1
      simpa only [Function.comp_apply, id_eq, hmass c] using hc0
    have hright : (∫⁻ x, f (c, x) * g (c, x) ∂muX) = 0 := by
      apply (lintegral_eq_zero_iff (by fun_prop)).2
      filter_upwards [hfzero] with x hx
      simp [hx]
    change z c * (∫⁻ x, g (c, x) ∂κ c) = ∫⁻ x, f (c, x) * g (c, x) ∂muX
    rw [hc0, zero_mul, hright]
  · have hcgood : c ∈ good := ⟨hc0, hcTop⟩
    change z c * ∫⁻ x, g (c, x) ∂(if c ∈ good then _ else _) = _
    rw [if_pos hcgood, lintegral_withDensity_eq_lintegral_mul]
    swap
    · exact (hf.comp (measurable_const.prodMk measurable_id)).div measurable_const
    swap
    · fun_prop
    rw [← lintegral_const_mul]
    swap
    · fun_prop
    apply lintegral_congr_ae
    have hflt : ∀ᵐ x ∂muX, f (c, x) ≠ ∞ := by
      exact (ae_lt_top (hf.comp (measurable_const.prodMk measurable_id))
        (by simpa only [Function.comp_apply, id_eq, hmass c] using hcTop)).mono fun _ h ↦ h.ne
    filter_upwards [hflt] with x hxTop
    change z c * ((f (c, x) / z c) * g (c, x)) = f (c, x) * g (c, x)
    rw [ENNReal.div_eq_inv_mul, mul_assoc, ENNReal.mul_inv_cancel_left hc0 hcTop]

private theorem compProd_prod_normalized
    (fA : C × A → ℝ≥0∞) (fB : C × B → ℝ≥0∞) (z : C → ℝ≥0∞)
    (hfA : Measurable fA) (hfB : Measurable fB) (hz : Measurable z)
    (hmassA : ∀ c, ∫⁻ a, fA (c, a) ∂muA = z c)
    (hmassB : ∀ c, ∫⁻ b, fB (c, b) ∂muB = z c)
    (κA : Kernel C A) (κB : Kernel C B) [IsMarkovKernel κA] [IsMarkovKernel κB]
    (hκA : κA =ᵐ[muC.withDensity z]
      fun c ↦ muA.withDensity (fun a ↦ fA (c, a) / z c))
    (hκB : κB =ᵐ[muC.withDensity z]
      fun c ↦ muB.withDensity (fun b ↦ fB (c, b) / z c))
    [IsFiniteMeasure (muC.withDensity z)] :
    muC.withDensity z ⊗ₘ (κA ×ₖ κB) =
      (muC.prod (muA.prod muB)).withDensity
        (fun q ↦ fA (q.1, q.2.1) * fB (q.1, q.2.2) / z q.1) := by
  have hzInt : ∫⁻ c, z c ∂muC ≠ ∞ := by
    have h := measure_ne_top (muC.withDensity z) Set.univ
    simpa [withDensity_apply] using h
  have hzFinite : ∀ᵐ c ∂muC, z c ≠ ∞ :=
    (ae_lt_top hz hzInt).mono fun _ h ↦ h.ne
  have hκA' : ∀ᵐ c ∂muC, z c ≠ 0 →
      κA c = muA.withDensity (fun a ↦ fA (c, a) / z c) := by
    exact (ae_withDensity_iff hz).1 hκA
  have hκB' : ∀ᵐ c ∂muC, z c ≠ 0 →
      κB c = muB.withDensity (fun b ↦ fB (c, b) / z c) := by
    exact (ae_withDensity_iff hz).1 hκB
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [Measure.lintegral_compProd hg,
    lintegral_withDensity_eq_lintegral_mul _ hz (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hzFinite, hκA', hκB'] with c hcTop hcA hcB
  by_cases hc0 : z c = 0
  · have hAzero : (fun a ↦ fA (c, a)) =ᵐ[muA] 0 := by
      apply (lintegral_eq_zero_iff (by fun_prop)).1
      rw [hmassA c, hc0]
    have hBzero : (fun b ↦ fB (c, b)) =ᵐ[muB] 0 := by
      apply (lintegral_eq_zero_iff (by fun_prop)).1
      rw [hmassB c, hc0]
    change z c * (∫⁻ ab, g (c, ab) ∂(κA ×ₖ κB) c) =
      ∫⁻ ab, (fA (c, ab.1) * fB (c, ab.2) / z c) * g (c, ab) ∂muA.prod muB
    rw [hc0, zero_mul]
    symm
    apply (lintegral_eq_zero_iff (by fun_prop)).2
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hAzero] with a ha
    filter_upwards [hBzero] with b hb
    simp [ha, hb]
  · change z c * (∫⁻ ab, g (c, ab) ∂(κA ×ₖ κB) c) = _
    rw [Kernel.prod_apply, hcA hc0, hcB hc0, prod_withDensity]
    swap
    · fun_prop
    swap
    · fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul]
    swap
    · fun_prop
    swap
    · fun_prop
    rw [← lintegral_const_mul]
    swap
    · fun_prop
    apply lintegral_congr_ae
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    apply ae_of_all
    intro a
    apply ae_of_all
    intro b
    change z c * ((fA (c, a) / z c * (fB (c, b) / z c)) * g (c, (a, b))) =
      (fA (c, a) * fB (c, b) / z c) * g (c, (a, b))
    simp only [ENNReal.div_eq_inv_mul]
    calc
      z c * ((z c)⁻¹ * fA (c, a) * ((z c)⁻¹ * fB (c, b)) * g (c, (a, b))) =
          (z c * ((z c)⁻¹ * fA (c, a))) * ((z c)⁻¹ * fB (c, b)) *
            g (c, (a, b)) := by ac_rfl
      _ = fA (c, a) * ((z c)⁻¹ * fB (c, b)) * g (c, (a, b)) := by
        rw [ENNReal.mul_inv_cancel_left hc0 hcTop]
      _ = (z c)⁻¹ * (fA (c, a) * fB (c, b)) * g (c, (a, b)) := by ac_rfl

private theorem condIndepFun_threeBlock_iff_ratio_reordered [Nonempty A] [Nonempty B]
    (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
        measurable_thirdThreeCoord.comap_le
        (@firstThreeCoord A B C) (@secondThreeCoord A B C)
        ((threeBlockReference muA muB muC).withDensity d) ↔
      (fun q : C × (A × B) ↦ d (q.2.1, (q.2.2, q.1))) =ᵐ[muC.prod (muA.prod muB)]
        fun q ↦ densityFirstConditioning muB d (q.2.1, q.1) *
          densitySecondConditioning muA d (q.2.2, q.1) /
            densityConditioning muA muB d q.1 := by
  let P := (threeBlockReference muA muB muC).withDensity d
  let z := densityConditioning muA muB d
  let fA : C × A → ℝ≥0∞ := fun q ↦ densityFirstConditioning muB d (q.2, q.1)
  let fB : C × B → ℝ≥0∞ := fun q ↦ densitySecondConditioning muA d (q.2, q.1)
  have hz : Measurable z := by
    unfold z densityConditioning
    fun_prop
  have hfA : Measurable fA := by
    unfold fA densityFirstConditioning
    fun_prop
  have hfB : Measurable fB := by
    unfold fB densitySecondConditioning
    fun_prop
  have hmassA : ∀ c, ∫⁻ a, fA (c, a) ∂muA = z c := by
    intro c
    rfl
  have hmassB : ∀ c, ∫⁻ b, fB (c, b) ∂muB = z c := by
    intro c
    change (∫⁻ b, ∫⁻ a, d (a, (b, c)) ∂muA ∂muB) =
      ∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA
    exact lintegral_lintegral_swap (by fun_prop)
  have hPmapC : P.map (@thirdThreeCoord A B C) = muC.withDensity z := by
    exact map_thirdThreeCoord_withDensity muA muB muC hd
  letI : IsFiniteMeasure (muC.withDensity z) := by
    rw [← hPmapC]
    infer_instance
  obtain ⟨κA, hκAmarkov, hκAcomp, hκA⟩ :=
    exists_normalizedKernel muC muA fA z hfA hz hmassA
  obtain ⟨κB, hκBmarkov, hκBcomp, hκB⟩ :=
    exists_normalizedKernel muC muB fB z hfB hz hmassB
  letI : IsMarkovKernel κA := hκAmarkov
  letI : IsMarkovKernel κB := hκBmarkov
  let condA := condDistrib (@firstThreeCoord A B C) (@thirdThreeCoord A B C) P
  let condB := condDistrib (@secondThreeCoord A B C) (@thirdThreeCoord A B C) P
  have hcondAcomp : muC.withDensity z ⊗ₘ condA = muC.withDensity z ⊗ₘ κA := by
    calc
      muC.withDensity z ⊗ₘ condA =
          P.map (fun q ↦ (thirdThreeCoord q, firstThreeCoord q)) := by
        rw [← hPmapC]
        exact compProd_map_condDistrib measurable_firstThreeCoord.aemeasurable
      _ = (muC.prod muA).withDensity fA := by
        exact map_thirdFirst_withDensity muA muB muC hd
      _ = muC.withDensity z ⊗ₘ κA := hκAcomp.symm
  have hcondBcomp : muC.withDensity z ⊗ₘ condB = muC.withDensity z ⊗ₘ κB := by
    calc
      muC.withDensity z ⊗ₘ condB =
          P.map (fun q ↦ (thirdThreeCoord q, secondThreeCoord q)) := by
        rw [← hPmapC]
        exact compProd_map_condDistrib measurable_secondThreeCoord.aemeasurable
      _ = (muC.prod muB).withDensity fB := by
        exact map_thirdSecond_withDensity muA muB muC hd
      _ = muC.withDensity z ⊗ₘ κB := hκBcomp.symm
  have hcondA : condA =ᵐ[muC.withDensity z] κA :=
    Kernel.ae_eq_of_compProd_eq hcondAcomp
  have hcondB : condB =ᵐ[muC.withDensity z] κB :=
    Kernel.ae_eq_of_compProd_eq hcondBcomp
  have hcondProd : condA ×ₖ condB =ᵐ[muC.withDensity z] κA ×ₖ κB := by
    filter_upwards [hcondA, hcondB] with c hcA hcB
    rw [Kernel.prod_apply, Kernel.prod_apply, hcA, hcB]
  have hprod : muC.withDensity z ⊗ₘ (κA ×ₖ κB) =
      (muC.prod (muA.prod muB)).withDensity
        (fun q ↦ fA (q.1, q.2.1) * fB (q.1, q.2.2) / z q.1) :=
    compProd_prod_normalized muA muB muC fA fB z hfA hfB hz hmassA hmassB
      κA κB hκA hκB
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    measurable_firstThreeCoord measurable_secondThreeCoord measurable_thirdThreeCoord]
  rw [← Measure.compProd_eq_comp_prod, hPmapC, Measure.compProd_congr hcondProd, hprod,
    map_thirdFirstSecond_withDensity muA muB muC hd]
  exact withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)

private theorem condIndepFun_threeBlock_iff_ratio [Nonempty A] [Nonempty B]
    (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
        measurable_thirdThreeCoord.comap_le
        (@firstThreeCoord A B C) (@secondThreeCoord A B C)
        ((threeBlockReference muA muB muC).withDensity d) ↔
      d =ᵐ[threeBlockReference muA muB muC]
        fun q ↦ densityFirstConditioning muB d (q.1, q.2.2) *
          densitySecondConditioning muA d (q.2.1, q.2.2) /
            densityConditioning muA muB d q.2.2 := by
  let e : ThreeBlock A B C ≃ᵐ C × (A × B) :=
    MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (threeBlockReference muA muB muC)
      (muC.prod (muA.prod muB)) := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map e (muA.prod (muB.prod muC)) = muC.prod (muA.prod muB)
    calc
      Measure.map e (muA.prod (muB.prod muC)) =
          Measure.map Prod.swap
            (Measure.map MeasurableEquiv.prodAssoc.symm (muA.prod (muB.prod muC))) := by
        rw [Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.symm.measurable]
        rfl
      _ = muC.prod (muA.prod muB) := by
        rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map, Measure.prod_swap]
  rw [condIndepFun_threeBlock_iff_ratio_reordered muA muB muC hd]
  constructor
  · intro h
    have hc := he.quasiMeasurePreserving.ae_eq_comp h
    have hleft : (fun q : C × (A × B) ↦ d (q.2.1, (q.2.2, q.1))) ∘ e = d := by
      funext q
      rfl
    have hright :
        (fun q : C × (A × B) ↦ densityFirstConditioning muB d (q.2.1, q.1) *
          densitySecondConditioning muA d (q.2.2, q.1) /
            densityConditioning muA muB d q.1) ∘ e =
        fun q ↦ densityFirstConditioning muB d (q.1, q.2.2) *
          densitySecondConditioning muA d (q.2.1, q.2.2) /
            densityConditioning muA muB d q.2.2 := by
      funext q
      rfl
    rwa [hleft, hright] at hc
  · intro h
    have hc := (he.symm e).quasiMeasurePreserving.ae_eq_comp h
    have hleft : d ∘ e.symm = fun q : C × (A × B) ↦ d (q.2.1, (q.2.2, q.1)) := by
      funext q
      rfl
    have hright :
        (fun q ↦ densityFirstConditioning muB d (q.1, q.2.2) *
          densitySecondConditioning muA d (q.2.1, q.2.2) /
            densityConditioning muA muB d q.2.2) ∘ e.symm =
        fun q : C × (A × B) ↦ densityFirstConditioning muB d (q.2.1, q.1) *
          densitySecondConditioning muA d (q.2.2, q.1) /
            densityConditioning muA muB d q.1 := by
      funext q
      rfl
    rwa [hleft, hright] at hc

private theorem threeBlockDensityIdentity_iff_ratio (hd : Measurable d) :
    ThreeBlockDensityIdentity muA muB muC d ↔
      d =ᵐ[threeBlockReference muA muB muC]
        fun q ↦ densityFirstConditioning muB d (q.1, q.2.2) *
          densitySecondConditioning muA d (q.2.1, q.2.2) /
            densityConditioning muA muB d q.2.2 := by
  let dAC := densityFirstConditioning muB d
  let dBC := densitySecondConditioning muA d
  let dC := densityConditioning muA muB d
  have hdAC : Measurable dAC := by
    unfold dAC densityFirstConditioning
    fun_prop
  have hdBC : Measurable dBC := by
    unfold dBC densitySecondConditioning
    fun_prop
  have hdC : Measurable dC := by
    unfold dC densityConditioning
    fun_prop
  have hdInt : ∫⁻ q, d q ∂threeBlockReference muA muB muC ≠ ∞ := by
    have h := measure_ne_top
      ((threeBlockReference muA muB muC).withDensity d) Set.univ
    simpa [withDensity_apply] using h
  have htotal : (∫⁻ c, dC c ∂muC) =
      ∫⁻ q, d q ∂threeBlockReference muA muB muC := by
    change (∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA ∂muC) = _
    rw [← lintegral_prod
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    rw [lintegral_prod_symm
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    change _ = ∫⁻ q, d q ∂muA.prod (muB.prod muC)
    rw [lintegral_prod d hd.aemeasurable]
    apply lintegral_congr
    intro a
    rw [← lintegral_prod (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [lintegral_prod_symm (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [← lintegral_prod (fun q : B × C ↦ d (a, q)) (by fun_prop)]
  have hdCFinite : ∀ᵐ c ∂muC, dC c < ∞ := by
    apply ae_lt_top hdC
    rwa [htotal]
  have hzeroC : ∀ᵐ c ∂muC, ∀ᵐ a ∂muA, ∀ᵐ b ∂muB,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 := by
    refine ae_of_all muC fun c ↦ ?_
    by_cases hc : dC c = 0
    · have hACzero : (fun a ↦ dAC (a, c)) =ᵐ[muA] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dC, dAC, densityConditioning, densityFirstConditioning] using hc
      filter_upwards [hACzero] with a ha0
      change dAC (a, c) = 0 at ha0
      have hdzero : (fun b ↦ d (a, (b, c))) =ᵐ[muB] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dAC, densityFirstConditioning] using ha0
      filter_upwards [hdzero] with b hb0
      exact fun _ ↦ ⟨ha0, hb0⟩
    · exact ae_of_all muA fun _ ↦ ae_of_all muB fun _ h ↦ (hc h).elim
  have hzeroFlat : ∀ᵐ q ∂muC.prod (muA.prod muB),
      dC q.1 = 0 → dAC (q.2.1, q.1) = 0 ∧ d (q.2.1, (q.2.2, q.1)) = 0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hzeroC] with c hc
    exact (Measure.ae_prod_iff_ae_ae (by measurability)).2 hc
  have hzeroSwap : ∀ᵐ ab ∂muA.prod muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (ab.1, c) = 0 ∧ d (ab.1, (ab.2, c)) = 0 := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact Measure.ae_ae_of_ae_prod hzeroFlat
  have hzeroABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 :=
    Measure.ae_ae_of_ae_prod hzeroSwap
  constructor
  · intro hid
    have hidABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
        d (a, (b, c)) * dC c = dAC (a, c) * dBC (b, c) := by
      filter_upwards [Measure.ae_ae_of_ae_prod hid] with a ha
      exact Measure.ae_ae_of_ae_prod ha
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hidABC, hzeroABC] with a ha hza
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [ha, hza] with b hb hzb
    filter_upwards [hb, hzb, hdCFinite] with c hidc hzc hfin
    change d (a, (b, c)) = dAC (a, c) * dBC (b, c) / dC c
    by_cases hc0 : dC c = 0
    · rw [(hzc hc0).2, (hzc hc0).1]
      simp
    · calc
        d (a, (b, c)) = (d (a, (b, c)) * dC c) / dC c := by
          rw [ENNReal.mul_div_cancel_right hc0 hfin.ne]
        _ = (dAC (a, c) * dBC (b, c)) / dC c := by rw [hidc]
  · intro hratio
    have hratioABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
        d (a, (b, c)) = dAC (a, c) * dBC (b, c) / dC c := by
      filter_upwards [Measure.ae_ae_of_ae_prod hratio] with a ha
      exact Measure.ae_ae_of_ae_prod ha
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hratioABC, hzeroABC] with a ha hza
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [ha, hza] with b hb hzb
    filter_upwards [hb, hzb, hdCFinite] with c hratioC hzc hfin
    change d (a, (b, c)) * dC c = dAC (a, c) * dBC (b, c)
    by_cases hc0 : dC c = 0
    · rw [(hzc hc0).2, (hzc hc0).1, hc0]
      simp
    · rw [hratioC]
      exact ENNReal.div_mul_cancel hc0 hfin.ne
/-- Conditional independence of the first two coordinates given the third coordinate implies
the cross-multiplied identity for any measurable finite density relative to a product reference. -/
theorem threeBlockDensityIdentity_of_condIndepFun (hd : Measurable d)
    (hci : CondIndepFun
      (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
      measurable_thirdThreeCoord.comap_le
      (@firstThreeCoord A B C) (@secondThreeCoord A B C)
      ((threeBlockReference muA muB muC).withDensity d)) :
    ThreeBlockDensityIdentity muA muB muC d := by
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI := hA
      exact ae_of_all _ fun q ↦ isEmptyElim q.1
  | inr hA =>
      letI := hA
      cases isEmpty_or_nonempty B with
      | inl hB =>
          letI := hB
          exact ae_of_all _ fun q ↦ isEmptyElim q.2.1
      | inr hB =>
          letI := hB
          exact (threeBlockDensityIdentity_iff_ratio muA muB muC hd).2
            ((condIndepFun_threeBlock_iff_ratio muA muB muC hd).1 hci)

/-- The cross-multiplied identity for a measurable finite product density implies conditional
independence of the first two coordinates given the third coordinate. -/
theorem condIndepFun_threeBlock_of_densityIdentity (hd : Measurable d)
    (hid : ThreeBlockDensityIdentity muA muB muC d) :
    CondIndepFun
      (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
      measurable_thirdThreeCoord.comap_le
      (@firstThreeCoord A B C) (@secondThreeCoord A B C)
      ((threeBlockReference muA muB muC).withDensity d) := by
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI := hA
      rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
        measurable_firstThreeCoord measurable_secondThreeCoord]
      intro s t hs ht
      exact ae_of_all _ fun q ↦ isEmptyElim q.1
  | inr hA =>
      letI := hA
      cases isEmpty_or_nonempty B with
      | inl hB =>
          letI := hB
          rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
            measurable_firstThreeCoord measurable_secondThreeCoord]
          intro s t hs ht
          exact ae_of_all _ fun q ↦ isEmptyElim q.2.1
      | inr hB =>
          letI := hB
          exact (condIndepFun_threeBlock_iff_ratio muA muB muC hd).2
            ((threeBlockDensityIdentity_iff_ratio muA muB muC hd).1 hid)

/-- For a measurable finite density over a three-fold product reference, conditional independence
of the first two coordinates given the third is equivalent to the marginal-density identity. -/
theorem condIndepFun_threeBlock_iff_densityIdentity (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
        measurable_thirdThreeCoord.comap_le
        (@firstThreeCoord A B C) (@secondThreeCoord A B C)
        ((threeBlockReference muA muB muC).withDensity d) ↔
      ThreeBlockDensityIdentity muA muB muC d :=
  ⟨threeBlockDensityIdentity_of_condIndepFun muA muB muC hd,
    condIndepFun_threeBlock_of_densityIdentity muA muB muC hd⟩

/-- [Three sigma-finite reference measures](hyp:muA,muB,muC) and [a measurable density](hyp:hd)
[make conditional independence of the first two blocks given the third equivalent to measurable
conditional product factorization](goal). -/
theorem condIndepFun_threeBlock_iff_factors (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
        measurable_thirdThreeCoord.comap_le
        (@firstThreeCoord A B C) (@secondThreeCoord A B C)
        ((threeBlockReference muA muB muC).withDensity d) ↔
      ThreeBlockFactors muA muB muC d := by
  rw [condIndepFun_threeBlock_iff_densityIdentity muA muB muC hd,
    threeBlockFactors_iff_densityIdentity muA muB muC hd]

end ConditionalIndependence

end Causalean.Mathlib.CondIndep.PositiveDensityIntersection

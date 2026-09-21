/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
public import Causalean.Mathlib.MeasureTheory.WithDensityInverse
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.WithDensity

/-! # Reciprocal tilts with Bernoulli marks

This file constructs a measurable Boolean Bernoulli mark over a base space and proves the
measure identities behind reciprocal-probability tilting.  The first marginal is the tilted
base law, the success and failure restrictions recover their density formulas, the mark has
the prescribed conditional mean, and measurable pushforwards of the success restriction are
transported back to the original base law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

@[expose] public section

namespace Causalean.Mathlib.Probability

/-- Given [a real-valued weight on a measurable space](hyp:h), the [Boolean Bernoulli-mark
kernel](goal) has success weight `max(h(a), 0)` and failure weight `max(1-h(a), 0)` at `a`.
For measurable unit-interval weights its fibers are Bernoulli probability measures. -/
noncomputable def bernoulliMarkKernel
    {α : Type*} [MeasurableSpace α] (h : α → ℝ) : Kernel α Bool :=
  Kernel.withDensity
    (Kernel.const α (Measure.dirac true + Measure.dirac false))
    (fun a z => if z then ENNReal.ofReal (h a) else ENNReal.ofReal (1 - h a))

/-- For [a base measure](hyp:ν₁) and [a real-valued weight](hyp:h), the [reciprocal
tilt](goal) weights each base point by `max(1/h, 0)`. -/
noncomputable def reciprocalTilt
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) (h : α → ℝ) : Measure α :=
  ν₁.withDensity fun a => ENNReal.ofReal (1 / h a)

/-- The [reciprocal tilt of an s-finite base measure](hyp:ν₁) by [any real-valued
weight](hyp:h) [is s-finite](goal). -/
noncomputable instance reciprocalTilt.instSFinite
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [SFinite ν₁] (h : α → ℝ) :
    SFinite (reciprocalTilt ν₁ h) := by
  unfold reciprocalTilt
  infer_instance

/-- For [a base measure](hyp:ν₁) and [a real-valued mark probability](hyp:h), the
[reciprocally tilted Bernoulli-marked law](goal) first draws from the reciprocal tilt and
then draws the Boolean mark with success weight `h`. -/
noncomputable def bernoulliMarkedLaw
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) (h : α → ℝ) : Measure (α × Bool) :=
  reciprocalTilt ν₁ h ⊗ₘ bernoulliMarkKernel h

/-- For [a measurable weight](hyp:h,hh), [the Bernoulli-mark kernel fiber at a base
point](hyp:a) [is the Boolean Bernoulli measure with that point's weight](goal). -/
theorem bernoulliMarkKernel_apply
    {α : Type*} [MeasurableSpace α] (h : α → ℝ) (hh : Measurable h) (a : α) :
    bernoulliMarkKernel h a = bernoulliBool (h a) := by
  rw [bernoulliMarkKernel, Kernel.withDensity_apply]
  · rw [Kernel.const_apply]
    rw [withDensity_add_measure, dirac_withDensity, dirac_withDensity]
    simp [bernoulliBool]
  · exact Measurable.ite (measurable_snd (measurableSet_singleton true))
      (ENNReal.measurable_ofReal.comp (hh.comp measurable_fst))
      (ENNReal.measurable_ofReal.comp
        (measurable_const.sub (hh.comp measurable_fst)))

/-- The [Bernoulli-mark kernel built from a weight](hyp:h) [is s-finite](goal). -/
noncomputable instance bernoulliMarkKernel.instIsSFiniteKernel
    {α : Type*} [MeasurableSpace α] (h : α → ℝ) :
    IsSFiniteKernel (bernoulliMarkKernel h) := by
  unfold bernoulliMarkKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro a z
  split_ifs <;> exact ENNReal.ofReal_ne_top

/-- For [a measurable weight](hyp:h,hh) and [a base point](hyp:a), [the success singleton
has kernel mass `max(h(a),0)`](goal). -/
theorem bernoulliMarkKernel_apply_true
    {α : Type*} [MeasurableSpace α] (h : α → ℝ) (hh : Measurable h) (a : α) :
    bernoulliMarkKernel h a {true} = ENNReal.ofReal (h a) := by
  rw [bernoulliMarkKernel_apply h hh a]
  simp [bernoulliBool]

/-- For [a measurable weight](hyp:h,hh) and [a base point](hyp:a), [the failure singleton
has kernel mass `max(1-h(a),0)`](goal). -/
theorem bernoulliMarkKernel_apply_false
    {α : Type*} [MeasurableSpace α] (h : α → ℝ) (hh : Measurable h) (a : α) :
    bernoulliMarkKernel h a {false} = ENNReal.ofReal (1 - h a) := by
  rw [bernoulliMarkKernel_apply h hh a]
  simp [bernoulliBool]

/-- If [a measurable weight](hyp:h,hh) [lies strictly above zero and at most one almost
everywhere](hyp:hpos,hle) under [a measure](hyp:μ), then [the corresponding Bernoulli-mark
fibers have total mass one almost everywhere](goal). -/
theorem ae_bernoulliMarkKernel_apply_univ_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
    (hh : Measurable h) (hpos : ∀ᵐ a ∂μ, 0 < h a) (hle : ∀ᵐ a ∂μ, h a ≤ 1) :
    ∀ᵐ a ∂μ, bernoulliMarkKernel h a univ = 1 := by
  filter_upwards [hpos, hle] with a ha h'a
  rw [bernoulliMarkKernel_apply h hh a]
  exact @IsProbabilityMeasure.measure_univ Bool _ _
    (bernoulliBool_isProbabilityMeasure ha.le h'a)

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh), and
[strict unit-interval overlap almost everywhere](hyp:hpos,hle), [the first-coordinate
pushforward of the reciprocal-tilt Bernoulli law is the reciprocal tilt](goal). -/
theorem bernoulliMarkedLaw_map_fst
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a) (hle : ∀ᵐ a ∂ν₁, h a ≤ 1) :
    (bernoulliMarkedLaw ν₁ h).map Prod.fst = reciprocalTilt ν₁ h := by
  have hac : reciprocalTilt ν₁ h ≪ ν₁ :=
    withDensity_absolutelyContinuous ν₁ (fun a => ENNReal.ofReal (1 / h a))
  have hmass : ∀ᵐ a ∂reciprocalTilt ν₁ h,
      bernoulliMarkKernel h a univ = 1 :=
    ae_bernoulliMarkKernel_apply_univ_eq_one (reciprocalTilt ν₁ h) h hh
      (hac.ae_le hpos) (hac.ae_le hle)
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  rw [bernoulliMarkedLaw, show Prod.fst ⁻¹' s = s ×ˢ univ by ext p; simp]
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
  calc
    (∫⁻ a in s, bernoulliMarkKernel h a univ ∂reciprocalTilt ν₁ h) =
        ∫⁻ _a in s, (1 : ENNReal) ∂reciprocalTilt ν₁ h := by
      apply setLIntegral_congr_fun_ae hs
      filter_upwards [hmass] with a ha _
      exact ha
    _ = reciprocalTilt ν₁ h s := setLIntegral_one s

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh),
[strict unit-interval overlap almost everywhere](hyp:hpos,hle), and [unit total mass of
the reciprocal tilt](hyp:hcal), [the reciprocal-tilt Bernoulli-marked law is a probability
measure](goal). -/
theorem bernoulliMarkedLaw_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a) (hle : ∀ᵐ a ∂ν₁, h a ≤ 1)
    (hcal : reciprocalTilt ν₁ h univ = 1) :
    IsProbabilityMeasure (bernoulliMarkedLaw ν₁ h) := by
  rw [isProbabilityMeasure_iff]
  calc
    bernoulliMarkedLaw ν₁ h univ =
        (bernoulliMarkedLaw ν₁ h).map Prod.fst univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = reciprocalTilt ν₁ h univ := by
      rw [bernoulliMarkedLaw_map_fst ν₁ h hh hpos hle]
    _ = 1 := hcal

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh), and
[strict positivity almost everywhere](hyp:hpos), [restricting the marked
law to successful marks and then forgetting the mark recovers the base measure](goal). -/
theorem bernoulliMarkedLaw_restrict_true_map_fst
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a) :
    ((bernoulliMarkedLaw ν₁ h).restrict (univ ×ˢ {true})).map Prod.fst = ν₁ := by
  have hcancel :=
    Causalean.Mathlib.MeasureTheory.withDensity_one_div_ofReal_cancel ν₁ h hh hpos
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.restrict_apply (measurable_fst hs)]
  rw [show Prod.fst ⁻¹' s ∩ univ ×ˢ {true} = s ×ˢ {true} by ext p; simp]
  rw [bernoulliMarkedLaw, Measure.compProd_apply_prod hs (measurableSet_singleton true)]
  simp_rw [bernoulliMarkKernel_apply_true h hh]
  rw [← withDensity_apply _ hs]
  change ((ν₁.withDensity fun a => ENNReal.ofReal (1 / h a)).withDensity
    (fun a => ENNReal.ofReal (h a))) s = ν₁ s
  rw [hcancel]

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh), and
[strict unit-interval overlap almost everywhere](hyp:hpos,hle), [restricting the marked
law to failed marks and then forgetting the mark gives the base measure tilted by the
failure odds `(1-h)/h`](goal). -/
theorem bernoulliMarkedLaw_restrict_false_map_fst
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a) (hle : ∀ᵐ a ∂ν₁, h a ≤ 1) :
    ((bernoulliMarkedLaw ν₁ h).restrict (univ ×ˢ {false})).map Prod.fst =
      ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)) := by
  have hfailure :
      (reciprocalTilt ν₁ h).withDensity (fun a => ENNReal.ofReal (1 - h a)) =
        ν₁.withDensity (fun a => ENNReal.ofReal ((1 - h a) / h a)) := by
    unfold reciprocalTilt
    rw [← withDensity_mul ν₁ (by fun_prop) (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [hpos, hle] with a ha h'a
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / h a)]
    congr 1
    field_simp
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.restrict_apply (measurable_fst hs)]
  rw [show Prod.fst ⁻¹' s ∩ univ ×ˢ {false} = s ×ˢ {false} by ext p; simp]
  rw [bernoulliMarkedLaw, Measure.compProd_apply_prod hs (measurableSet_singleton false)]
  simp_rw [bernoulliMarkKernel_apply_false h hh]
  rw [← withDensity_apply _ hs, hfailure]

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh),
[strict unit-interval overlap almost everywhere](hyp:hpos,hle), and [unit total mass of
the reciprocal tilt](hyp:hcal), [the conditional mean of the Boolean mark given the base
coordinate equals the success weight at that coordinate](goal). -/
theorem bernoulliMarkedLaw_condExp_mark
    {α : Type*} [MeasurableSpace α] (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h)
    (hpos : ∀ᵐ a ∂ν₁, 0 < h a) (hle : ∀ᵐ a ∂ν₁, h a ≤ 1)
    (hcal : reciprocalTilt ν₁ h univ = 1) :
    (bernoulliMarkedLaw ν₁ h)[(fun p => if p.2 then (1 : ℝ) else 0) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[bernoulliMarkedLaw ν₁ h]
      fun p => h p.1 := by
  let Q := bernoulliMarkedLaw ν₁ h
  have hprob : IsProbabilityMeasure Q :=
    bernoulliMarkedLaw_isProbabilityMeasure ν₁ h hh hpos hle hcal
  let _ : IsProbabilityMeasure Q := hprob
  have hmap : Q.map Prod.fst = reciprocalTilt ν₁ h :=
    bernoulliMarkedLaw_map_fst ν₁ h hh hpos hle
  have hac : reciprocalTilt ν₁ h ≪ ν₁ :=
    withDensity_absolutelyContinuous ν₁ (fun a => ENNReal.ofReal (1 / h a))
  have hpos_tilt : ∀ᵐ a ∂reciprocalTilt ν₁ h, 0 < h a := hac.ae_le hpos
  have hle_tilt : ∀ᵐ a ∂reciprocalTilt ν₁ h, h a ≤ 1 := hac.ae_le hle
  have hpos_Q : ∀ᵐ p ∂Q, 0 < h p.1 := by
    rw [← hmap] at hpos_tilt
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_const hh)).mp hpos_tilt
  have hle_Q : ∀ᵐ p ∂Q, h p.1 ≤ 1 := by
    rw [← hmap] at hle_tilt
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le hh measurable_const)).mp hle_tilt
  have hY : Integrable (fun p : α × Bool => if p.2 then (1 : ℝ) else 0) Q := by
    apply Integrable.of_bound
      (Measurable.ite (measurable_snd (measurableSet_singleton true))
        measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with p
    cases p.2 <;> simp
  have hm : Integrable (fun p : α × Bool => h p.1) Q := by
    apply Integrable.of_bound (hh.comp measurable_fst).aestronglyMeasurable 1
    filter_upwards [hpos_Q, hle_Q] with p hp hp'
    simpa [Real.norm_eq_abs, abs_of_pos hp] using hp'
  have hm_design : AEStronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
      (fun p : α × Bool => h p.1) Q := by
    exact (hh.comp (comap_measurable Prod.fst)).aestronglyMeasurable
  apply Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
    Q Prod.fst measurable_fst _ _ hY hm hm_design
  intro S hS
  let A : Set (α × Bool) := Prod.fst ⁻¹' S
  let B : Set (α × Bool) := univ ×ˢ {true}
  have hA : MeasurableSet A := measurable_fst hS
  have hB : MeasurableSet B := MeasurableSet.univ.prod (measurableSet_singleton true)
  have hsuccess := bernoulliMarkedLaw_restrict_true_map_fst ν₁ h hh hpos
  have hsuccess_set := congrArg (fun μ : Measure α => μ S) hsuccess
  rw [Measure.map_apply measurable_fst hS,
    Measure.restrict_apply (measurable_fst hS)] at hsuccess_set
  have hleft :
      ∫ p in A, (if p.2 then (1 : ℝ) else 0) ∂Q = ν₁.real S := by
    rw [← integral_indicator hA]
    calc
      ∫ p, A.indicator (fun p => if p.2 then (1 : ℝ) else 0) p ∂Q =
          ∫ p, (A ∩ B).indicator (1 : (α × Bool) → ℝ) p ∂Q := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with p
        rcases p with ⟨a, z⟩
        by_cases hpA : (a, z) ∈ A <;> cases z <;> simp [hpA, A, B]
      _ = Q.real (A ∩ B) := integral_indicator_one (hA.inter hB)
      _ = ν₁.real S := by
        apply congrArg ENNReal.toReal
        simpa [A, B] using hsuccess_set
  have hcancel :=
    Causalean.Mathlib.MeasureTheory.withDensity_one_div_ofReal_cancel ν₁ h hh hpos
  have hright_tilt :
      ∫ a in S, h a ∂reciprocalTilt ν₁ h = ν₁.real S := by
    calc
      ∫ a in S, h a ∂reciprocalTilt ν₁ h =
          ∫ a in S, (ENNReal.ofReal (h a)).toReal • (1 : ℝ)
            ∂reciprocalTilt ν₁ h := by
        apply setIntegral_congr_ae hS
        filter_upwards [hpos_tilt] with a ha
        simp [ENNReal.toReal_ofReal ha.le]
      _ = ∫ _a in S, (1 : ℝ) ∂(reciprocalTilt ν₁ h).withDensity
          (fun a => ENNReal.ofReal (h a)) := by
        symm
        apply setIntegral_withDensity_eq_setIntegral_toReal_smul
          (ENNReal.measurable_ofReal.comp hh) _ _ hS
        filter_upwards [] with a
        exact ENNReal.ofReal_lt_top
      _ = ∫ _a in S, (1 : ℝ) ∂ν₁ := by
        rw [show (reciprocalTilt ν₁ h).withDensity
          (fun a => ENNReal.ofReal (h a)) = ν₁ by
            simpa [reciprocalTilt] using hcancel]
      _ = ν₁.real S := by simp
  have hmap_integral :
      ∫ a in S, h a ∂Q.map Prod.fst = ∫ p in A, h p.1 ∂Q := by
    simpa [A] using setIntegral_map hS hh.aestronglyMeasurable measurable_fst.aemeasurable
  rw [hmap] at hmap_integral
  exact hleft.trans (hmap_integral.symm.trans hright_tilt).symm

/-- For [a finite base measure](hyp:ν₁), [a measurable success weight](hyp:h,hh) that is
[strictly positive almost everywhere](hyp:hpos), and [a measurable statistic of a marked
point](hyp:g,hg), [the statistic's law on successful marks is the pushforward of the base
measure by evaluating that statistic at a successful mark](goal). -/
theorem bernoulliMarkedLaw_map_restrict_true
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν₁ : Measure α) [IsFiniteMeasure ν₁]
    (h : α → ℝ) (hh : Measurable h) (hpos : ∀ᵐ a ∂ν₁, 0 < h a)
    (g : α × Bool → β) (hg : Measurable g) :
    ((bernoulliMarkedLaw ν₁ h).restrict (univ ×ˢ {true})).map g =
      ν₁.map (fun a => g (a, true)) := by
  have hsection : Measurable (fun a => g (a, true)) := by fun_prop
  have hcancel :=
    Causalean.Mathlib.MeasureTheory.withDensity_one_div_ofReal_cancel ν₁ h hh hpos
  ext s hs
  rw [Measure.map_apply hg hs, Measure.map_apply hsection hs]
  rw [Measure.restrict_apply (hs.preimage hg)]
  rw [show g ⁻¹' s ∩ univ ×ˢ {true} =
      ((fun a => g (a, true)) ⁻¹' s) ×ˢ {true} by
        ext ⟨a, z⟩
        cases z <;> simp]
  rw [bernoulliMarkedLaw,
    Measure.compProd_apply_prod (hs.preimage hsection) (measurableSet_singleton true)]
  simp_rw [bernoulliMarkKernel_apply_true h hh]
  rw [← withDensity_apply _ (hs.preimage hsection)]
  change ((ν₁.withDensity fun a => ENNReal.ofReal (1 / h a)).withDensity
    (fun a => ENNReal.ofReal (h a))) ((fun a => g (a, true)) ⁻¹' s) =
      ν₁ ((fun a => g (a, true)) ⁻¹' s)
  rw [hcancel]

end Causalean.Mathlib.Probability

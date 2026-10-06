module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Parameters
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Density comparison of selected three-Bernoulli laws

The existing `selectedLaw_cell` theorem supplies the four conditional cells.
Here a positive cellwise ratio gives a density of one selected law with respect
to another when the base and treatment propensity are common.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- The [cellwise likelihood ratio](goal) at a [selected observation](hyp:z)
compares [two outcome-mean pairs](hyp:q₀,q₁,q₀',q₁') under the
[same treatment propensity](hyp:e). -/
def selectedCellRatio {X : Type u} (e q₀ q₁ q₀' q₁' : X → ℝ)
    (z : SelectedCoord X) : ℝ≥0∞ :=
  ENNReal.ofReal
    (cellMass (e z.1) (q₀ z.1) (q₁ z.1) z.2.1 z.2.2 /
      cellMass (e z.1) (q₀' z.1) (q₁' z.1) z.2.1 z.2.2)

/-- [The first selected law is the second selected law weighted by its
cellwise likelihood ratio](goal) for a [probability base law](hyp:μ),
[measurable propensity and outcome means](hyp:he,hq₀,hq₁,hq₀',hq₁'),
and [uniform interior bounds](hyp:hη0,hηhalf,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Proof route: compare on each measurable base-by-cell rectangle using
`selectedLaw_cell`; positivity permits cancellation of every reference cell
mass. Finish by the four-cell partition, or transport the common counting
measure density through the coordinate swap.
-/
theorem selectedLaw_eq_withDensity {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1 / 2)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    selectedLaw μ e q₀ q₁ =
      (selectedLaw μ e q₀' q₁').withDensity
        (selectedCellRatio e q₀ q₁ q₀' q₁') := by
  let ν : Measure ((Bool × Bool) × X) :=
    ((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ
  let f : ((Bool × Bool) × X) → SelectedCoord X := fun z => (z.2, z.1)
  let r := selectedCellRatio e q₀ q₁ q₀' q₁'
  have hf : Measurable f := by fun_prop
  have hc (p q s : X → ℝ) (hp : Measurable p) (hq : Measurable q)
      (hs : Measurable s) :
      Measurable (fun z : SelectedCoord X =>
        cellMass (p z.1) (q z.1) (s z.1) z.2.1 z.2.2) := by
    unfold cellMass bitMass
    apply Measurable.mul
    · apply Measurable.ite
      · measurability
      · exact hp.comp (by fun_prop)
      · exact measurable_const.sub (hp.comp (by fun_prop))
    · apply Measurable.ite
      · measurability
      · apply Measurable.ite
        · measurability
        · exact hs.comp (by fun_prop)
        · exact hq.comp (by fun_prop)
      · exact measurable_const.sub (by
          apply Measurable.ite
          · measurability
          · exact hs.comp (by fun_prop)
          · exact hq.comp (by fun_prop))
  have hd' : Measurable (selectedDensity e q₀' q₁') := by
    change Measurable (fun z : (Bool × Bool) × X =>
      ENNReal.ofReal (cellMass (e z.2) (q₀' z.2) (q₁' z.2) z.1.1 z.1.2))
    simpa [f, Function.comp_def] using
      (ENNReal.measurable_ofReal.comp (hc e q₀' q₁' he hq₀' hq₁')).comp hf
  have hr : Measurable r := by
    unfold r selectedCellRatio
    exact ENNReal.measurable_ofReal.comp
      ((hc e q₀ q₁ he hq₀ hq₁).div (hc e q₀' q₁' he hq₀' hq₁'))
  have hmap (ν : Measure ((Bool × Bool) × X)) :
      (ν.map f).withDensity r = (ν.withDensity (r ∘ f)).map f := by
    ext S hS
    rw [withDensity_apply _ hS, Measure.map_apply hf hS,
      withDensity_apply _ (hS.preimage hf)]
    rw [← lintegral_indicator hS, lintegral_map (hr.indicator hS) hf,
      ← lintegral_indicator (hS.preimage hf)]
    rfl
  have hpos (p : ℝ) (hp : p ∈ Set.Icc η (1 - η)) (b : Bool) :
      0 < bitMass p b := by
    cases b with
    | false => change 0 < 1 - p; linarith [hp.2]
    | true => change 0 < p; exact lt_of_lt_of_le hη0 hp.1
  have hcellpos (x : X) (a y : Bool) :
      0 < cellMass (e x) (q₀' x) (q₁' x) a y := by
    unfold cellMass
    exact mul_pos (hpos (e x) (heη x) a)
      (by cases a with
        | false => exact hpos (q₀' x) (hq₀'η x) y
        | true => exact hpos (q₁' x) (hq₁'η x) y)
  have hmul : selectedDensity e q₀' q₁' * (r ∘ f) =
      selectedDensity e q₀ q₁ := by
    funext z
    obtain ⟨⟨a, y⟩, x⟩ := z
    change ENNReal.ofReal (cellMass (e x) (q₀' x) (q₁' x) a y) *
      ENNReal.ofReal (cellMass (e x) (q₀ x) (q₁ x) a y /
        cellMass (e x) (q₀' x) (q₁' x) a y) =
      ENNReal.ofReal (cellMass (e x) (q₀ x) (q₁ x) a y)
    rw [ENNReal.ofReal_div_of_pos (hcellpos x a y)]
    exact ENNReal.mul_div_cancel (by simp [hcellpos x a y])
      (by simp)
  change (ν.withDensity (selectedDensity e q₀ q₁)).map f =
    ((ν.withDensity (selectedDensity e q₀' q₁')).map f).withDensity r
  rw [hmap, ← withDensity_mul ν hd' (hr.comp hf), hmul]

/-- [Two selected laws with a shared base and propensity are absolutely
continuous in the stated direction](goal) for [measurable interior
parameters](hyp:he,hq₀,hq₁,hq₀',hq₁',hη0,hηhalf,heη,hq₀η,hq₁η,hq₀'η,hq₁'η)
over a [probability base law](hyp:μ).

Rewrite with `selectedLaw_eq_withDensity`, then use
`withDensity_absolutelyContinuous`.
-/
theorem selectedLaw_ac {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1 / 2)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    selectedLaw μ e q₀ q₁ ≪ selectedLaw μ e q₀' q₁' := by
  rw [selectedLaw_eq_withDensity μ e q₀ q₁ q₀' q₁' he hq₀ hq₁ hq₀' hq₁'
    hη0 hηhalf heη hq₀η hq₁η hq₀'η hq₁'η]
  exact withDensity_absolutelyContinuous _ _

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

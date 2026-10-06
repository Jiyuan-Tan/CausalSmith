module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional-distribution congruence on a conditioning fiber

This module localizes a joint law to a measurable conditioning fiber. It turns
almost-everywhere equality of two outcomes on that fiber into equality of their
conditional distributions there. The proof packages the restricted joint-law,
composition-product restriction, and localized kernel-uniqueness steps for use
in general finite-measure arguments.
-/

public section

namespace Causalean.Mathlib.Probability.Kernel.CondDistribFiber

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Given [a measure `μ`](hyp:μ), [a measurable conditioning variable `T`](hyp:T,hT),
[two measurable outcome variables `Yv` and `Zv`](hyp:Yv,Zv,hY,hZ), and [a measurable
conditioning set `s`](hyp:s,hs), if [the outcomes agree almost everywhere on the
preimage of that set](hyp:h), then [their joint laws agree after restriction to that
conditioning set](goal). -/
theorem map_prod_restrict_eq_of_ae_eq_on_preimage
    {Ω B Y : Type*} [MeasurableSpace Ω] [MeasurableSpace B] [MeasurableSpace Y]
    (μ : Measure Ω) (T : Ω → B) (Yv Zv : Ω → Y)
    (hT : Measurable T) (hY : Measurable Yv) (hZ : Measurable Zv)
    {s : Set B} (hs : MeasurableSet s)
    (h : ∀ᵐ ω ∂μ, T ω ∈ s → Yv ω = Zv ω) :
    (μ.map (fun ω => (T ω, Yv ω))).restrict (s ×ˢ Set.univ) =
      (μ.map (fun ω => (T ω, Zv ω))).restrict (s ×ˢ Set.univ) := by
  have hYprod : Measurable (fun ω => (T ω, Yv ω)) := hT.prodMk hY
  have hZprod : Measurable (fun ω => (T ω, Zv ω)) := hT.prodMk hZ
  have hYpre : (fun ω => (T ω, Yv ω)) ⁻¹' (s ×ˢ Set.univ) = T ⁻¹' s := by
    ext ω
    simp
  have hZpre : (fun ω => (T ω, Zv ω)) ⁻¹' (s ×ˢ Set.univ) = T ⁻¹' s := by
    ext ω
    simp
  rw [Measure.restrict_map hYprod (hs.prod MeasurableSet.univ),
    Measure.restrict_map hZprod (hs.prod MeasurableSet.univ), hYpre, hZpre]
  apply Measure.map_congr
  apply (ae_restrict_iff' (hT hs)).2
  filter_upwards [h] with ω hω hωs
  exact congrArg (fun y => (T ω, y)) (hω hωs)

/-- Given [an s-finite base measure `ν`](hyp:ν), [an s-finite kernel `κ`](hyp:κ), and
[a measurable base set `s`](hyp:s,hs), [restricting their composition product to that
set in the first coordinate gives the composition product formed from the restricted
base measure](goal). -/
theorem compProd_restrict_left
    {B Y : Type*} [MeasurableSpace B] [MeasurableSpace Y]
    (ν : Measure B) [SFinite ν]
    (κ : Kernel B Y) [IsSFiniteKernel κ]
    {s : Set B} (hs : MeasurableSet s) :
    (ν ⊗ₘ κ).restrict (s ×ˢ Set.univ) = (ν.restrict s) ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply' (hs.prod MeasurableSet.univ),
    Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht, ← lintegral_indicator hs]
  congr 1
  ext b
  by_cases hb : b ∈ s <;> simp [hb]

/-- Given [a finite base measure `ν`](hyp:ν), [two finite kernels `κ` and `η`](hyp:κ,η),
and [a measurable base set `s`](hyp:s,hs), if [their composition products agree after
restriction to that set](hyp:h), then [the kernels agree almost everywhere on the
selected set](goal). -/
theorem ae_eq_on_of_compProd_restrict_eq
    {B Y : Type*} [MeasurableSpace B] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    (ν : Measure B) [IsFiniteMeasure ν]
    (κ η : Kernel B Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set B} (hs : MeasurableSet s)
    (h : (ν ⊗ₘ κ).restrict (s ×ˢ Set.univ) =
      (ν ⊗ₘ η).restrict (s ×ˢ Set.univ)) :
    ∀ᵐ b ∂ν, b ∈ s → κ b = η b := by
  rw [compProd_restrict_left ν κ hs,
    compProd_restrict_left ν η hs] at h
  exact ae_imp_of_ae_restrict (Kernel.ae_eq_of_compProd_eq h)

/-- Given [a finite sampling measure `μ`](hyp:μ), [a measurable covariate map `Xv`](hyp:Xv,hX),
[a measurable treatment map `Av`](hyp:Av,hA), [two measurable outcome maps `Yv` and
`Zv`](hyp:Yv,Zv,hY,hZ), and [a selected treatment value `a`](hyp:a), if [the outcomes
agree almost everywhere whenever treatment has that value](hyp:h), then [their conditional
distributions given covariates and treatment agree almost everywhere on the corresponding
conditioning fiber](goal). -/
theorem condDistrib_congr_on_conditioning_fiber
    {Ω X A Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xv : Ω → X) (Av : Ω → A) (Yv Zv : Ω → Y)
    (hX : Measurable Xv) (hA : Measurable Av)
    (hY : Measurable Yv) (hZ : Measurable Zv) (a : A)
    (h : ∀ᵐ ω ∂μ, Av ω = a → Yv ω = Zv ω) :
    ∀ᵐ xa ∂μ.map (fun ω => (Xv ω, Av ω)), xa.2 = a →
      condDistrib Yv (fun ω => (Xv ω, Av ω)) μ xa =
        condDistrib Zv (fun ω => (Xv ω, Av ω)) μ xa := by
  let T : Ω → X × A := fun ω => (Xv ω, Av ω)
  let s : Set (X × A) := {xa | xa.2 = a}
  have hT : Measurable T := hX.prodMk hA
  have hs : MeasurableSet s := measurable_snd (measurableSet_singleton a)
  have h' : ∀ᵐ ω ∂μ, T ω ∈ s → Yv ω = Zv ω := by
    simpa [T, s] using h
  have hJ := map_prod_restrict_eq_of_ae_eq_on_preimage
    μ T Yv Zv hT hY hZ hs h'
  rw [← compProd_map_condDistrib (X := T) hY.aemeasurable,
    ← compProd_map_condDistrib (X := T) hZ.aemeasurable] at hJ
  have hK := ae_eq_on_of_compProd_restrict_eq
    (μ.map T) (condDistrib Yv T μ) (condDistrib Zv T μ) hs hJ
  simpa [T, s] using hK

end Causalean.Mathlib.Probability.Kernel.CondDistribFiber

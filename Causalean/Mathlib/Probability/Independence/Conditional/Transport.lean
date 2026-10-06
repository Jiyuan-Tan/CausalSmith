/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.Independence.Conditional.Transport.AeRetraction

/-!
Transport of conditional-independence statements along measurable maps and almost-everywhere
retractions. It supports replacing a random variable by an equivalent representation without
losing its conditional independence structure.
-/

public section

namespace Causalean.Mathlib.Probability.Independence.Conditional

/-- For [standard Borel spaces `α` and `β`](hyp:α,β), [nonempty standard
Borel spaces `γ` and `δ`](hyp:γ,δ), [a measurable space `ε`](hyp:ε),
[a map `φ`](hyp:φ), [its measurability](hyp:hφ), [functions `X`, `Y`, and
`Z`](hyp:X,Y,Z), [their measurability](hyp:hX,hY,hZ), [a finite measure `ν`
whose pushforward by `φ` is finite](hyp:ν), and
[conditional independence after composition](hyp:h),
[conditional independence holds under the pushforward measure](goal). -/
theorem condIndepFun_of_map
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    {ε : Type*} [MeasurableSpace ε]
    {φ : α → β} (hφ : Measurable φ)
    {X : β → γ} (hX : Measurable X)
    {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z)
    {ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure ν]
    [MeasureTheory.IsFiniteMeasure (ν.map φ)]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (Z ∘ φ) inferInstance)
      (Measurable.comap_le (hZ.comp hφ))
      (X ∘ φ) (Y ∘ φ) ν) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap Z inferInstance) (hZ.comap_le)
      X Y (ν.map φ) := by
  have hcd1 : ProbabilityTheory.condDistrib (Y ∘ φ) (Z ∘ φ) ν =
      ProbabilityTheory.condDistrib Y Z (ν.map φ) := by
    simp only [ProbabilityTheory.condDistrib]
    congr 1
    exact (MeasureTheory.Measure.map_map (hZ.prodMk hY) hφ).symm
  have hcd2 : ProbabilityTheory.condDistrib (Y ∘ φ)
        (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) ν =
      ProbabilityTheory.condDistrib Y (fun b ↦ (Z b, X b)) (ν.map φ) := by
    simp only [ProbabilityTheory.condDistrib]
    congr 1
    exact (MeasureTheory.Measure.map_map ((hZ.prodMk hX).prodMk hY) hφ).symm
  have hfilt : ν.map (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) =
      (ν.map φ).map (fun b ↦ (Z b, X b)) :=
    (MeasureTheory.Measure.map_map (hZ.prodMk hX) hφ).symm
  rw [ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  have h' := (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hY.comp hφ) (hX.comp hφ) (hZ.comp hφ)).mp h
  rw [hcd2, hcd1, hfilt] at h'
  exact h'

end Causalean.Mathlib.Probability.Independence.Conditional

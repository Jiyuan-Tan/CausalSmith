/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation identified on measurable preimages

This module packages the uniqueness characterization of conditional expectation in the
form where restricted integrals agree on every measurable preimage of a generating map.
-/

public section

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- [The conditional expectation of one integrable real function equals another almost
everywhere](goal) for [a finite measure](hyp:mu) and [a measurable generating
map](hyp:design,hdesign), provided [both functions are integrable](hyp:Y,m,hY,hm), [the second
is strongly measurable for the pullback σ-algebra](hyp:hm_design), and [their restricted
integrals agree on every measurable preimage](hyp:hintegral).

Global integrability of the second function supplies integrability on the finite
conditioning events, while finiteness of the measure supplies the sigma-finiteness
required by Mathlib's conditional-expectation uniqueness theorem. -/
theorem condExp_eq_of_integral_preimage_eq
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y m : Omega -> Real)
    (hY : Integrable Y mu) (hm : Integrable m mu)
    (hm_design :
      AEStronglyMeasurable[MeasurableSpace.comap design inferInstance] m mu)
    (hintegral : forall S : Set D, MeasurableSet S ->
      ∫ omega in design ⁻¹' S, Y omega ∂mu =
        ∫ omega in design ⁻¹' S, m omega ∂mu) :
    mu[Y | MeasurableSpace.comap design inferInstance] =ᵐ[mu] m := by
  have hversion :
      m =ᵐ[mu] mu[Y | MeasurableSpace.comap design inferInstance] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hdesign.comap_le hY ?_ ?_ hm_design
    · intro S _ _
      exact hm.integrableOn
    · intro S hS _
      rcases hS with ⟨T, hT, rfl⟩
      exact (hintegral T hT).symm
  exact hversion.symm

end Causalean.Mathlib.MeasureTheory

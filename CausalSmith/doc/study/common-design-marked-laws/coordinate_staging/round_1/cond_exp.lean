/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation identified on design preimages

This module packages the uniqueness characterization of conditional expectation in the
form used by random-design models: it is enough to match restricted integrals on every
measurable preimage of the design map.
-/

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- For [a finite sampling measure](hyp:mu), [a measurable design map](hyp:design,hdesign),
[an integrable outcome and candidate regression](hyp:Y,m,hY,hm), [a candidate regression
measurable with respect to the design σ-algebra](hyp:hm_design), and [matching outcome and
candidate-regression integrals on every measurable design event](hyp:hintegral), [the
candidate regression is a version of the outcome's conditional expectation given the
design](goal).

Global integrability of the candidate regression supplies integrability on the finite
conditioning events, while finiteness of the sampling measure supplies the sigma-finiteness
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

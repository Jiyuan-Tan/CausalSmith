/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Measurability of parametric Lp-norm functionals

For a parameter-dependent function `g : Ω → X → E` valued in a Borel normed
additive group, the map
`ω ↦ (eLpNorm (g ω) p P).toReal` is measurable at every finite nonzero exponent
`p`, provided `g` is jointly
measurable in `(ω, x)`.

This file provides two flavours, both consequences of Tonelli for the
parametric integral `ω ↦ ∫⁻ x, ‖g ω x‖₊^p.toReal ∂P` followed by the post-processing
`(·)^(1/p.toReal)` and `.toReal`:

* `measurable_eLpNorm_toReal_of_uncurry`  — top-σ-algebra version: from
  joint measurability of `Function.uncurry g`.
* `measurable_eLpNorm_toReal_of_uncurry_of_factor`  — sub-σ-algebra
  version: from joint measurability wrt the sub-σ-algebra product.

These are general measurability facts for parameterized Lp seminorms.
-/

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! # Measurability of Parametric Lp Norms

This file proves that the parameter map sending a jointly measurable integrand to
its finite nonzero Lp norm under a fixed measure is measurable. It supplies a Tonelli-based
measurability tool for parameterized families of functions.

The top-σ-algebra lemma is `measurable_eLpNorm_toReal_of_uncurry`; the
sub-σ-algebra version, where joint measurability factors through
`mΩ × MeasurableSpace X`, is
`measurable_eLpNorm_toReal_of_uncurry_of_factor`. -/

public section

open MeasureTheory ENNReal

namespace Causalean.Mathlib.MeasureTheory.Function.LpSeminorm

variable {Ω X : Type*} [MeasurableSpace X]

/-- **Lp-norm measurable from joint measurability (top σ-algebra).** For a σ-finite base measure
`P` and [an exponent `p` that is neither zero](hyp:hp_zero) [nor infinite](hyp:hp_top), if [the
map `(ω, x) ↦ g ω x` is jointly measurable on the product of `Ω` and `X`](hyp:hg), then [the
real-valued Lp norm `ω ↦ ‖g ω‖_{Lp(P)}` is measurable as a function of `ω`](goal).

**Proof sketch.** `(eLpNorm (g ω) p P).toReal =
  ((∫⁻ x, ‖g ω x‖₊^p.toReal ∂P)^(1/p.toReal)).toReal`.  Use:
* `Measurable.lintegral_prod_right` (Tonelli) on `(ω, x) ↦ ‖g ω x‖₊^p.toReal` —
  joint measurable from `hg` via `Measurable.pow_const` and `enorm`.
* `Measurable.pow_const` for the `(1/p.toReal)` power.
* `ENNReal.measurable_toReal` for the final `.toReal`. -/
@[fun_prop]
lemma measurable_eLpNorm_toReal_of_uncurry
    [MeasurableSpace Ω] {P : Measure X} [SFinite P]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [ContinuousENorm E]
    [OpensMeasurableSpace E]
    {g : Ω → X → E} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ω => (eLpNorm (g ω) p P).toReal) := by
  have h_int :
      Measurable (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ p.toReal ∂P) := by
    exact Measurable.lintegral_prod_right' ((hg.enorm).pow_const p.toReal)
  have h_norm : Measurable (fun ω => eLpNorm (g ω) p P) := by
    simpa [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        hp_zero hp_top] using
      (h_int.pow_const (1 / p.toReal))
  exact ENNReal.measurable_toReal.comp h_norm

/-- Given [an exponent `p` that is neither zero](hyp:hp_zero) [nor infinite](hyp:hp_top) and
[joint measurability of the parameterized function](hyp:hg), [its real-valued Lp norm is
measurable in the parameter](goal). This is the deprecated `_two_` spelling, although `p` was
never fixed to `2`. -/
@[deprecated measurable_eLpNorm_toReal_of_uncurry (since := "2026-08-29")]
lemma measurable_eLpNorm_two_toReal_of_uncurry
    [MeasurableSpace Ω] {P : Measure X} [SFinite P]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [ContinuousENorm E]
    [OpensMeasurableSpace E]
    {g : Ω → X → E} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ω => (eLpNorm (g ω) p P).toReal) :=
  measurable_eLpNorm_toReal_of_uncurry hp_zero hp_top hg

/-- **Lp-norm measurable with respect to a sub-σ-algebra.** For a σ-finite base measure `P` and
[an exponent `p` that is neither zero](hyp:hp_zero) [nor infinite](hyp:hp_top), if [the map
`(ω, x) ↦ g ω x` is jointly measurable with respect to the product of a sub-σ-algebra `mΩ` on `Ω`
and the σ-algebra on `X`](hyp:hg_uncurry), then [the real-valued Lp norm `ω ↦ ‖g ω‖_{Lp(P)}` is
measurable with respect to `mΩ`](goal).

**Proof sketch.** Apply `Measurable.lintegral_prod_right'` at the
sub-σ-algebra product level to `‖g ω x‖₊^p.toReal`, then post-process by
`(·)^(1/p.toReal)` and `.toReal`. -/
@[fun_prop]
lemma measurable_eLpNorm_toReal_of_uncurry_of_factor
    {mΩ : MeasurableSpace Ω}
    {P : Measure X} [SFinite P]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [ContinuousENorm E]
    [OpensMeasurableSpace E]
    {g : Ω → X → E} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg_uncurry :
      @Measurable (Ω × X) E
        (@Prod.instMeasurableSpace Ω X mΩ inferInstance) inferInstance
        (Function.uncurry g)) :
    Measurable[mΩ] (fun ω => (eLpNorm (g ω) p P).toReal) := by
  have h_int :
      Measurable[mΩ] (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ p.toReal ∂P) := by
    exact Measurable.lintegral_prod_right' ((hg_uncurry.enorm).pow_const p.toReal)
  have h_norm : Measurable[mΩ] (fun ω => eLpNorm (g ω) p P) := by
    simpa [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        hp_zero hp_top] using
      (h_int.pow_const (1 / p.toReal))
  exact ENNReal.measurable_toReal.comp h_norm

/-- Given [an exponent `p` that is neither zero](hyp:hp_zero) [nor infinite](hyp:hp_top) and
[joint measurability for the product with a chosen parameter σ-algebra](hyp:hg_uncurry), [the
real-valued Lp norm is measurable for that parameter σ-algebra](goal). This is the deprecated
`_two_` spelling, although `p` was never fixed to `2`. -/
@[deprecated measurable_eLpNorm_toReal_of_uncurry_of_factor (since := "2026-08-29")]
lemma measurable_eLpNorm_two_toReal_of_uncurry_of_factor
    {mΩ : MeasurableSpace Ω}
    {P : Measure X} [SFinite P]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [ContinuousENorm E]
    [OpensMeasurableSpace E]
    {g : Ω → X → E} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg_uncurry :
      @Measurable (Ω × X) E
        (@Prod.instMeasurableSpace Ω X mΩ inferInstance) inferInstance
        (Function.uncurry g)) :
    Measurable[mΩ] (fun ω => (eLpNorm (g ω) p P).toReal) :=
  measurable_eLpNorm_toReal_of_uncurry_of_factor hp_zero hp_top hg_uncurry

end Causalean.Mathlib.MeasureTheory.Function.LpSeminorm

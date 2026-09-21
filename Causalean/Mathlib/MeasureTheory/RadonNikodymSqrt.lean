/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.MeasureTheory.BoundedCenteredDense
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Square-root Radon--Nikodym densities in L²

This module packages the square root of a finite measure's Radon--Nikodym
derivative as an `L²` element.  For probability measures it also identifies the
base law's square-root density with the constant-one vector.  These are the
measure-theoretic primitives used to state differentiability in quadratic mean.
-/

@[expose] public section

noncomputable section

open _root_.MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

variable {Z : Type*} [MeasurableSpace Z]

/-- For [a real L² element `f`](hyp:f), [its squared Hilbert norm is the integral
of the square of any canonical representative](goal). -/
theorem lpNorm_sq_eq_integral_sq {P : Measure Z} (f : Lp ℝ 2 P) :
    ‖f‖ ^ 2 = ∫ z, f z ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with z
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Given [a finite measure `Q`](hyp:Q) and [a reference measure `P`](hyp:P), the
[square-root Radon--Nikodym density of `Q` relative to `P`](goal) is
`sqrt((dQ/dP).toReal)`. -/
noncomputable def rnSqrtDensity (P Q : Measure Z) [IsFiniteMeasure Q] : Z → ℝ :=
  fun z => Real.sqrt ((Q.rnDeriv P z).toReal)

/-- For [a finite measure `Q`](hyp:Q) and [a reference measure `P`](hyp:P), its
[square-root Radon--Nikodym density is square-integrable under `P`](goal). -/
theorem rnSqrtDensity_memLp (P Q : Measure Z) [IsFiniteMeasure Q] :
    MemLp (rnSqrtDensity P Q) 2 P := by
  have hmeas : Measurable (rnSqrtDensity P Q) :=
    Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv Q P))
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
  refine (Measure.integrable_toReal_rnDeriv (μ := Q) (ν := P)).congr ?_
  filter_upwards [] with z
  simp only [rnSqrtDensity, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]

/-- Given [a finite measure `Q`](hyp:Q) and [a reference measure `P`](hyp:P), the
[L² square-root Radon--Nikodym density](goal) is the equivalence class of
`sqrt(dQ/dP)`. -/
noncomputable def rnSqrtDensityLp (P Q : Measure Z) [IsFiniteMeasure Q] : Lp ℝ 2 P :=
  (rnSqrtDensity_memLp P Q).toLp (rnSqrtDensity P Q)

/-- For [a probability measure `P`](hyp:P), [its square-root density relative to
itself is the constant-one L² vector](goal). -/
@[simp] theorem rnSqrtDensityLp_self (P : Measure Z) [IsProbabilityMeasure P] :
    rnSqrtDensityLp P P = lpOne P := by
  apply Lp.ext
  filter_upwards [(rnSqrtDensity_memLp P P).coeFn_toLp,
    (memLp_const (1 : ℝ)).coeFn_toLp (p := 2) (μ := P),
    Measure.rnDeriv_self P] with z hs h1 hrn
  rw [show rnSqrtDensityLp P P z = rnSqrtDensity P P z from hs]
  rw [show lpOne P z = (1 : ℝ) from h1]
  simp [rnSqrtDensity, hrn]

end Causalean.Mathlib.MeasureTheory

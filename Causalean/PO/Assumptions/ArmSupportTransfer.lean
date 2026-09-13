/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge

/-! # Transferring an outcome bound from an observed arm to a potential outcome

Within a positive-mass cell, conditioning is done by normalizing the restricted measure (see
`Causalean.Mathlib.Probability.normalizedRestrict`).  This module provides the real-valued
indicator of a treatment arm and the support-transfer step used in potential-outcome arguments:
if a potential outcome is independent of the arm indicator under the cell law (ignorability),
agrees with the observed outcome on that arm (consistency), and the arm has positive probability
(positivity), then an almost-sure absolute bound on the observed outcome in the arm carries over
to the potential outcome throughout the cell.
-/

namespace Causalean.PO

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability

/-- Given [a sample space and an event in it](hyp:Ω,A), the [real-valued arm
indicator](goal) equals one for sample points in the event and zero for all other sample
points.

The real-valued indicator of membership in an event, equal to one on the
event and zero elsewhere. -/
noncomputable def armIndicator {Ω : Type*} (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun _ => 1)

/-- Within [a measurable positive-mass cell](hyp:hC,hCpos), for [a measurable
arm event](hyp:hA), if [the potential outcome is measurable](hyp:hYpot), [the arm has positive normalized cell
probability](hyp:hArmPos), [the potential outcome is independent of the arm indicator under the
normalized cell law](hyp:hInd), [the observed and potential outcomes agree almost surely on that
arm](hyp:hConsistency), and [the observed outcome obeys an absolute bound there](hyp:hObservedBound),
then [the potential outcome obeys the same absolute bound almost surely throughout the cell](goal). -/
theorem ae_abs_potential_le_of_indep_positive_arm
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {C A : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < P C)
    (hA : MeasurableSet A)
    {Ypot Yobs : Ω → ℝ} (hYpot : Measurable Ypot)
    (hArmPos : 0 < normalizedRestrict P C A)
    (hInd : IndepFun Ypot (armIndicator A) (normalizedRestrict P C))
    (hConsistency :
      Yobs =ᵐ[(normalizedRestrict P C).restrict A] Ypot)
    {R : ℝ}
    (hObservedBound :
      ∀ᵐ ω ∂(normalizedRestrict P C).restrict A, |Yobs ω| ≤ R) :
    ∀ᵐ ω ∂P.restrict C, |Ypot ω| ≤ R := by
  let B : Set Ω := {ω | R < |Ypot ω|}
  have hBadRange : MeasurableSet {y : ℝ | R < |y|} := by
    rw [show {y : ℝ | R < |y|} = {y : ℝ | R < ‖y‖} by
      ext y
      simp only [Real.norm_eq_abs]]
    exact measurableSet_lt measurable_const (by fun_prop)
  have hB : MeasurableSet B := hYpot hBadRange
  have hPotBoundArm :
      ∀ᵐ ω ∂(normalizedRestrict P C).restrict A, |Ypot ω| ≤ R := by
    filter_upwards [hConsistency, hObservedBound] with ω hEq hBound
    rw [← hEq]
    exact hBound
  have hBAzero : normalizedRestrict P C (B ∩ A) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_imp_of_ae_restrict hPotBoundArm] with ω hω
    intro hmem
    exact (not_lt_of_ge (hω hmem.2)) hmem.1
  have hArmPreimage : armIndicator A ⁻¹' ({1} : Set ℝ) = A := by
    ext ω
    simp [armIndicator]
  have hFactor :
      normalizedRestrict P C (B ∩ A) =
        normalizedRestrict P C B * normalizedRestrict P C A := by
    simpa [B, hArmPreimage] using
      hInd.measure_inter_preimage_eq_mul
        {y : ℝ | R < |y|} ({1} : Set ℝ)
        hBadRange (measurableSet_singleton (1 : ℝ))
  have hBzero : normalizedRestrict P C B = 0 := by
    have hprod :
        normalizedRestrict P C B * normalizedRestrict P C A = 0 := by
      rw [← hFactor, hBAzero]
    exact (mul_eq_zero.mp hprod).resolve_right hArmPos.ne'
  apply (ae_normalizedRestrict_iff hCpos).mp
  filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hBzero)] with ω hω
  exact le_of_not_gt (by simpa [B] using hω)

end Causalean.PO

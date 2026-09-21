/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge

/-! # Support Transfer Across an Independent Event

This file defines a real-valued event indicator and proves a measure-theoretic
support-transfer theorem under a normalized restriction to a positive-mass
cell. Independence from a positive-probability event and almost-everywhere
agreement on that event transfer an absolute bound from a reference quantity
to the target quantity throughout the cell.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability

/-- Given [a sample space and an event in it](hyp:Omega,A), the [real-valued
event indicator](goal) equals one for sample points in the event and zero for
all other sample points. -/
noncomputable def eventIndicator {Omega : Type*} (A : Set Omega) : Omega → ℝ :=
  A.indicator (fun _ => 1)

/-- Within [a measurable positive-mass cell](hyp:_hC,hCpos), for [a measurable
event](hyp:_hA), if [a target quantity is measurable](hyp:hTarget), [the event
has positive normalized cell probability](hyp:hEventPos), [the target is
independent of the event indicator under the normalized cell
law](hyp:hInd), [a reference quantity agrees almost surely with the target on
that event](hyp:hAgreement), and [the reference obeys an absolute bound
there](hyp:hReferenceBound), then [the target obeys the same absolute bound
almost surely throughout the cell](goal). -/
theorem ae_abs_target_le_of_indep_positive_event
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {C A : Set Omega} (_hC : MeasurableSet C) (hCpos : 0 < P C)
    (_hA : MeasurableSet A)
    {target reference : Omega → ℝ} (hTarget : Measurable target)
    (hEventPos : 0 < normalizedRestrict P C A)
    (hInd : IndepFun target (eventIndicator A) (normalizedRestrict P C))
    (hAgreement :
      reference =ᵐ[(normalizedRestrict P C).restrict A] target)
    {R : ℝ}
    (hReferenceBound :
      ∀ᵐ omega ∂(normalizedRestrict P C).restrict A,
        |reference omega| ≤ R) :
    ∀ᵐ omega ∂P.restrict C, |target omega| ≤ R := by
  let B : Set Omega := {omega | R < |target omega|}
  have hBadRange : MeasurableSet {y : ℝ | R < |y|} := by
    rw [show {y : ℝ | R < |y|} = {y : ℝ | R < ‖y‖} by
      ext y
      simp only [Real.norm_eq_abs]]
    exact measurableSet_lt measurable_const (by fun_prop)
  have hB : MeasurableSet B := hTarget hBadRange
  have hTargetBoundEvent :
      ∀ᵐ omega ∂(normalizedRestrict P C).restrict A,
        |target omega| ≤ R := by
    filter_upwards [hAgreement, hReferenceBound] with omega hEq hBound
    rw [← hEq]
    exact hBound
  have hBAzero : normalizedRestrict P C (B ∩ A) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_imp_of_ae_restrict hTargetBoundEvent] with omega homega
    intro hmem
    exact (not_lt_of_ge (homega hmem.2)) hmem.1
  have hEventPreimage : eventIndicator A ⁻¹' ({1} : Set ℝ) = A := by
    ext omega
    simp [eventIndicator]
  have hFactor :
      normalizedRestrict P C (B ∩ A) =
        normalizedRestrict P C B * normalizedRestrict P C A := by
    simpa [B, hEventPreimage] using
      hInd.measure_inter_preimage_eq_mul
        {y : ℝ | R < |y|} ({1} : Set ℝ)
        hBadRange (measurableSet_singleton (1 : ℝ))
  have hBzero : normalizedRestrict P C B = 0 := by
    have hprod :
        normalizedRestrict P C B * normalizedRestrict P C A = 0 := by
      rw [← hFactor, hBAzero]
    exact (mul_eq_zero.mp hprod).resolve_right hEventPos.ne'
  apply (ae_normalizedRestrict_iff hCpos).mp
  filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hBzero)] with omega homega
  exact le_of_not_gt (by simpa [B] using homega)

end Causalean.Stat

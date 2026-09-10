/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-! # Finite-cell conditional moments and support transfer

This module provides generic probability tools for conditioning on a measurable
positive-mass cell by normalizing its restricted measure.  It turns bounded-test
factorization into finite-coordinate moment factorization and transfers an
almost-sure outcome bound from a positive observed arm to an independent
potential outcome throughout the cell.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory ProbabilityTheory

/-- Given [a measurable sample space, a measure on it, and a cell in that sample
space](hyp:Ω,P,C), the [normalized restricted measure](goal) is the measure restricted to
the cell and scaled by the reciprocal of the measure of that cell.

The normalized restriction of a measure to a cell is the restricted measure
rescaled so that a positive-mass cell has total mass one. -/
noncomputable def normalizedRestrict {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Set Ω) : Measure Ω :=
  (P C)⁻¹ • P.restrict C

/-- Given [a measurable sample space, a real normed vector-valued outcome space, a measure,
a cell, and a function on the sample space](hyp:Ω,E,P,C,f), the [normalized restricted
integral](goal) is the integral of the function with respect to the normalized restricted
measure of that cell.

A normalized restricted integral is the expectation of a function under the
probability law obtained by conditioning the original measure on a cell. -/
noncomputable def normalizedRestrictedIntegral
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (C : Set Ω) (f : Ω → E) : E :=
  ∫ ω, f ω ∂normalizedRestrict P C

/-- For a finite sampling measure, a [measurable cell](hyp:hC) with [strictly
positive mass](hyp:hCpos) has [a normalized restricted law that is a probability
measure](goal). -/
theorem normalizedRestrict_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < P C) :
    IsProbabilityMeasure (normalizedRestrict P C) := by
  have hCne : P C ≠ 0 := ne_of_gt hCpos
  have hCtop : P C ≠ ⊤ := measure_ne_top P C
  refine ⟨?_⟩
  simp only [normalizedRestrict, Measure.smul_apply, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hCne hCtop

/-- For a [positive-mass cell](hyp:hCpos) and a [measurable event](hyp:hA), [the
normalized cell law of that event is its intersection mass divided by the cell
mass](goal). -/
theorem normalizedRestrict_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {C A : Set Ω} (hCpos : 0 < P C) (hA : MeasurableSet A) :
    normalizedRestrict P C A = (P C)⁻¹ * P (A ∩ C) := by
  simp [normalizedRestrict, Measure.smul_apply, Measure.restrict_apply hA]

/-- On a [positive-mass cell](hyp:hCpos), [integrating a function](hyp:f) under
the normalized cell law is [the restricted integral rescaled by the reciprocal
cell mass](goal). -/
theorem normalizedRestrictedIntegral_eq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {C : Set Ω} (hCpos : 0 < P C)
    (f : Ω → E) :
    normalizedRestrictedIntegral P C f =
      (P C).toReal⁻¹ • ∫ ω in C, f ω ∂P := by
  simp [normalizedRestrictedIntegral, normalizedRestrict,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]

/-- On a [positive-mass cell](hyp:hCpos), [an almost-sure assertion holds under
the normalized cell law exactly when it holds under the unnormalized restricted
measure](goal). -/
theorem ae_normalizedRestrict_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {C : Set Ω} (hCpos : 0 < P C) {p : Ω → Prop} :
    (∀ᵐ ω ∂normalizedRestrict P C, p ω) ↔ (∀ᵐ ω ∂P.restrict C, p ω) := by
  have hscale : 0 < (P C)⁻¹ ∧ (P C)⁻¹ < ⊤ := ⟨
    ENNReal.inv_pos.mpr (measure_ne_top P C),
    ENNReal.inv_lt_top.mpr hCpos⟩
  rw [normalizedRestrict]
  exact Measure.ae_ennreal_smul_measure_iff hscale.1.ne'

/-- Given [a measurable sample space, two measurable value spaces, a measure, and two
random elements](hyp:Ω,S,T,μ,X,Y), the [bounded-test factorization condition](goal) holds
exactly when, for every pair of measurable bounded real-valued test functions on the two
value spaces, the integral of their product after applying the two random elements equals
the product of their separate integrals.

Bounded measurable tests of two random elements factor under a measure when
the expectation of every product of such tests is the product of expectations. -/
def BoundedTestFactorization
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) : Prop :=
  ∀ (φ : S → ℝ) (ψ : T → ℝ),
    Measurable φ → Measurable ψ →
    (∃ K : ℝ, ∀ x, |φ x| ≤ K) →
    (∃ L : ℝ, ∀ y, |ψ y| ≤ L) →
    (∫ ω, φ (X ω) * ψ (Y ω) ∂μ) =
      (∫ ω, φ (X ω) ∂μ) * (∫ ω, ψ (Y ω) ∂μ)

/-- Given [a measurable sample space, two measurable value spaces, a measure, a cell, and
two random elements](hyp:Ω,S,T,P,C,X,Y), the [normalized restricted bounded-test
factorization condition](goal) is bounded-test factorization of those random elements under
the normalized restriction of the measure to the cell.

Bounded-test factorization under the normalized probability law obtained by
restricting a measure to a cell. -/
def NormalizedRestrictedBoundedTestFactorization
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) (C : Set Ω) (X : Ω → S) (Y : Ω → T) : Prop :=
  BoundedTestFactorization (normalizedRestrict P C) X Y

/-- Under a probability law, [measurable random elements](hyp:hX,hY) whose [all
bounded measurable real-valued tests factor](hyp:hfactor) are [independent](goal). -/
theorem indepFun_of_boundedTestFactorization
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y)
    (hfactor : BoundedTestFactorization μ X Y) :
    IndepFun X Y μ := by
  rw [indepFun_iff_indepSet_preimage hX hY]
  intro s t hs ht
  have hsX : MeasurableSet (X ⁻¹' s) := hX hs
  have htY : MeasurableSet (Y ⁻¹' t) := hY ht
  rw [indepSet_iff_measure_inter_eq_mul hsX htY μ]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ (X ⁻¹' s ∩ Y ⁻¹' t))
    (ENNReal.mul_ne_top (measure_ne_top μ (X ⁻¹' s))
      (measure_ne_top μ (Y ⁻¹' t)))).mp
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    ← integral_indicator_one (hsX.inter htY),
    ← integral_indicator_one hsX, ← integral_indicator_one htY]
  have hfac := hfactor
    (s.indicator (fun _ => (1 : ℝ))) (t.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hs) (measurable_const.indicator ht)
    ⟨1, by intro x; by_cases hx : x ∈ s <;> simp [Set.indicator, hx]⟩
    ⟨1, by intro y; by_cases hy : y ∈ t <;> simp [Set.indicator, hy]⟩
  have hscomp :
      (fun ω => s.indicator (fun _ => (1 : ℝ)) (X ω)) =
        (X ⁻¹' s).indicator (fun _ => 1) := by
    funext ω
    by_cases hx : X ω ∈ s <;> simp [Set.indicator, hx]
  have htcomp :
      (fun ω => t.indicator (fun _ => (1 : ℝ)) (Y ω)) =
        (Y ⁻¹' t).indicator (fun _ => 1) := by
    funext ω
    by_cases hy : Y ω ∈ t <;> simp [Set.indicator, hy]
  have hprod :
      (fun ω => s.indicator (fun _ => (1 : ℝ)) (X ω) *
        t.indicator (fun _ => (1 : ℝ)) (Y ω)) =
        (X ⁻¹' s ∩ Y ⁻¹' t).indicator (fun _ => 1) := by
    funext ω
    by_cases hx : X ω ∈ s <;> by_cases hy : Y ω ∈ t <;>
      simp [Set.indicator, hx, hy]
  rw [hprod, hscomp, htcomp] at hfac
  exact hfac

/-- Given [a measurable sample space, a finite vector dimension, a measure, and a
finite-dimensional real random vector](hyp:Ω,n,μ,X), the [first-moment vector](goal) has
at each coordinate the integral of the corresponding coordinate of the random vector.

The vector of coordinatewise first moments of a finite-dimensional real
random variable under a measure. -/
noncomputable def firstMomentVector
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ ω, X ω i ∂μ

/-- Given [a measurable sample space, two finite vector dimensions, a measure, and two
finite-dimensional real random vectors](hyp:Ω,m,n,μ,X,Y), the [cross-moment matrix](goal)
has at each ordered pair of coordinates the integral of the product of the corresponding
coordinates of the two random vectors.

The matrix of coordinatewise cross moments of two finite-dimensional real
random variables under a measure. -/
noncomputable def crossMomentMatrix
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (μ : Measure Ω) (X : Ω → Fin m → ℝ) (Y : Ω → Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => ∫ ω, X ω i * Y ω j ∂μ

/-- For [a measurable positive-mass cell](hyp:hC,hCpos), [measurable
finite-coordinate random vectors](hyp:hX,hY), [integrable individual
coordinates](hyp:hXint,hYint), and [factorization of every bounded measurable
test under the normalized cell law](hyp:hfactor), [each coordinate product is
integrable and its cell cross moment factors into the two cell first moments](goal). -/
theorem normalizedRestricted_coordinate_factorization
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < P C)
    {m n : ℕ} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ i, Integrable (fun ω => X ω i) (normalizedRestrict P C))
    (hYint : ∀ j, Integrable (fun ω => Y ω j) (normalizedRestrict P C))
    (hfactor : NormalizedRestrictedBoundedTestFactorization P C X Y) :
    ∀ i j,
      Integrable (fun ω => X ω i * Y ω j) (normalizedRestrict P C) ∧
      normalizedRestrictedIntegral P C (fun ω => X ω i * Y ω j) =
        normalizedRestrictedIntegral P C (fun ω => X ω i) *
          normalizedRestrictedIntegral P C (fun ω => Y ω j) := by
  let _ : IsProbabilityMeasure (normalizedRestrict P C) :=
    normalizedRestrict_isProbabilityMeasure hC hCpos
  have hInd : IndepFun X Y (normalizedRestrict P C) :=
    indepFun_of_boundedTestFactorization hX hY hfactor
  intro i j
  have hcoordInd :
      IndepFun (fun ω => X ω i) (fun ω => Y ω j) (normalizedRestrict P C) := by
    simpa only [Function.comp_def] using
      hInd.comp (measurable_pi_apply i) (measurable_pi_apply j)
  constructor
  · change Integrable ((fun ω => X ω i) * (fun ω => Y ω j))
      (normalizedRestrict P C)
    exact hcoordInd.integrable_mul (hXint i) (hYint j)
  · simpa only [normalizedRestrictedIntegral, Pi.mul_apply] using
      hcoordInd.integral_mul_eq_mul_integral (hXint i).1 (hYint j).1

/-- For [a measurable positive-mass cell](hyp:hC,hCpos), [measurable
finite-coordinate random vectors](hyp:hX,hY), [integrable individual
coordinates](hyp:hXint,hYint), and [factorization of every bounded measurable
test under the normalized cell law](hyp:hfactor), [the complete normalized
cross-moment matrix is the outer product of the two normalized first-moment
vectors](goal). -/
theorem normalizedRestricted_crossMomentMatrix_eq_outer
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < P C)
    {m n : ℕ} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ i, Integrable (fun ω => X ω i) (normalizedRestrict P C))
    (hYint : ∀ j, Integrable (fun ω => Y ω j) (normalizedRestrict P C))
    (hfactor : NormalizedRestrictedBoundedTestFactorization P C X Y) :
    crossMomentMatrix (normalizedRestrict P C) X Y =
      Matrix.vecMulVec
        (firstMomentVector (normalizedRestrict P C) X)
        (firstMomentVector (normalizedRestrict P C) Y) := by
  ext i j
  exact (normalizedRestricted_coordinate_factorization hC hCpos hX hY hXint hYint
    hfactor i j).2

/-- Given [a sample space and an event in it](hyp:Ω,A), the [real-valued arm
indicator](goal) equals one for sample points in the event and zero for all other sample
points.

The real-valued indicator of membership in an event, equal to one on the
event and zero elsewhere. -/
noncomputable def armIndicator {Ω : Type*} (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun _ => 1)

/-- Within [a measurable positive-mass cell](hyp:hC,hCpos), for [a measurable
arm event](hyp:hA), if [the potential and observed outcomes are measurable](hyp:hYpot,hYobs),
[the potential outcome and observed outcome are integrable under their respective cell and
observed-arm laws](hyp:hYpotInt,hYobsInt), [the arm has positive normalized cell
probability](hyp:hArmPos), [the potential outcome is independent of the arm indicator under the
normalized cell law](hyp:hInd), [the observed and potential outcomes agree almost surely on that
arm](hyp:hConsistency), and [the observed outcome obeys an absolute bound there](hyp:hObservedBound),
then [the potential outcome obeys the same absolute bound almost surely throughout the cell](goal). -/
theorem ae_abs_potential_le_of_indep_positive_arm
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {C A : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < P C)
    (hA : MeasurableSet A)
    {Ypot Yobs : Ω → ℝ} (hYpot : Measurable Ypot) (hYobs : Measurable Yobs)
    (hYpotInt : Integrable Ypot (normalizedRestrict P C))
    (hYobsInt : Integrable Yobs ((normalizedRestrict P C).restrict A))
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

end Causalean.Mathlib.Probability

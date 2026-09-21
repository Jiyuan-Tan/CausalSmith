/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.Independence.Integral
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration

/-! # Finite-cell conditional moments

This module provides generic probability tools for conditioning on a measurable
positive-mass cell by normalizing its restricted measure.  It turns bounded-test
factorization into independence and into finite-coordinate moment factorization.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability

open MeasureTheory ProbabilityTheory

/-- Given [a measurable sample space, a measure on it, and a cell in that sample
space](hyp:Ω,P,C), the [normalized restricted measure](goal) is the measure restricted to
the cell and scaled by the reciprocal of the measure of that cell.

No condition is imposed on the cell. When the cell has positive finite measure the result is a
probability measure; a null cell or a cell of infinite measure gives the zero measure, since the
reciprocal of zero or of infinity is taken as infinity or zero respectively and the scaled
restriction then vanishes. -/
noncomputable def normalizedRestrict {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Set Ω) : Measure Ω :=
  (P C)⁻¹ • P.restrict C

/-- Given [a measurable sample space](hyp:Ω), [a normed outcome space](hyp:E),
[a measure](hyp:P), [a cell](hyp:C), and [a function](hyp:f), the
[normalized restricted integral](goal) integrates the function against the normalized restriction.

When the cell has positive finite measure this is the expectation of the function under the
probability law obtained by conditioning on the cell; otherwise the normalized restriction is the
zero measure and the integral is zero. -/
noncomputable def normalizedRestrictedIntegral
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (C : Set Ω) (f : Ω → E) : E :=
  ∫ ω, f ω ∂normalizedRestrict P C

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a real function `g`](hyp:g), and
[a measurable space](hyp:Ω), [the normalized restricted integral is the mass quotient](goal). -/
lemma eventCondExp_eq (μ : Measure Ω) (A : Set Ω) (g : Ω → ℝ) :
    normalizedRestrictedIntegral μ A g = (∫ ω in A, g ω ∂μ) / (μ A).toReal := by
  simp only [normalizedRestrictedIntegral, normalizedRestrict,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
  rw [div_eq_inv_mul, smul_eq_mul]

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [finite mass](hyp:hA_fin),
[a real function `f`](hyp:f), and [a measurable space](hyp:Ω),
[the normalized integral satisfies the scaling identity](goal). -/
lemma eventCondExp_mul_measure_toReal (μ : Measure Ω) (A : Set Ω)
    (hA_fin : μ A ≠ ⊤) (f : Ω → ℝ) :
    normalizedRestrictedIntegral μ A f * (μ A).toReal = ∫ ω in A, f ω ∂μ := by
  simp only [eventCondExp_eq]
  by_cases h0 : (μ A).toReal = 0
  · rw [h0, mul_zero]
    have hμ0 : μ A = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
      · exact h
      · exact absurd h hA_fin
    exact (MeasureTheory.setIntegral_measure_zero f hμ0).symm
  · field_simp

/-- For [a finite index type `ι`](hyp:ι), [a finite measure `μ`](hyp:μ),
[measurable cells `A`](hyp:A) that are [measurable](hyp:hmeas),
[pairwise disjoint](hyp:hdisj), and [cover the space](hyp:hcov), and an
[integrable real function `f`](hyp:f,hf) on [a measurable space](hyp:Ω),
[the finite-partition identity holds](goal). -/
lemma integral_eq_sum_measure_mul_eventCondExp
    {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcov : (⋃ i, A i) = Set.univ)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ
      = ∑ i, (μ (A i)).toReal * normalizedRestrictedIntegral μ (A i) f := by
  have hsplit : ∫ ω in (⋃ i, A i), f ω ∂μ = ∑ i, ∫ ω in A i, f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype hmeas hdisj
      (fun _ => hf.integrableOn)
  have hcov' : ∫ ω, f ω ∂μ = ∑ i, ∫ ω in A i, f ω ∂μ := by
    rw [← hsplit, hcov, setIntegral_univ]
  rw [hcov']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm, ← eventCondExp_mul_measure_toReal μ (A i) (measure_ne_top _ _) f]

/-- For [a finite index type `ι`](hyp:ι), [a measure `μ`](hyp:μ),
[a measurable set `A`](hyp:A,hAmeas), [measurable cells `C`](hyp:C,hCmeas) that are
[pairwise disjoint](hyp:hdisj), [cover the space](hyp:hcov), and whose intersections with
`A` have [finite mass](hyp:hAC_fin), and an [integrable function `f`](hyp:f,hf) on
[a measurable space](hyp:Ω), [the mass-ratio cell decomposition holds](goal). -/
lemma eventCondExp_eq_sum_condProb_mul_eventCondExp
    {ι : Type*} [Fintype ι] (μ : Measure Ω)
    (A : Set Ω) (C : ι → Set Ω) (hAmeas : MeasurableSet A)
    (hCmeas : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (Function.onFun Disjoint C))
    (hcov : (⋃ i, C i) = Set.univ)
    (hAC_fin : ∀ i, μ (A ∩ C i) ≠ ⊤)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    normalizedRestrictedIntegral μ A f =
      ∑ i, (μ (A ∩ C i)).toReal / (μ A).toReal *
        normalizedRestrictedIntegral μ (A ∩ C i) f := by
  have hAC_meas : ∀ i, MeasurableSet (A ∩ C i) := fun i => hAmeas.inter (hCmeas i)
  have hAC_disj : Pairwise (Function.onFun Disjoint (fun i => A ∩ C i)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAC_cov : (⋃ i, A ∩ C i) = A := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  have hsplit : ∫ ω in A, f ω ∂μ = ∑ i, ∫ ω in A ∩ C i, f ω ∂μ := by
    have h := MeasureTheory.integral_iUnion_fintype hAC_meas hAC_disj
      (fun _ => hf.integrableOn)
    rwa [hAC_cov] at h
  have hcell : ∀ i, ∫ ω in A ∩ C i, f ω ∂μ =
      (μ (A ∩ C i)).toReal * normalizedRestrictedIntegral μ (A ∩ C i) f := by
    intro i
    rw [mul_comm, ← eventCondExp_mul_measure_toReal μ (A ∩ C i) (hAC_fin i) f]
  have hLHS : normalizedRestrictedIntegral μ A f =
      (∫ ω in A, f ω ∂μ) / (μ A).toReal :=
    eventCondExp_eq μ A f
  rw [hLHS, hsplit, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcell i, mul_div_right_comm]

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a real function `f`](hyp:f),
[a real function `g`](hyp:g), [a measurable space](hyp:Ω), and
[almost-everywhere agreement](hyp:h),
[their normalized restricted integrals are equal](goal). -/
lemma eventCondExp_congr_ae (μ : Measure Ω) (A : Set Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[μ.restrict A] g) :
    normalizedRestrictedIntegral μ A f = normalizedRestrictedIntegral μ A g := by
  simp only [eventCondExp_eq]
  rw [MeasureTheory.integral_congr_ae h]

/-- For [a measure `μ`](hyp:μ), [a measurable set `A`](hyp:A,hA),
[real functions `f` and `g`](hyp:f,g), [a measurable space](hyp:Ω), and
[pointwise agreement on `A`](hyp:h), [their normalized restricted integrals are equal](goal). -/
lemma eventCondExp_congr_on (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A)
    {f g : Ω → ℝ} (h : ∀ ω ∈ A, f ω = g ω) :
    normalizedRestrictedIntegral μ A f = normalizedRestrictedIntegral μ A g := by
  simp only [eventCondExp_eq]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun hA h

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a real function `f`](hyp:f),
[a real function `g`](hyp:g), [a measurable space](hyp:Ω),
[integrability on `A`](hyp:hf,hg), and
[almost-everywhere order](hyp:hfg), [the normalized integral order is preserved](goal). -/
lemma eventCondExp_mono_ae (μ : Measure Ω) {A : Set Ω} {f g : Ω → ℝ}
    (hf : IntegrableOn f A μ) (hg : IntegrableOn g A μ)
    (hfg : f ≤ᵐ[μ.restrict A] g) :
    normalizedRestrictedIntegral μ A f ≤ normalizedRestrictedIntegral μ A g := by
  simp only [eventCondExp_eq]
  have hint_le : ∫ ω in A, f ω ∂μ ≤ ∫ ω in A, g ω ∂μ :=
    MeasureTheory.setIntegral_mono_ae_restrict hf hg hfg
  have hnn : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  exact div_le_div_of_nonneg_right hint_le hnn

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a real function `g₁`](hyp:g₁),
[a real function `g₂`](hyp:g₂), [a measurable space](hyp:Ω), and
[integrability on `A`](hyp:h₁,h₂),
[the normalized restricted integral is additive](goal). -/
lemma eventCondExp_add (μ : Measure Ω) (A : Set Ω)
    {g₁ g₂ : Ω → ℝ}
    (h₁ : IntegrableOn g₁ A μ) (h₂ : IntegrableOn g₂ A μ) :
    normalizedRestrictedIntegral μ A (g₁ + g₂) =
      normalizedRestrictedIntegral μ A g₁ + normalizedRestrictedIntegral μ A g₂ := by
  simp only [eventCondExp_eq, Pi.add_apply, integral_add h₁ h₂, add_div]

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a real function `g₁`](hyp:g₁),
[a real function `g₂`](hyp:g₂), [a measurable space](hyp:Ω), and
[integrability on `A`](hyp:h₁,h₂),
[the normalized restricted integral preserves subtraction](goal). -/
lemma eventCondExp_sub (μ : Measure Ω) (A : Set Ω)
    {g₁ g₂ : Ω → ℝ}
    (h₁ : IntegrableOn g₁ A μ) (h₂ : IntegrableOn g₂ A μ) :
    normalizedRestrictedIntegral μ A (g₁ - g₂) =
      normalizedRestrictedIntegral μ A g₁ - normalizedRestrictedIntegral μ A g₂ := by
  simp only [eventCondExp_eq, Pi.sub_apply, integral_sub h₁ h₂, sub_div]

/-- For [a measure `μ`](hyp:μ), [a set `A`](hyp:A), [a scalar `c`](hyp:c),
[a real function `g`](hyp:g), and [a measurable space](hyp:Ω),
[the normalized restricted integral commutes with scalar multiplication](goal). -/
lemma eventCondExp_smul (μ : Measure Ω) (A : Set Ω) (c : ℝ) (g : Ω → ℝ) :
    normalizedRestrictedIntegral μ A (fun ω => c * g ω) =
      c * normalizedRestrictedIntegral μ A g := by
  simp only [eventCondExp_eq, MeasureTheory.integral_const_mul, mul_div_assoc]

/-- For [measurable spaces](hyp:Ω,α,β), [a measure `μ`](hyp:μ),
[a random element `z`](hyp:z), [a random element `B`](hyp:B), [independence](hyp:hInd),
[their measurability](hyp:hz,hB),
[a real function `factualF`](hyp:factualF), [a measurable real function `h`](hyp:h,hh_meas),
[a point `x`](hyp:x) with [measurable singleton](hyp:hx), [agreement on its preimage](hyp:hF_eq),
and [nonzero finite cell mass](hyp:hμA_ne_zero), [the independence identity holds](goal). -/
theorem eventCondExp_of_ae_eq_IndepFun
    {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure Ω}
    {z : Ω → α} {B : Ω → β}
    (hInd : IndepFun z B μ) (hz : Measurable z) (hB : Measurable B)
    {factualF : Ω → ℝ}
    {h : β → ℝ} (hh_meas : Measurable h) {x : α}
    (hx : MeasurableSet ({x} : Set α))
    (hF_eq : factualF =ᵐ[μ.restrict (z ⁻¹' {x})] fun ω => h (B ω))
    (hμA_ne_zero : (μ (z ⁻¹' {x})).toReal ≠ 0) :
    normalizedRestrictedIntegral μ (z ⁻¹' {x}) factualF = ∫ ω, h (B ω) ∂μ := by
  simp only [eventCondExp_eq]
  rw [MeasureTheory.integral_congr_ae hF_eq]
  rw [hInd.integral_restrict_preimage_eq_mul hz.aemeasurable hB.aemeasurable
    hx (hz hx) hh_meas.aestronglyMeasurable]
  field_simp

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

When the cell has positive finite measure this is bounded-test factorization under the
conditional probability law on the cell. For a null or infinite-measure cell the normalized
restriction is the zero measure and the condition holds trivially, so results using it assume
positive finite cell mass. -/
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

No integrability is required: a coordinate that is not integrable contributes zero, by the
convention for the Bochner integral, so this is the first-moment vector only for integrable
coordinates. -/
noncomputable def firstMomentVector
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ ω, X ω i ∂μ

/-- Given [a measurable sample space, two finite vector dimensions, a measure, and two
finite-dimensional real random vectors](hyp:Ω,m,n,μ,X,Y), the [cross-moment matrix](goal)
has at each ordered pair of coordinates the integral of the product of the corresponding
coordinates of the two random vectors.

No integrability is required: an entry whose coordinate product is not integrable is zero, by
the convention for the Bochner integral, so this is the cross-moment matrix only when every product
is integrable. -/
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

end Causalean.Mathlib.Probability

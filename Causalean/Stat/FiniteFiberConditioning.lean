/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Conditional

/-! # Conditional Independence from Finite Fibers

This file turns elementary probability-mass factorization within every fiber
of a finite-valued conditioning map into conditional independence given that
map. The proof computes conditional expectations of event indicators by
finite-fiber probability ratios.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

/-- The normalized real mass of an event inside one fiber of a finite-valued
map. -/
private noncomputable def finiteCondProb
    {Omega T : Type*} [MeasurableSpace Omega] [MeasurableSpace T]
    (mu : Measure Omega) (X : Omega → T) (A : Set Omega) (x : T) : ℝ :=
  (mu.real (X ⁻¹' {x}))⁻¹ * mu.real ((X ⁻¹' {x}) ∩ A)

/-- A finite-fiber conditional probability is nonnegative. -/
private lemma finiteCondProb_nonneg
    {Omega T : Type*} [MeasurableSpace Omega] [MeasurableSpace T]
    (mu : Measure Omega) (X : Omega → T) (A : Set Omega) (x : T) :
    0 ≤ finiteCondProb mu X A x :=
  mul_nonneg (inv_nonneg.mpr measureReal_nonneg) measureReal_nonneg

/-- Under a finite measure, a finite-fiber conditional probability is at most
one. -/
private lemma finiteCondProb_le_one
    {Omega T : Type*} [MeasurableSpace Omega] [MeasurableSpace T]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega → T) (A : Set Omega) (x : T) :
    finiteCondProb mu X A x ≤ 1 := by
  unfold finiteCondProb
  by_cases hzero : mu.real (X ⁻¹' {x}) = 0
  · simp [hzero]
  · rw [inv_mul_le_one₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero))]
    exact measureReal_mono Set.inter_subset_left

/-- The conditional expectation of an event indicator given a finite-valued
map equals the elementary conditional-probability ratio on each fiber. -/
private lemma condExp_indicator_finite_comap
    {Omega T : Type*} [Finite T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega → T) (hX : Measurable X)
    (A : Set Omega) (hA : MeasurableSet A) :
    mu[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[mu]
      fun omega => finiteCondProb mu X A (X omega) := by
  let _ := Fintype.ofFinite T
  let q : T → ℝ := finiteCondProb mu X A
  have hq : Measurable q := measurable_of_finite q
  have hqm : StronglyMeasurable[MeasurableSpace.comap X
      (inferInstance : MeasurableSpace T)] (q ∘ X) :=
    (hq.comp (comap_measurable X)).stronglyMeasurable
  have hqOmega : StronglyMeasurable (q ∘ X) :=
    (hq.comp hX).stronglyMeasurable
  have hq_int : Integrable (q ∘ X) mu := by
    apply Integrable.of_bound hqOmega.aestronglyMeasurable 1
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans
        (finiteCondProb_nonneg mu X A (X omega))
    · exact finiteCondProb_le_one mu X A (X omega)
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const 1).indicator hA
  have hversion :
      (q ∘ X) =ᵐ[mu]
        mu[A.indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap X (inferInstance : MeasurableSpace T)] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hind
    · intro x _ _
      exact hq_int.integrableOn
    · intro x hx _
      rcases hx with ⟨u, hu, rfl⟩
      classical
      let U : Finset T := Finset.univ.filter (· ∈ u)
      rw [show X ⁻¹' u = ⋃ x ∈ U, X ⁻¹' {x} by
        ext omega
        simp [U]]
      rw [integral_biUnion_finset, integral_biUnion_finset]
      · apply Finset.sum_congr rfl
        intro x hx
        have heq :
            (q ∘ X) =ᵐ[mu.restrict (X ⁻¹' {x})] fun _ => q x := by
          filter_upwards [ae_restrict_mem
            (hX (measurableSet_singleton x))] with omega homega
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at homega
          exact congrArg q homega
        rw [integral_congr_ae heq, integral_const]
        change ((mu.restrict (X ⁻¹' {x})) Set.univ).toReal * q x =
          ∫ y in X ⁻¹' {x}, A.indicator (fun _ => (1 : ℝ)) y ∂mu
        rw [Measure.restrict_apply_univ]
        rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
        unfold q finiteCondProb
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          ((mu.restrict (X ⁻¹' {x})) A).toReal
        rw [Measure.restrict_apply hA, Set.inter_comm A]
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          mu.real ((X ⁻¹' {x}) ∩ A)
        by_cases hzero : mu.real (X ⁻¹' {x}) = 0
        · have hsub : mu.real ((X ⁻¹' {x}) ∩ A) = 0 :=
            le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_left)
              measureReal_nonneg
          simp [hzero, hsub]
        · field_simp
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hind.integrableOn
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hq_int.integrableOn
    · exact hqm.aestronglyMeasurable
  exact hversion.symm

/-- For [a finite measure](hyp:mu), [a finite-valued conditioning map](hyp:X),
[two random elements](hyp:f,g), [measurability of all three
maps](hyp:hX,hf,hg), and [factorization of their ordinary real masses on every
measurable pair of events inside every conditioning fiber](hyp:hfactor), [the
two random elements are conditionally independent given the sigma-algebra
generated by the conditioning map](goal). -/
theorem condIndepFun_finite_of_measureReal_fibers
    {Omega T A B : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Finite T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega → T) (hX : Measurable X)
    (f : Omega → A) (hf : Measurable f)
    (g : Omega → B) (hg : Measurable g)
    (hfactor :
      ∀ (x : T) (s : Set A) (t : Set B),
        MeasurableSet s → MeasurableSet t →
        mu.real (((f ⁻¹' s) ∩ (g ⁻¹' t)) ∩ X ⁻¹' {x}) *
            mu.real (X ⁻¹' {x}) =
          mu.real ((f ⁻¹' s) ∩ X ⁻¹' {x}) *
            mu.real ((g ⁻¹' t) ∩ X ⁻¹' {x})) :
    CondIndepFun (MeasurableSpace.comap X inferInstance)
      hX.comap_le f g mu := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro s t hs ht
  have hfg : MeasurableSet (f ⁻¹' s ∩ g ⁻¹' t) :=
    (hf hs).inter (hg ht)
  have hleft := condExp_indicator_finite_comap mu X hX _ hfg
  have hfiber := condExp_indicator_finite_comap mu X hX _ (hf hs)
  have hgiber := condExp_indicator_finite_comap mu X hX _ (hg ht)
  filter_upwards [hleft, hfiber, hgiber] with omega hleftomega hfomega hgomega
  rw [hleftomega, hfomega, hgomega]
  unfold finiteCondProb
  let m := mu.real (X ⁻¹' {X omega})
  by_cases hm : m = 0
  · simp only [m] at hm
    simp [hm]
  · have hfac := hfactor (X omega) s t hs ht
    simp only [Set.inter_assoc] at hfac
    change m⁻¹ *
        mu.real (X ⁻¹' {X omega} ∩ (f ⁻¹' s ∩ g ⁻¹' t)) =
      (m⁻¹ * mu.real (X ⁻¹' {X omega} ∩ f ⁻¹' s)) *
        (m⁻¹ * mu.real (X ⁻¹' {X omega} ∩ g ⁻¹' t))
    have hfac' :
        mu.real (X ⁻¹' {X omega} ∩ (f ⁻¹' s ∩ g ⁻¹' t)) * m =
          mu.real (X ⁻¹' {X omega} ∩ f ⁻¹' s) *
            mu.real (X ⁻¹' {X omega} ∩ g ⁻¹' t) := by
      simpa [m, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        hfac
    field_simp
    simpa [mul_comm] using hfac'

end Causalean.Stat

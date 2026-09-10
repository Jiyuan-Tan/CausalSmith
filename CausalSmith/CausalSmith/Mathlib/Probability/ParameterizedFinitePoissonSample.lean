import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic

/-!
# Parameterized finite Poisson sample kernels

This file turns an atomwise measurable family of probability measures on a
finite discrete space into the corresponding Markov kernel of finite samples
with an independent Poisson sample size.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Mathlib.Probability

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Singletons are measurable in the space of finite samples whenever
singletons are measurable in the observation space. -/
noncomputable instance finiteSampleMeasurableSingletonClass
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] :
    MeasurableSingletonClass (FiniteSample X) where
  measurableSet_singleton s := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet ((Sigma.mk n) ⁻¹' {s})
    rcases s with ⟨m, x⟩
    by_cases hnm : n = m
    · subst m
      convert MeasurableSet.singleton x using 1
      ext y
      simp
    · convert MeasurableSet.empty using 1
      ext y
      simp [hnm]

/-- The mass of a finite Poisson sample singleton is its Poisson count mass
times the product of the observation atom masses. -/
lemma finitePoissonSampleLaw_singleton
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) (s : FiniteSample X) :
    finitePoissonSampleLaw P lam {s} =
      poissonMeasure lam {s.count} * ∏ i, P {s.points i} := by
  classical
  have hpre : fixedSizeEmbed s.count ⁻¹' ({s} : Set (FiniteSample X)) =
      ({s.points} : Set (Fin s.count → X)) := by
    ext x
    rcases s with ⟨n, y⟩
    simp only [FiniteSample.count, FiniteSample.points]
    constructor
    · intro h
      cases h
      rfl
    · intro h
      cases h
      rfl
  have hsubset : ({s} : Set (FiniteSample X)) ⊆
      FiniteSample.count ⁻¹' ({s.count} : Set ℕ) := by
    rintro t rfl
    simp
  calc
    finitePoissonSampleLaw P lam {s} =
        finitePoissonSampleLaw P lam
          ({s} ∩ FiniteSample.count ⁻¹' ({s.count} : Set ℕ)) := by
      rw [Set.inter_eq_left.mpr hsubset]
    _ = (finitePoissonSampleLaw P lam).restrict
          (FiniteSample.count ⁻¹' ({s.count} : Set ℕ)) {s} := by
      rw [Measure.restrict_apply (MeasurableSet.singleton s)]
    _ = poissonMeasure lam {s.count} * ∏ i, P {s.points i} := by
      rw [finitePoissonSampleLaw_restrict_count_eq, Measure.smul_apply,
        Measure.map_apply (measurable_fixedSizeEmbed s.count)
          (MeasurableSet.singleton s), hpre, Measure.pi_singleton, smul_eq_mul]

/-- An atomwise measurable family of probability laws on a finite discrete
space induces the exact finite-Poisson-sample Markov kernel. -/
noncomputable def parameterizedFinitePoissonSampleKernel
    {Θ X : Type*} [MeasurableSpace Θ] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : ∀ x, Measurable (fun θ ↦ P θ {x})) (lam : ℝ≥0) :
    Kernel Θ (FiniteSample X) where
  toFun θ := finitePoissonSampleLaw (P θ) lam
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hatom (s : FiniteSample X) :
        Measurable (fun θ ↦ finitePoissonSampleLaw (P θ) lam {s}) := by
      simp_rw [finitePoissonSampleLaw_singleton]
      exact measurable_const.mul
        (Finset.measurable_prod Finset.univ fun i _hi ↦ hP (s.points i))
    have hsum : Measurable (fun θ ↦ ∑' s : FiniteSample X,
        A.indicator (fun s ↦ finitePoissonSampleLaw (P θ) lam {s}) s) :=
      Measurable.ennreal_tsum fun s ↦ by
      by_cases hs : s ∈ A
      · simpa [Set.indicator_of_mem hs] using hatom s
      · simp [Set.indicator, hs]
    convert hsum using 1
    funext θ
    exact (Measure.tsum_indicator_apply_singleton
      (finitePoissonSampleLaw (P θ) lam) A hA).symm

/-- The parameterized finite Poisson sample kernel has the requested law at
every parameter. -/
@[simp]
lemma parameterizedFinitePoissonSampleKernel_apply
    {Θ X : Type*} [MeasurableSpace Θ] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : ∀ x, Measurable (fun θ ↦ P θ {x})) (lam : ℝ≥0) (θ : Θ) :
    parameterizedFinitePoissonSampleKernel P hP lam θ =
      finitePoissonSampleLaw (P θ) lam := rfl

instance parameterizedFinitePoissonSampleKernel_isMarkovKernel
    {Θ X : Type*} [MeasurableSpace Θ] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : ∀ x, Measurable (fun θ ↦ P θ {x})) (lam : ℝ≥0) :
    IsMarkovKernel (parameterizedFinitePoissonSampleKernel P hP lam) where
  isProbabilityMeasure θ := by
    change IsProbabilityMeasure (finitePoissonSampleLaw (P θ) lam)
    infer_instance

end CausalSmith.Mathlib.Probability

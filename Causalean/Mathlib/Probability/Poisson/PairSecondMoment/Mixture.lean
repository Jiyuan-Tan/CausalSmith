module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Two independent finite Poisson count fibres

The nonnegative integral of a statistic of two independent finite Poisson
samples is a double mixture of fixed-size iid-array integrals. This isolates
the count decomposition needed for real-valued moment calculations.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A finite-sample measure is the sum of its disjoint count restrictions. -/
private lemma finiteSample_count_sum {Z : Type*} [MeasurableSpace Z]
    (μ : Measure (FiniteSample Z)) :
    μ = Measure.sum (fun k : ℕ =>
      μ.restrict (FiniteSample.count ⁻¹' ({k} : Set ℕ))) := by
  have hcover : (⋃ k : ℕ, FiniteSample.count (X := Z) ⁻¹' ({k} : Set ℕ)) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact ⟨z.count, rfl⟩
  calc
    μ = μ.restrict Set.univ := (Measure.restrict_univ).symm
    _ = μ.restrict (⋃ k : ℕ, FiniteSample.count ⁻¹' ({k} : Set ℕ)) := by rw [hcover]
    _ = Measure.sum (fun k : ℕ =>
          μ.restrict (FiniteSample.count ⁻¹' ({k} : Set ℕ))) :=
      Measure.restrict_iUnion
        (fun i j hij => (Set.disjoint_singleton.mpr hij).preimage FiniteSample.count)
        (fun k => measurable_finiteSample_count (measurableSet_singleton k))

/-- Given [two probability observation laws](hyp:P,Q), [their nonnegative
Poisson rates](hyp:rateA,rateB), and [a measurable nonnegative statistic of
their finite samples](hyp:f,hf), [its integral is the double Poisson-weighted
series of fixed-count iid-array integrals](goal). -/
theorem lintegral_pair_count_mixture
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (rateA rateB : ℝ≥0)
    (f : FiniteSample X × FiniteSample Y → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ p, f p ∂((finitePoissonSampleLaw P rateA).prod
      (finitePoissonSampleLaw Q rateB))) =
      ∑' m : ℕ, ∑' n : ℕ,
        (poissonMeasure rateA) ({m} : Set ℕ) *
          (poissonMeasure rateB) ({n} : Set ℕ) *
            (∫⁻ p : (Fin m → X) × (Fin n → Y),
              f (⟨m, p.1⟩, ⟨n, p.2⟩)
              ∂((Measure.pi fun _ : Fin m => P).prod
                (Measure.pi fun _ : Fin n => Q))) := by
  let μA := finitePoissonSampleLaw P rateA
  let μB := finitePoissonSampleLaw Q rateB
  change ∫⁻ p, f p ∂(μA.prod μB) = _
  rw [finiteSample_count_sum μA, finiteSample_count_sum μB,
    Measure.prod_sum, lintegral_sum_measure,
    ENNReal.tsum_prod']
  congr 1
  funext m
  congr 1
  funext n
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq,
    Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_prod_map _ _ (measurable_fixedSizeEmbed m)
      (measurable_fixedSizeEmbed n), lintegral_smul_measure,
    lintegral_smul_measure, lintegral_map hf
      ((measurable_fixedSizeEmbed m).prodMap (measurable_fixedSizeEmbed n))]
  simp only [smul_eq_mul, Prod.map, fixedSizeEmbed, mul_assoc]

/-- Given [two probability observation laws](hyp:P,Q), [their nonnegative
Poisson rates](hyp:rateA,rateB), and [an integrable real statistic of their
finite samples](hyp:f,hf), [its expectation is the double Poisson-weighted
series of fixed-count iid-array expectations](goal). -/
theorem integral_pair_count_mixture
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (rateA rateB : ℝ≥0)
    (f : FiniteSample X × FiniteSample Y → ℝ)
    (hf : Integrable f ((finitePoissonSampleLaw P rateA).prod
      (finitePoissonSampleLaw Q rateB))) :
    (∫ p, f p ∂((finitePoissonSampleLaw P rateA).prod
      (finitePoissonSampleLaw Q rateB))) =
      ∑' m : ℕ, ∑' n : ℕ,
        ((poissonMeasure rateA) ({m} : Set ℕ)).toReal *
          ((poissonMeasure rateB) ({n} : Set ℕ)).toReal *
            (∫ p : (Fin m → X) × (Fin n → Y),
              f (⟨m, p.1⟩, ⟨n, p.2⟩)
              ∂((Measure.pi fun _ : Fin m => P).prod
                (Measure.pi fun _ : Fin n => Q))) := by
  -- Expand both laws by their disjoint count fibres as in the preceding
  -- nonnegative theorem. Use `integral_sum_measure hf` twice; integrability
  -- descends to each fibre by `Integrable.mono_measure`. Then rewrite each
  -- fibre with `finitePoissonSampleLaw_restrict_count_eq`, map-product
  -- compatibility, and `integral_smul_measure`.
  let μA := finitePoissonSampleLaw P rateA
  let μB := finitePoissonSampleLaw Q rateB
  change Integrable f (μA.prod μB) at hf
  change ∫ p, f p ∂(μA.prod μB) = _
  rw [finiteSample_count_sum μA, finiteSample_count_sum μB,
    Measure.prod_sum] at hf ⊢
  rw [integral_sum_measure hf]
  rw [(hasSum_integral_measure hf).summable.tsum_prod]
  congr 1
  funext m
  congr 1
  funext n
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq,
    Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_prod_map _ _ (measurable_fixedSizeEmbed m)
      (measurable_fixedSizeEmbed n), integral_smul_measure,
    integral_smul_measure]
  by_cases hA : (poissonMeasure rateA) ({m} : Set ℕ) = 0
  · simp [hA]
  by_cases hB : (poissonMeasure rateB) ({n} : Set ℕ) = 0
  · simp [hB]
  have hFibre : Integrable f
      ((μA.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ))).prod
        (μB.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)))) := by
    apply hf.mono_measure
    exact Measure.le_sum _ (m, n)
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_prod_map _ _ (measurable_fixedSizeEmbed m)
      (measurable_fixedSizeEmbed n)] at hFibre
  have hmap : AEStronglyMeasurable f
      (Measure.map (Prod.map (fixedSizeEmbed m) (fixedSizeEmbed n))
        ((Measure.pi fun _ : Fin m => P).prod
          (Measure.pi fun _ : Fin n => Q))) :=
    ((aemeasurable_smul_measure_iff (mul_ne_zero hA hB)).mp
      hFibre.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  rw [integral_map
    ((measurable_fixedSizeEmbed m).prodMap (measurable_fixedSizeEmbed n)).aemeasurable
    hmap]
  simp only [smul_eq_mul, Prod.map, fixedSizeEmbed, mul_assoc]

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment

module
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent-copy Jensen reduction for path sums

The squared norm of a centered finite sum of Bochner-integrable paths is
bounded by the expected squared norm of its difference from an independent
copy. Independence among the summands is not needed for this reduction.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- For finitely many random continuous paths that are
[Bochner-integrable](hyp:hWint) and [have
integrable squared supremum norm](hyp:hWsq), [the expected squared supremum
norm of the centered sum of the paths is at most the expected squared
supremum norm of the summed differences between two independent draws of
the paths](goal).

Independence among the summands is not needed.
-/
theorem centered_path_sum_energy_le_copy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (W : Fin n → Ω → Path)
    (hWint : ∀ j, Integrable (W j) μ)
    (hWsq : ∀ j, Integrable (fun ω => ‖W j ω‖ ^ 2) μ) :
    (∫ ω, ‖∑ j, (W j ω - ∫ x, W j x ∂μ)‖ ^ 2 ∂μ) ≤
      ∫ ω, ∫ ω', ‖∑ j, (W j ω - W j ω')‖ ^ 2 ∂μ ∂μ := by
  /- For fixed ω, the centered sum is the Bochner mean over ω' of the
  difference. Apply convexity/Jensen for the squared norm, then integrate in
  ω. Derive product integrability from the individual second moments. -/
  let S : Ω → Path := fun ω => ∑ j, W j ω
  have hSi : Integrable S μ := by
    simpa [S] using integrable_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => hWint j)
  have hS2 : Integrable (fun ω => ‖S ω‖ ^ 2) μ := by
    apply (memLp_two_iff_integrable_sq_norm hSi.aestronglyMeasurable).mp
    have hj : ∀ j, MemLp (W j) 2 μ := fun j =>
      (memLp_two_iff_integrable_sq_norm (hWint j).aestronglyMeasurable).mpr (hWsq j)
    simpa [S] using memLp_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ => hj j)
  have hD2 : Integrable (fun p : Ω × Ω => ‖S p.1 - S p.2‖ ^ 2) (μ.prod μ) := by
    have hDm : AEStronglyMeasurable (fun p : Ω × Ω => S p.1 - S p.2) (μ.prod μ) := by
      exact AEStronglyMeasurable.sub
        (AEStronglyMeasurable.comp_fst hSi.aestronglyMeasurable)
        (AEStronglyMeasurable.comp_snd hSi.aestronglyMeasurable)
    apply (memLp_two_iff_integrable_sq_norm hDm).mp
    have h1 : MemLp (fun p : Ω × Ω => S p.1) 2 (μ.prod μ) :=
      (memLp_two_iff_integrable_sq_norm
        (AEStronglyMeasurable.comp_fst hSi.aestronglyMeasurable)).mpr
        (Integrable.comp_fst hS2 μ)
    have h2 : MemLp (fun p : Ω × Ω => S p.2) 2 (μ.prod μ) :=
      (memLp_two_iff_integrable_sq_norm
        (AEStronglyMeasurable.comp_snd hSi.aestronglyMeasurable)).mpr
        (Integrable.comp_snd hS2 μ)
    change MemLp ((fun p : Ω × Ω => S p.1) - (fun p : Ω × Ω => S p.2)) 2 (μ.prod μ)
    exact h1.sub h2
  have hRi : Integrable (fun ω => ∫ ω', ‖S ω - S ω'‖ ^ 2 ∂μ) μ := by
    exact hD2.integral_prod_left
  have hconv : ConvexOn ℝ Set.univ (fun x : Path => ‖x‖ ^ 2) := by
    change ConvexOn ℝ Set.univ ((norm : Path → ℝ) ^ 2)
    exact (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : Path → ℝ)).pow
      (by intro x hx; exact norm_nonneg x) 2
  have hpoint (ω : Ω) :
      ‖S ω - ∫ x, S x ∂μ‖ ^ 2 ≤ ∫ ω', ‖S ω - S ω'‖ ^ 2 ∂μ := by
    have hDi : Integrable (fun ω' => S ω - S ω') μ :=
      (integrable_const _).sub hSi
    have hDi2 : Integrable (fun ω' => ‖S ω - S ω'‖ ^ 2) μ := by
      apply (memLp_two_iff_integrable_sq_norm hDi.aestronglyMeasurable).mp
      change MemLp ((fun _ : Ω => S ω) - S) 2 μ
      exact (memLp_const (S ω)).sub
        ((memLp_two_iff_integrable_sq_norm hSi.aestronglyMeasurable).mpr hS2)
    have hj := hconv.map_integral_le (by fun_prop) isClosed_univ (by simp) hDi
      (by simpa [Function.comp_def] using hDi2)
    simpa [integral_sub (integrable_const _) hSi, IsProbabilityMeasure.measure_univ]
      using hj
  have hCi : Integrable (fun ω => ‖S ω - ∫ x, S x ∂μ‖ ^ 2) μ := by
    have hC : Integrable (fun ω => S ω - ∫ x, S x ∂μ) μ := hSi.sub (integrable_const _)
    apply (memLp_two_iff_integrable_sq_norm hC.aestronglyMeasurable).mp
    change MemLp (S - fun _ : Ω => ∫ x, S x ∂μ) 2 μ
    exact ((memLp_two_iff_integrable_sq_norm hSi.aestronglyMeasurable).mpr hS2).sub
      (memLp_const (∫ x, S x ∂μ))
  have hmain := integral_mono hCi hRi hpoint
  simpa only [S, integral_finsetSum (Finset.univ : Finset (Fin n))
    (fun j _ => hWint j), Finset.sum_sub_distrib] using hmain

end Causalean.Stat.Concentration.BoundedVariation

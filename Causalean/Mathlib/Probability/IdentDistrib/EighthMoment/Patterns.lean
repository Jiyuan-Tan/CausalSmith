module

public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Counting
public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Scalar
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product integration of repeated index patterns

An eight-slot product is regrouped by coordinate multiplicities before applying finite-product
integration. A singleton fiber contributes the centered first moment, hence makes the integral
zero. For patterns with no singleton fibers, each used coordinate contributes at most the
second moment of a bounded mark.

Use `Finset.prod_fiberwise'` to regroup the product and
`MeasureTheory.integral_fintype_prod_eq_prod` for independence. The latter theorem imposes no
measurability or integrability hypotheses; integrability is separately supplied for sum-integral
interchange.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Under [an iid probability product law](hyp:μ), the integral of an eight-slot
coordinate product specified by [an index map](hyp:a) is [the product of the scalar
moments indexed by coordinate multiplicities](goal), for [any real mark](hyp:g). -/
theorem integral_pattern_factorization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (a : Fin 8 → ι) :
    (∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ)) =
      ∏ r : ι, ∫ y, g y ^ multiplicity a r ∂μ := by
  -- Pointwise regroup via `Finset.prod_fiberwise'`, rewriting each fiber product as a power.
  -- Then apply `integral_fintype_prod_eq_prod` to the coordinate-dependent powers.
  have hprod (x : ι → Ω) :
      (∏ j : Fin 8, g (x (a j))) = ∏ r : ι, g (x r) ^ multiplicity a r := by
    simpa [multiplicity] using
      (Finset.prod_fiberwise' Finset.univ a (fun r => g (x r))).symm
  simp_rw [hprod]
  exact integral_fintype_prod_eq_prod (fun r y => g y ^ multiplicity a r)

omit [DecidableEq ι] in
/-- An eight-slot coordinate product of a [measurable mark](hyp:hg) with
[absolute value at most one](hyp:hb), specified by [an index map](hyp:a), is
[integrable](goal) under [an iid probability product law](hyp:μ). -/
@[fun_prop]
theorem integrable_pattern (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1) (a : Fin 8 → ι) :
    Integrable (fun x : ι → Ω => ∏ j : Fin 8, g (x (a j)))
      (Measure.pi (fun _ : ι => μ)) := by
  classical
  have hm : Measurable (fun x : ι → Ω => ∏ j : Fin 8, g (x (a j))) := by
    fun_prop
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one (fun j _ => abs_nonneg _) (fun j _ => hb _)

/-- If [a real mark has zero mean](hyp:hcenter) and [a coordinate occurs exactly
once](hyp:hr) in [an eight-slot map](hyp:a), the corresponding product has
[zero integral](goal) under [an iid probability product law](hyp:μ). -/
theorem integral_pattern_eq_zero_of_singleton (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hcenter : (∫ y, g y ∂μ) = 0)
    (a : Fin 8 → ι) (r : ι) (hr : multiplicity a r = 1) :
    (∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ)) = 0 := by
  -- Factorization has a zero factor at r, since its multiplicity is one.
  rw [integral_pattern_factorization]
  exact Finset.prod_eq_zero (Finset.mem_univ r) (by simpa [hr] using hcenter)

/-- For [a measurable mark](hyp:hg) with [absolute value at most one](hyp:hb), an
eight-slot product specified by [a map without singleton fibers](hyp:ha) has
[absolute integral bounded by its second moment raised to the image size](goal) under
[an iid probability product law](hyp:μ). -/
theorem abs_integral_pattern_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1)
    (a : Fin 8 → ι) (ha : NoSingleton a) :
    |∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ)| ≤
      (∫ y, g y ^ 2 ∂μ) ^ (patternImage a).card := by
  -- Factorize, remove unused coordinates (power 0 integrates to 1 under a probability law),
  -- and use `abs_integral_pow_le_secondMoment` for every used coordinate.
  rw [integral_pattern_factorization, Finset.abs_prod]
  have hrestrict :
      (∏ r ∈ patternImage a, |∫ y, g y ^ multiplicity a r ∂μ|) =
        ∏ r : ι, |∫ y, g y ^ multiplicity a r ∂μ| := by
    apply Finset.prod_subset (Finset.subset_univ (patternImage a))
    intro r _ hr
    have hzero : multiplicity a r = 0 := by
      unfold multiplicity
      rw [Finset.filter_eq_empty_iff.mpr ?_, Finset.card_empty]
      intro j hj hjr
      exact hr (Finset.mem_image.mpr ⟨j, hj, hjr⟩)
    simp [hzero]
  rw [← hrestrict]
  calc
    _ ≤ ∏ r ∈ patternImage a, (∫ y, g y ^ 2 ∂μ) :=
      Finset.prod_le_prod (fun r _ => abs_nonneg _)
        (fun r hr => abs_integral_pow_le_secondMoment μ g hg hb _ (ha r hr))
    _ = _ := Finset.prod_const _

end Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

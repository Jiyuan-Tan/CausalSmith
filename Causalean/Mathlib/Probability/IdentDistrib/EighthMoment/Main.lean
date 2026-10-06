module

public import Causalean.Mathlib.Probability.IdentDistrib.EighthMoment.Patterns

/-!
# Eighth moment of a centered bounded iid sum over a finite coordinate subset

The headline theorem `iid_centered_bounded_sum_eighth_moment` applies to a measurable real
mark in [0,1], any finite coordinate type, and any finite subset of those coordinates. It bounds
the eighth moment of the centered sum by 8! times the sum of the fourth and first powers of
subset size times the mark's variance. Empty subsets and empty coordinate types are allowed.

The proof expands via `Finset.sum_pow'`, cancels singleton fibers by product integration,
bounds the other patterns by variance powers, and applies the generic counting theorem.
`centered_sum_eighth_moment_le` also exposes the useful mean-zero, absolute-bound-one version.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- For a [measurable mark](hyp:hg) with [absolute value at most one](hyp:hb), the
eighth moment of its sum on [a finite coordinate subset](hyp:S) is [the sum of the
integrals of all supported eight-slot products](goal) under [an iid probability law](hyp:μ). -/
theorem integral_eighth_sum_eq_pattern_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1) (S : Finset ι) :
    (∫ x : ι → Ω, (∑ r ∈ S, g (x r)) ^ 8 ∂Measure.pi (fun _ : ι => μ)) =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin 8 => S),
        ∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ) := by
  -- Rewrite pointwise by `Finset.sum_pow'`, then use `integral_finsetSum` and
  -- `integrable_pattern` for each term. No independence argument is needed in this step.
  classical
  have hexpand (x : ι → Ω) := Finset.sum_pow' S (fun r => g (x r)) 8
  simp_rw [hexpand]
  exact integral_finsetSum _ (fun a _ => integrable_pattern μ g hg hb a)

/-- For a [measurable mark](hyp:hg) with [absolute value at most one](hyp:hb) and
[zero mean](hyp:hcenter), the eighth moment of its sum on [a finite coordinate
subset](hyp:S) is [bounded by the second-moment-weighted surviving patterns](goal)
under [an iid probability law](hyp:μ). -/
theorem integral_eighth_sum_le_survivors (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1)
    (hcenter : (∫ y, g y ∂μ) = 0) (S : Finset ι) :
    (∫ x : ι → Ω, (∑ r ∈ S, g (x r)) ^ 8 ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ a ∈ survivingPatterns S, (∫ y, g y ^ 2 ∂μ) ^ (patternImage a).card := by
  -- Start with the expansion above. If ¬NoSingleton a, a used coordinate has
  -- positive multiplicity <2, hence multiplicity 1; cancel using
  -- `integral_pattern_eq_zero_of_singleton`. Keep only the filter, use le_abs_self,
  -- and apply `abs_integral_pattern_le` termwise.
  classical
  rw [integral_eighth_sum_eq_pattern_sum μ g hg hb S]
  have hrestrict :
      (∑ a ∈ survivingPatterns S,
        ∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ)) =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin 8 => S),
        ∫ x : ι → Ω, (∏ j : Fin 8, g (x (a j))) ∂Measure.pi (fun _ : ι => μ) := by
    apply Finset.sum_subset (Finset.filter_subset NoSingleton _)
    intro a ha hnot
    have hn : ¬NoSingleton a := fun h => hnot (Finset.mem_filter.mpr ⟨ha, h⟩)
    simp only [NoSingleton] at hn
    push Not at hn
    obtain ⟨r, hr, hlt⟩ := hn
    have hpos : 0 < multiplicity a r := by
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    exact integral_pattern_eq_zero_of_singleton μ g hcenter a r (by omega)
  rw [← hrestrict]
  apply Finset.sum_le_sum
  intro a ha
  exact (le_abs_self _).trans
    (abs_integral_pattern_le μ g hg hb a (Finset.mem_filter.mp ha).2)

omit [DecidableEq ι] in
/-- A [measurable mark](hyp:hg) with [absolute value at most one](hyp:hb) and
[zero mean](hyp:hcenter) has its [eighth moment over a finite coordinate
subset](hyp:S) [bounded by eight factorial times the first and fourth powers of
subset size times its second moment](goal) under [an iid probability law](hyp:μ). -/
theorem centered_sum_eighth_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ y, |g y| ≤ 1)
    (hcenter : (∫ y, g y ∂μ) = 0) (S : Finset ι) :
    (∫ x : ι → Ω, (∑ r ∈ S, g (x r)) ^ 8 ∂Measure.pi (fun _ : ι => μ)) ≤
      (Nat.factorial 8 : ℝ) *
        (((S.card : ℝ) * (∫ y, g y ^ 2 ∂μ)) ^ 4 +
          (S.card : ℝ) * (∫ y, g y ^ 2 ∂μ)) := by
  classical
  exact (integral_eighth_sum_le_survivors μ g hg hb hcenter S).trans
    (weighted_survivingPatterns_le S _ (integral_nonneg (fun y => sq_nonneg (g y))))

omit [DecidableEq ι] in
/-- A [measurable real mark](hyp:hf) [valued in the unit interval](hyp:h0,h1) has
its [centered sum over any finite coordinate subset](hyp:S) [bounded in eighth
moment by eight factorial times the fourth plus first powers of subset size times
the one-mark variance](goal) under [an iid probability product law](hyp:μ). -/
theorem iid_centered_bounded_sum_eighth_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1)
    (S : Finset ι) :
    (∫ x : ι → Ω, (∑ r ∈ S, (f (x r) - ∫ y, f y ∂μ)) ^ 8
      ∂Measure.pi (fun _ : ι => μ)) ≤
      (Nat.factorial 8 : ℝ) *
        (((S.card : ℝ) * variance f μ) ^ 4 + (S.card : ℝ) * variance f μ) := by
  have h := centered_sum_eighth_moment_le μ (fun y => f y - ∫ z, f z ∂μ)
    (hf.sub measurable_const) (abs_centered_mark_le_one μ f hf h0 h1)
    (integral_centered_mark_eq_zero μ f hf h0 h1) S
  rw [← variance_eq_integral hf.aemeasurable] at h
  exact h

example {n : ℕ} (μ : Measure ↥(Set.Icc (0 : ℝ) 1)) [IsProbabilityMeasure μ]
    (S : Finset (Fin n)) :
    (∫ x : Fin n → ↥(Set.Icc (0 : ℝ) 1),
      (∑ r ∈ S, ((x r : ℝ) - ∫ y, (y : ℝ) ∂μ)) ^ 8
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      (Nat.factorial 8 : ℝ) *
        (((S.card : ℝ) * variance (fun y : ↥(Set.Icc (0 : ℝ) 1) => (y : ℝ)) μ) ^ 4 +
          (S.card : ℝ) * variance (fun y : ↥(Set.Icc (0 : ℝ) 1) => (y : ℝ)) μ) := by
  exact iid_centered_bounded_sum_eighth_moment μ (fun y => (y : ℝ))
    measurable_subtype_coe (fun y => y.property.1) (fun y => y.property.2) S

end Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

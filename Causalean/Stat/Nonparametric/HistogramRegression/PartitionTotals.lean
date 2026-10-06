module
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic

/-!
# Integration over the positive-mass partition

These label-API bridges reuse Mathlib's finite disjoint-union integral theorem,
then remove zero-mass fibers. They supply the partition sum for integrated risk
and the mass-one simplification for a constant cubical oscillation envelope.
Zero-mass cells are retained in the estimator and omitted only from integrals.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [A measurable finite partition and covariates](hyp:hlabel,hX) and
[an integrable observation function](hyp:hf) give
[its integral as the sum of set integrals over positive-mass cells](goal). -/
theorem integral_eq_sum_positive_cells
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (f : Ω → ℝ) (hlabel : Measurable label) (hX : Measurable X)
    (hf : Integrable f μ) :
    (∫ ω, f ω ∂μ) =
      ∑ k ∈ positiveCells μ label X, ∫ ω in cell label X k, f ω ∂μ := by
  -- Apply integral_iUnion_fintype to the measurable label fibers: distinct
  -- fibers are disjoint and their union is univ. Use Finset.sum_subset to
  -- remove the labels outside positiveCells. For each omitted cell, nonnegative
  -- toReal mass and finite measure imply measure zero, hence restrict_eq_zero.
  have hmeas : ∀ k, MeasurableSet (cell label X k) := fun k =>
    (measurableSet_singleton k).preimage (hlabel.comp hX)
  have hdisj : Pairwise (Function.onFun Disjoint (cell label X)) := by
    intro i j hij
    change Disjoint (cell label X i) (cell label X j)
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.symm.trans hj)
  have hcover : (⋃ k, cell label X k) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨label (X ω), rfl⟩
  calc
    (∫ ω, f ω ∂μ) = ∑ k : κ, ∫ ω in cell label X k, f ω ∂μ := by
      simpa only [hcover, Measure.restrict_univ] using
        (integral_iUnion_fintype hmeas hdisj (fun _ => hf.integrableOn))
    _ = ∑ k ∈ positiveCells μ label X, ∫ ω in cell label X k, f ω ∂μ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hnpos : ¬ 0 < cellMass μ label X k := by
        simpa only [positiveCells, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      have hz : (μ (cell label X k)).toReal = 0 :=
        le_antisymm (le_of_not_gt hnpos) ENNReal.toReal_nonneg
      have hzero : μ (cell label X k) = 0 :=
        ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top μ _)
      rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]

/-- [Measurable finite partition labels and covariates](hyp:hlabel,hX) imply
[the real masses of the positive-mass cells sum to one](goal). -/
theorem sum_positiveCells_mass
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (hlabel : Measurable label) (hX : Measurable X) :
    (∑ k ∈ positiveCells μ label X, cellMass μ label X k) = 1 := by
  -- Apply integral_eq_sum_positive_cells to the constant function 1 and
  -- simplify setIntegral_const, cellMass, and measure_univ. This reuses the
  -- finite integral partition law rather than reproving a measure sum law.
  have h := integral_eq_sum_positive_cells μ label X (fun _ => (1 : ℝ))
    hlabel hX (integrable_const 1)
  simpa [cellMass, setIntegral_const, Measure.real] using h.symm

end

end Causalean.Stat.Nonparametric.HistogramRegression

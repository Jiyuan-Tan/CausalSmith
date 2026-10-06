module
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuous paths of bounded variation

This module fixes the compact time interval, the path norm and total variation,
and a continuous cumulative-variation control used in continuum chaining.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The time domain](goal) is [the closed real interval from zero to
one](step:1).
-/
abbrev Time : Type := Set.Icc (0 : ℝ) 1

/-- [A path](goal) is [a continuous real-valued function on the closed
unit time interval](step:1).
-/
abbrev Path : Type := C(Time, ℝ)

/-- [The σ-algebra on continuous paths](goal) is [the Borel σ-algebra of
the uniform-norm topology](step:1).
-/
noncomputable instance : MeasurableSpace Path := borel Path

/-- [The left endpoint of the time interval](goal) is [the time
0](step:1).
-/
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩

/-- [The right endpoint of the time interval](goal) is [the time
1](step:1).
-/
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩

/-- [The total variation](goal) of [a continuous path f](hyp:f) is [its
extended total variation over the unit interval, converted to a real
number](step:1).

For a bounded-variation path this is its ordinary total variation; a path
of infinite variation is assigned the value 0.
-/
noncomputable def pathTV (f : Path) : ℝ := (eVariationOn f Set.univ).toReal

/-- [The size](goal) of [a continuous path f](hyp:f) is [its supremum
norm plus its total variation](step:1).
-/
noncomputable def pathSize (f : Path) : ℝ := ‖f‖ + pathTV f

/-- [The real-valued total variation of every path is
nonnegative](goal).
-/
theorem pathTV_nonneg (f : Path) : 0 ≤ pathTV f := by
  exact ENNReal.toReal_nonneg

/-- [The supremum-plus-variation size of every path is
nonnegative](goal).
-/
theorem pathSize_nonneg (f : Path) : 0 ≤ pathSize f := by
  exact add_nonneg (norm_nonneg _) (pathTV_nonneg f)

/-- [Total variation is a Borel-measurable function of a continuous path
under the uniform-norm topology](goal).

The proof takes a supremum over rational partitions, then converts the
extended-real variation to a real number.
-/
@[fun_prop] theorem measurable_pathTV : Measurable pathTV := by
  have h : LowerSemicontinuous (fun f : Path => eVariationOn f Set.univ) := by
    intro f
    apply eVariationOn.lowerSemicontinuous_aux
    intro x _
    exact (continuous_eval_const x).tendsto f
  let : BorelSpace Path := ⟨rfl⟩
  exact h.measurable.ennreal_toReal

/-- If [a continuous path has bounded variation](hyp:hf), then [it has a
continuous nondecreasing cumulative-variation control that starts at zero,
ends at the path's total variation, and dominates every ordered increment of
the path](goal).
-/
theorem exists_variation_control (f : Path)
    (hf : eVariationOn f Set.univ < ⊤) :
    ∃ v : Path, Monotone (v : Time → ℝ) ∧
      v timeZero = 0 ∧ v timeOne = pathTV f ∧
      ∀ s t : Time, s ≤ t → |f t - f s| ≤ v t - v s := by
  have hbf : BoundedVariationOn (f : Time → ℝ) Set.univ := ne_of_lt hf
  let w : Time → ℝ := variationOnFromTo f Set.univ timeZero
  have hw_cont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro x
    apply continuousAt_iff_continuous_left_right.mpr
    constructor
    · rw [← continuousWithinAt_Iio_iff_Iic]
      have h := variationOnFromTo.tendsto_left (s := Set.univ) (a := timeZero)
        (b := x) (l := f x) (Set.mem_univ _) (Set.mem_univ _)
        hbf.locallyBoundedVariationOn
        (f.continuous.continuousAt.mono_left (nhdsWithin_le_nhds))
      simpa [ContinuousWithinAt, w, Set.univ_inter] using h
    · rw [← continuousWithinAt_Ioi_iff_Ici]
      have h := variationOnFromTo.tendsto_right (s := Set.univ) (a := timeZero)
        (b := x) (l := f x) (Set.mem_univ _) (Set.mem_univ _)
        hbf.locallyBoundedVariationOn
        (f.continuous.continuousAt.mono_left (nhdsWithin_le_nhds))
      simpa [ContinuousWithinAt, w, Set.univ_inter] using h
  refine ⟨⟨w, hw_cont⟩, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact (variationOnFromTo.monotoneOn hbf.locallyBoundedVariationOn
      (Set.mem_univ timeZero)) (Set.mem_univ s) (Set.mem_univ t) hst
  · exact variationOnFromTo.self f Set.univ timeZero
  · have hinterval : Set.Icc timeZero timeOne = Set.univ := by
      ext x
      simp only [Set.mem_Icc, Set.mem_univ, iff_true]
      exact ⟨x.property.1, x.property.2⟩
    change variationOnFromTo f Set.univ timeZero timeOne = pathTV f
    have h01 : timeZero ≤ timeOne := by
      change (0 : ℝ) ≤ 1
      norm_num
    rw [variationOnFromTo.eq_of_le f Set.univ h01]
    simp [hinterval, pathTV]
  · intro s t hst
    exact variationOnFromTo.abs_sub_le_sub_of_le hbf.locallyBoundedVariationOn
      (Set.mem_univ timeZero) (Set.mem_univ s) (Set.mem_univ t) hst

end Causalean.Stat.Concentration.BoundedVariation

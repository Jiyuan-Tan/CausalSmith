module
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Finite conditional averages of continuous paths

For a finite auxiliary experiment, a conditional average is a finite weighted
sum of continuous paths. Convexity of squared uniform norm gives a pointwise
inequality and therefore contracts its expected squared path risk.
-/

public section

open MeasureTheory
open Causalean.Stat.Concentration.BoundedVariation

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [Nonnegative finite weights summing to one](hyp:weight,hw_nonneg,hw_sum) and [continuous paths](hyp:Z) give [a squared-supremum Jensen inequality for their weighted average](goal). -/
-- Apply finite Jensen to `ConvexOn ℝ Set.univ (fun z : Path => ‖z‖^2)`;
-- `convexOn_univ_norm` and `.pow` establish the convexity premise.
theorem finite_path_average_sq_norm_le
    {A : Type*} [Fintype A]
    (weight : A → ℝ) (hw_nonneg : ∀ a, 0 ≤ weight a)
    (hw_sum : ∑ a, weight a = 1) (Z : A → Path) :
    ‖∑ a, weight a • Z a‖ ^ 2 ≤
      ∑ a, weight a * ‖Z a‖ ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun z : Path => ‖z‖ ^ 2) := by
    have hnorm : ConvexOn ℝ Set.univ (norm : Path → ℝ) := convexOn_univ_norm
    convert hnorm.pow (fun z _ => norm_nonneg z) 2 using 1 <;> rfl
  simpa only [Finset.sum_smul, smul_eq_mul] using
    hconv.map_sum_le (t := Finset.univ) (w := weight) (p := Z)
      (fun a _ => hw_nonneg a) (by simpa using hw_sum) (fun _ _ => Set.mem_univ _)

/-- Under [a probability law](hyp:μ), [measurable nonnegative auxiliary weights that sum to one](hyp:weight,hw_nonneg,hw_sum,hw_meas), [measurable continuous paths](hyp:Z,hZ_meas), and [an integrable weighted squared-path cost](hyp:hcost), [finite conditional averaging contracts expected squared supremum risk](goal). -/
-- The observation space may be infinite (in particular, a table of Poisson
-- counts). Prove measurability of the finite weighted sum from `hw_meas` and
-- `hZ_meas`. Pointwise Jensen gives domination by the integrable right side;
-- derive left integrability using this domination and apply `integral_mono`.
theorem finite_conditional_path_risk_le
    {X A : Type*} [Fintype A] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (weight : X → A → ℝ) (hw_nonneg : ∀ x a, 0 ≤ weight x a)
    (hw_sum : ∀ x, ∑ a, weight x a = 1)
    (hw_meas : ∀ a, Measurable (fun x => weight x a))
    (Z : X → A → Path) (hZ_meas : ∀ a, Measurable (fun x => Z x a))
    (hcost : Integrable (fun x => ∑ a, weight x a * ‖Z x a‖ ^ 2) μ) :
    (∫ x, ‖∑ a, weight x a • Z x a‖ ^ 2 ∂μ) ≤
      ∫ x, ∑ a, weight x a * ‖Z x a‖ ^ 2 ∂μ := by
  let : BorelSpace Path := ⟨rfl⟩
  have hpath : Measurable (fun x => ∑ a, weight x a • Z x a) := by
    have hsum : StronglyMeasurable
        (∑ a, fun x : X => weight x a • Z x a) := by
      apply Finset.stronglyMeasurable_sum
      intro a ha
      exact (hw_meas a).stronglyMeasurable.smul (hZ_meas a).stronglyMeasurable
    convert hsum.measurable using 1
    ext x
    simp
  have hleft : Measurable (fun x => ‖∑ a, weight x a • Z x a‖ ^ 2) :=
    hpath.norm.pow_const 2
  have hpoint (x : X) :
      ‖∑ a, weight x a • Z x a‖ ^ 2 ≤
        ∑ a, weight x a * ‖Z x a‖ ^ 2 :=
    finite_path_average_sq_norm_le (weight x) (hw_nonneg x) (hw_sum x) (Z x)
  have hleft_int : Integrable (fun x => ‖∑ a, weight x a • Z x a‖ ^ 2) μ :=
    hcost.mono_nonneg hleft.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall hpoint)
  exact integral_mono hleft_int hcost hpoint

end Causalean.Stat.Concentration.BoundedVariation

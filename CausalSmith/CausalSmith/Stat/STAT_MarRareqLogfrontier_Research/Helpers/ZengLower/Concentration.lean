module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedTable
public import Mathlib.Probability.Moments.Variance

/-! Chebyshev concentration and conditioning for iid relaxed rare-cell priors. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

private lemma iid_sum_integral {d : ℕ} {ν : Measure MarkedParam}
    [IsProbabilityMeasure ν] (f : MarkedParam → ℝ)
    (hf : Integrable f ν) :
    (∫ z : Fin d → MarkedParam, ∑ x, f (z x) ∂Measure.pi (fun _ : Fin d => ν)) =
      d * ∫ t, f t ∂ν := by
  rw [integral_finsetSum]
  · calc
      ∑ x : Fin d, ∫ z, f (z x) ∂Measure.pi (fun _ : Fin d => ν) =
          ∑ _x : Fin d, ∫ t, f t ∂ν := by
            apply Finset.sum_congr rfl
            intro x hx
            exact integral_comp_eval (μ := fun _ : Fin d => ν)
              (i := x) hf.aestronglyMeasurable
      _ = d * ∫ t, f t ∂ν := by simp
  · intro x hx
    exact integrable_comp_eval (μ := fun _ : Fin d => ν) (i := x) hf

private lemma iid_sum_chebyshev {d : ℕ} {ν : Measure MarkedParam}
    [IsProbabilityMeasure ν] (f : MarkedParam → ℝ)
    (hf : StronglyMeasurable f) {b r : ℝ} (hr : 0 < r)
    (hbound : ∀ᵐ t ∂ν, f t ∈ Set.Icc 0 b) :
    Measure.pi (fun _ : Fin d => ν)
        {z | r ≤ |(∑ x, f (z x)) - d * ∫ t, f t ∂ν|} ≤
      ENNReal.ofReal (d * b ^ 2 / r ^ 2) := by
  have hfLp : MemLp f 2 ν := memLp_of_bounded hbound hf.aestronglyMeasurable 2
  have hsum_eq : (fun z : Fin d → MarkedParam => ∑ x, f (z x)) =
      (∑ i : Fin d, fun z => f (z i)) := by
    funext z
    simp only [Finset.sum_apply]
  have hsumLp : MemLp (fun z : Fin d → MarkedParam => ∑ x, f (z x)) 2
      (Measure.pi (fun _ : Fin d => ν)) := by
    rw [hsum_eq]
    exact memLp_finsetSum' (Finset.univ : Finset (Fin d)) fun i hi =>
      hfLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin d => ν) i)
  have hvar : variance (fun z : Fin d → MarkedParam => ∑ x, f (z x))
      (Measure.pi (fun _ : Fin d => ν)) ≤ d * b ^ 2 := by
    rw [hsum_eq]
    rw [variance_sum_pi (fun _ : Fin d => hfLp)]
    calc
      ∑ _i : Fin d, variance f ν ≤ ∑ _i : Fin d, ((b - 0) / 2) ^ 2 := by
        exact Finset.sum_le_sum fun i hi =>
          variance_le_sq_of_bounded hbound hf.aestronglyMeasurable.aemeasurable
      _ ≤ d * b ^ 2 := by
        simp only [sum_const, card_fin, nsmul_eq_mul]
        nlinarith [sq_nonneg b]
  rw [← iid_sum_integral f (hfLp.integrable (by norm_num))]
  refine (meas_ge_le_variance_div_sq hsumLp hr).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hvar (sq_nonneg r)

/-- For [the specified inputs and assumptions](hyp:d,ν,massRadius,targetRadius,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def iidRareGood {d : ℕ} (ν : Measure MarkedParam)
    (massRadius targetRadius : ℝ) (z : Fin d → MarkedParam) : Prop :=
  |(∑ x, (z x).1) - d * ∫ t, t.1 ∂ν| < massRadius ∧
    |(∑ x, targetFunctional (z x)) -
      d * ∫ t, targetFunctional t ∂ν| < targetRadius

private theorem measurableSet_iidRareGood {d : ℕ} (ν : Measure MarkedParam)
    (massRadius targetRadius : ℝ) :
    MeasurableSet {z : Fin d → MarkedParam |
      iidRareGood ν massRadius targetRadius z} := by
  change MeasurableSet
    ({z : Fin d → MarkedParam |
      |(∑ x, (z x).1) - d * ∫ t, t.1 ∂ν| < massRadius} ∩
    {z : Fin d → MarkedParam |
      |(∑ x, targetFunctional (z x)) -
        d * ∫ t, targetFunctional t ∂ν| < targetRadius})
  apply MeasurableSet.inter
  · exact measurableSet_lt (by fun_prop) measurable_const
  · exact measurableSet_lt (by
      unfold targetFunctional
      fun_prop) measurable_const

end CausalSmith.Stat.MarRareqLogfrontier

module

public import Causalean.Stat.Bootstrap.EfronResampling.FiniteRepresentation

/-!
# Measurability of data-dependent bootstrap event probabilities

This module supplies the joint-measurability bridge needed when a conditional bootstrap event
depends on both the observed data and the resample.  The finite atomic representation of Efron
resampling reduces the conditional probability to a finite sum of measurable indicators.
-/

public section

namespace Causalean.Stat

open MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- For [a jointly measurable event in the data and resample](hyp:A,hA), [its probability under
the data-dependent Efron resampling law is a measurable function of the observed data](goal). -/
theorem measurable_bootstrapResample_real_of_measurableSet
    {n : ℕ} (A : Set ((Fin n → X) × (Fin n → X))) (hA : MeasurableSet A) :
    Measurable (fun x : Fin n → X ↦
      (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.measurable
  · rw [show (fun x : Fin n → X ↦
        (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) =
        fun x ↦ ((n : ℝ) ^ n)⁻¹ *
          ∑ j : Fin n → Fin n, if (x, x ∘ j) ∈ A then 1 else 0 by
      funext x
      have hsection : MeasurableSet {xstar | (x, xstar) ∈ A} :=
        hA.preimage (measurable_const.prodMk measurable_id)
      rw [bootstrapResample_eq_average_dirac, Measure.real, Measure.smul_apply,
        Measure.finsetSum_apply]
      simp only [Measure.dirac_apply' _ hsection, smul_eq_mul]
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
        ENNReal.toReal_natCast]
      rw [ENNReal.toReal_sum (by
        intro j hj
        by_cases h : (x, x ∘ j) ∈ A <;> simp [Set.indicator, h])]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : (x, x ∘ j) ∈ A <;> simp [Set.indicator, h]]
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro j hj
    have hcomp : Measurable (fun x : Fin n → X ↦ x ∘ j) := by
      refine measurable_pi_iff.mpr fun i ↦ ?_
      exact measurable_pi_apply (j i)
    exact Measurable.ite
      (hA.preimage (measurable_id.prodMk hcomp)) measurable_const measurable_const

end

end Causalean.Stat

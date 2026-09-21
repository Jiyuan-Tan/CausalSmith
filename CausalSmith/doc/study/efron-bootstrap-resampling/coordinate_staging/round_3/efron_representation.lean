module
public import Causalean.Stat.Bootstrap.Efron
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite atomic representation of the Efron bootstrap

This module expands the product of empirical measures into the uniform atomic law on all index
maps `Fin n → Fin n`.  It also records the corresponding exact finite-average integration rule.
-/

public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- For [a data vector](hyp:x), [the Efron resampling law is the uniform atomic measure on all
`n^n` index resamples](goal), with duplicate data values retained through their index
multiplicities. -/
theorem bootstrapResample_eq_average_dirac (x : Fin n → X) :
    bootstrapResample x =
      ((n : ℝ≥0∞) ^ n)⁻¹ •
        ∑ j : Fin n → Fin n, Measure.dirac (x ∘ j) := by
  -- Proof plan: express one empirical coordinate as the map of the uniform atomic law on
  -- `Fin n`, commute coordinatewise map with `Measure.pi`, and expand the finite product.
  -- The empty-index case is `Measure.pi_of_empty`; the successor case distributes the product
  -- over a finite sum and uses `Measure.map_dirac'`.
  classical
  by_cases hn : n = 0
  · subst n
    simp only [bootstrapResample, empiricalMeasure,
      Causalean.Stat.Concentration.finiteSampleMeasure, Finset.univ_eq_empty,
      Finset.sum_empty, smul_zero, Nat.cast_zero, pow_zero, inv_one, one_smul,
      Fintype.sum_unique]
    rw [Measure.pi_of_empty _ (x ∘ default)]
  · let _ : IsProbabilityMeasure (empiricalMeasure x) :=
      empiricalMeasure_isProbabilityMeasure x hn
    unfold bootstrapResample
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
    unfold empiricalMeasure Causalean.Stat.Concentration.finiteSampleMeasure
    simp_rw [Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ (hs _), smul_eq_mul]
    rw [ENNReal.ofReal_natCast, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.inv_pow]
    rw [Fintype.prod_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : x ∘ j ∈ Set.univ.pi s
    · have hi : ∀ i, x (j i) ∈ s i := by
        simpa [Set.mem_pi] using h
      simp [Set.indicator, h, hi]
    · have hi : ∃ i, x (j i) ∉ s i := by
        simpa [Set.mem_pi] using h
      obtain ⟨i, hi⟩ := hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      · exact Set.indicator_of_notMem h (1 : (Fin n → X) → ℝ≥0∞)
      · exact Set.indicator_of_notMem hi (1 : X → ℝ≥0∞)

/-- For [a data vector](hyp:x) and [a real-valued function of its resamples](hyp:f) that is
[measurable](hyp:hf), [its bootstrap expectation is the ordinary average over all `n^n` index
resamples](goal). -/
theorem integral_bootstrapResample_eq_average (x : Fin n → X)
    (f : (Fin n → X) → ℝ) (hf : Measurable f) :
    ∫ y, f y ∂bootstrapResample x =
      ((n : ℝ) ^ n)⁻¹ * ∑ j : Fin n → Fin n, f (x ∘ j) := by
  -- Proof plan: rewrite by `bootstrapResample_eq_average_dirac`, then use
  -- `integral_smul_measure`, `integral_finsetSum_measure`, and `integral_dirac'`.
  rw [bootstrapResample_eq_average_dirac, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac' f _ hf.stronglyMeasurable, smul_eq_mul,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  · intro j hj
    exact integrable_dirac' hf.stronglyMeasurable (by simp)

end

end Causalean.Stat

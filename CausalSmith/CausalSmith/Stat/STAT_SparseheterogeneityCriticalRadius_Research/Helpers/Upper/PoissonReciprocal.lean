module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Bias
public import Causalean.Mathlib.Probability.Poisson.InverseMoments
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments

/-! The guarded inverse-count moment used by the heavy correction. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

@[no_expose]
noncomputable def guardedNatReciprocal (z : ℕ) : ℝ :=
  if z = 0 then 0 else 1 / (z : ℝ)

@[simp] lemma guardedNatReciprocal_zero : guardedNatReciprocal 0 = 0 := by
  rw [guardedNatReciprocal]
  simp

lemma guardedNatReciprocal_of_ne {z : ℕ} (hz : z ≠ 0) :
    guardedNatReciprocal z = 1 / (z : ℝ) := by
  rw [guardedNatReciprocal, if_neg hz]

lemma guardedNatReciprocal_integrable (lambda : ℝ≥0) :
    Integrable guardedNatReciprocal (poissonMeasure lambda) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with z
  by_cases hz : z = 0
  · simp [guardedNatReciprocal, hz]
  · rw [guardedNatReciprocal, if_neg hz, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hzpos : (0 : ℝ) < z := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_one hzpos).mpr
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)

/-- Equation (38), including the zero-rate endpoint. -/
lemma poisson_guarded_reciprocal_le_min (lambda : ℝ≥0) :
    (∫ z : ℕ, guardedNatReciprocal z ∂poissonMeasure lambda) ≤
      min (lambda : ℝ) (2 / (lambda : ℝ)) := by
  have hf := guardedNatReciprocal_integrable lambda
  have hcount := (poisson_natCast_memLp_two lambda).integrable (by norm_num)
  have hshift := (shifted_reciprocal_memLp_two lambda).integrable (by norm_num)
  have hleCount (z : ℕ) : guardedNatReciprocal z ≤ (z : ℝ) := by
    by_cases hz : z = 0
    · simp [guardedNatReciprocal, hz]
    · rw [guardedNatReciprocal, if_neg hz]
      have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hzpos : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz1
      rw [div_le_iff₀ hzpos]
      nlinarith [sq_nonneg ((z : ℝ) - 1)]
  have hRate : (∫ z : ℕ, guardedNatReciprocal z ∂poissonMeasure lambda) ≤
      (lambda : ℝ) := by
    calc
      _ ≤ ∫ z : ℕ, (z : ℝ) ∂poissonMeasure lambda :=
        integral_mono hf hcount hleCount
      _ = _ := poisson_count_first_moment lambda
  by_cases hlambda : lambda = 0
  · subst lambda
    simpa using hRate
  · have hlam : (0 : ℝ) < lambda := by exact_mod_cast pos_iff_ne_zero.mpr hlambda
    have hleShift (z : ℕ) : guardedNatReciprocal z ≤
        2 * (((z + 1 : ℕ) : ℝ))⁻¹ := by
      by_cases hz : z = 0
      · simp [guardedNatReciprocal, hz]
      · rw [guardedNatReciprocal, if_neg hz]
        have hzpos : (0 : ℝ) < z := by
          exact_mod_cast Nat.pos_of_ne_zero hz
        rw [inv_eq_one_div]
        rw [show 2 * (1 / (((z + 1 : ℕ) : ℝ))) =
          2 / (((z + 1 : ℕ) : ℝ)) by ring]
        norm_num only [Nat.cast_add, Nat.cast_one]
        apply (div_le_div_iff₀ hzpos (by positivity : (0 : ℝ) < z + 1)).mpr
        norm_num
        exact_mod_cast (show z + 1 ≤ 2 * z by omega)
    have htwoInt : Integrable
        (fun z : ℕ => 2 * (((z + 1 : ℕ) : ℝ))⁻¹)
        (poissonMeasure lambda) := hshift.const_mul 2
    have hmul : (lambda : ℝ) *
        (∫ z : ℕ, guardedNatReciprocal z ∂poissonMeasure lambda) ≤ 2 := by
      calc
        _ ≤ (lambda : ℝ) *
            (∫ z : ℕ, 2 * (((z + 1 : ℕ) : ℝ))⁻¹
              ∂poissonMeasure lambda) := by
          exact mul_le_mul_of_nonneg_left
            (integral_mono hf htwoInt hleShift) hlam.le
        _ = 2 * (1 - Real.exp (-(lambda : ℝ))) := by
          rw [integral_const_mul]
          calc
            (lambda : ℝ) * (2 * ∫ z : ℕ, (((z + 1 : ℕ) : ℝ))⁻¹
                ∂poissonMeasure lambda) =
              2 * ((lambda : ℝ) * ∫ z : ℕ, (((z + 1 : ℕ) : ℝ))⁻¹
                ∂poissonMeasure lambda) := by ring
            _ = _ := by rw [shifted_reciprocal_first_moment]
        _ ≤ 2 := by
          have : 0 ≤ Real.exp (-(lambda : ℝ)) := Real.exp_nonneg _
          linarith
    have hInv : (∫ z : ℕ, guardedNatReciprocal z ∂poissonMeasure lambda) ≤
        2 / (lambda : ℝ) := (le_div_iff₀ hlam).mpr (by simpa [mul_comm] using hmul)
    exact le_min hRate hInv

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

module
public import Causalean.Stat.EmpiricalProcess.Countable.ScalarSigns
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ScoreMean

/-!
# Exact sign moments for the revealed-source reverse test

The independent assignment signs have exact weighted second and fourth moments.
These identities supply the finite-row moment calculations in the reverse test.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
open Causalean.Stat.EmpiricalProcess.Countable
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The actual independent assignment expectation equals the uniform Boolean average.  [For the stated data and conditions](hyp:d,f), [the stated conclusion holds](goal). -/
-- @node: integral_halfBernoulli_eq_signAverage
lemma integral_halfBernoulli_eq_signAverage (d : ℕ) (f : Assign (Fin d) → ℝ) :
    (∫ z, f z ∂halfBernoulli (Fin d)) = signAverage f := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  have hmass (z : Assign (Fin d)) :
      (halfBernoulli (Fin d)) {z} = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ d) := by
    rw [halfBernoulli, Measure.pi_singleton]
    have hc (b : Bool) : bernoulliLaw (1 / 2) {b} = ENNReal.ofReal (1 / 2) := by
      cases b <;> simp [bernoulliLaw, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply', measurableSet_singleton] <;> norm_num [ENNReal.ofReal_div_of_pos]
    simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [integral_fintype (halfBernoulli_integrable f)]
  simp only [measureReal_def, hmass, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2 : ℝ)⁻¹ ^ d), smul_eq_mul, ← Finset.mul_sum, signAverage]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- Weighted independent centered signs have their coefficient energy as second moment.  [For the stated data and conditions](hyp:d,a), [the stated conclusion holds](goal). -/
-- @node: reverse_sign_second_moment
lemma reverse_sign_second_moment (d : ℕ) (a : Fin d → ℝ) :
    (∫ z, (∑ j, signOf (z j) * a j) ^ 2 ∂halfBernoulli (Fin d)) = ∑ j, a j ^ 2 := by
  rw [integral_halfBernoulli_eq_signAverage]
  have hs (b : Bool) : signOf b = if b then (1 : ℝ) else -1 := by cases b <;> rfl
  simp_rw [hs]
  rw [signAverage, (signSum_moments d a).1]
  exact mul_div_cancel_left₀ _ (pow_ne_zero d (by norm_num))

/-- The fourth moment retains the exact diagonal correction, rather than a loose bound.  [For the stated data and conditions](hyp:d,a), [the stated conclusion holds](goal). -/
-- @node: reverse_sign_fourth_moment
lemma reverse_sign_fourth_moment (d : ℕ) (a : Fin d → ℝ) :
    (∫ z, (∑ j, signOf (z j) * a j) ^ 4 ∂halfBernoulli (Fin d)) =
      3 * (∑ j, a j ^ 2) ^ 2 - 2 * ∑ j, a j ^ 4 := by
  rw [integral_halfBernoulli_eq_signAverage]
  have hs (b : Bool) : signOf b = if b then (1 : ℝ) else -1 := by cases b <;> rfl
  simp_rw [hs]
  exact signAverage_fourth_exact a

/-- Summing two coefficient levels counts the revealed coordinates exactly.  [For the stated data and conditions](hyp:d,R,u,v), [the stated conclusion holds](goal). -/
-- @node: reverse_two_level_sum
lemma reverse_two_level_sum (d : ℕ) (R : Finset (Fin d)) (u v : ℝ) :
    (∑ j : Fin d, if j ∈ R then u else v) = d * v + R.card * (u - v) := by
  have he (j : Fin d) : (if j ∈ R then u else v) =
      v + (if j ∈ R then u - v else 0) := by split_ifs <;> ring
  simp_rw [he]
  simp [Finset.sum_add_distrib, Finset.sum_ite_mem]
  ring

/-- A revealed sum over r coordinates has second moment r.  [For the stated data and conditions](hyp:d,R), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_second_moment
lemma reverse_revealed_second_moment (d : ℕ) (R : Finset (Fin d)) :
    (∫ z, (∑ j ∈ R, signOf (z j)) ^ 2 ∂halfBernoulli (Fin d)) = R.card := by
  have h := reverse_sign_second_moment d (fun j => if j ∈ R then 1 else 0)
  simpa [mul_ite, Finset.sum_ite_mem] using h

/-- Polarizing second moments gives E[AT] = r for revealed and total sign sums.  [For the stated data and conditions](hyp:d,R), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_total_product_mean
lemma reverse_revealed_total_product_mean (d : ℕ) (R : Finset (Fin d)) :
    (∫ z, (∑ j ∈ R, signOf (z j)) * (∑ j : Fin d, signOf (z j))
      ∂halfBernoulli (Fin d)) = R.card := by
  let A : Assign (Fin d) → ℝ := fun z => ∑ j ∈ R, signOf (z j)
  let T : Assign (Fin d) → ℝ := fun z => ∑ j : Fin d, signOf (z j)
  have h := reverse_sign_second_moment d (fun j => if j ∈ R then 2 else 1)
  have hA := reverse_revealed_second_moment d R
  have hT := reverse_sign_second_moment d (fun _ => 1)
  have he (z : Assign (Fin d)) :
      (∑ j, signOf (z j) * (if j ∈ R then 2 else 1)) = A z + T z := by
    have hj (j : Fin d) : signOf (z j) * (if j ∈ R then 2 else 1) =
        (if j ∈ R then signOf (z j) else 0) + signOf (z j) := by split_ifs <;> ring
    simp_rw [hj]
    simp [Finset.sum_add_distrib, Finset.sum_ite_mem, A, T]
  simp_rw [he] at h
  norm_num [ite_pow, reverse_two_level_sum] at h
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hT
  change (∫ z, A z ^ 2 ∂halfBernoulli (Fin d)) = _ at hA
  change (∫ z, T z ^ 2 ∂halfBernoulli (Fin d)) = _ at hT
  have hp : (∫ z, (A z + T z) ^ 2 ∂halfBernoulli (Fin d)) =
      (∫ z, A z ^ 2 ∂halfBernoulli (Fin d)) +
      2 * (∫ z, A z * T z ∂halfBernoulli (Fin d)) +
      (∫ z, T z ^ 2 ∂halfBernoulli (Fin d)) := by
    have he (z : Assign (Fin d)) : (A z + T z) ^ 2 =
        A z ^ 2 + 2 * (A z * T z) + T z ^ 2 := by ring
    simp_rw [he]
    rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_const_mul]
  change (∫ z, A z * T z ∂halfBernoulli (Fin d)) = _
  rw [h, hA, hT] at hp
  linarith

/-- A revealed sum over r coordinates has fourth moment 3r² − 2r.  [For the stated data and conditions](hyp:d,R), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_fourth_moment
lemma reverse_revealed_fourth_moment (d : ℕ) (R : Finset (Fin d)) :
    (∫ z, (∑ j ∈ R, signOf (z j)) ^ 4 ∂halfBernoulli (Fin d)) =
      3 * (R.card : ℝ) ^ 2 - 2 * R.card := by
  have h := reverse_sign_fourth_moment d (fun j => if j ∈ R then 1 else 0)
  simpa [mul_ite, Finset.sum_ite_mem] using h

/-- Polarizing exact fourth moments yields the mixed revealed/total second moment.
The coordinates outside R remain observed assignment coordinates.  [For the stated data and conditions](hyp:d,R), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_total_mixed_moment
lemma reverse_revealed_total_mixed_moment (d : ℕ) (R : Finset (Fin d)) :
    (∫ z, (∑ j ∈ R, signOf (z j)) ^ 2 * (∑ j : Fin d, signOf (z j)) ^ 2
      ∂halfBernoulli (Fin d)) =
      (R.card : ℝ) * d + 2 * R.card * (R.card - 1 : ℝ) := by
  let A : Assign (Fin d) → ℝ := fun z => ∑ j ∈ R, signOf (z j)
  let T : Assign (Fin d) → ℝ := fun z => ∑ j : Fin d, signOf (z j)
  have hplus := reverse_sign_fourth_moment d (fun j => if j ∈ R then 2 else 1)
  have hminus := reverse_sign_fourth_moment d (fun j => if j ∈ R then 0 else -1)
  have hA := reverse_revealed_fourth_moment d R
  have hT := reverse_sign_fourth_moment d (fun _ => 1)
  have heplus (z : Assign (Fin d)) :
      (∑ j, signOf (z j) * (if j ∈ R then 2 else 1)) = A z + T z := by
    have he (j : Fin d) : signOf (z j) * (if j ∈ R then 2 else 1) =
        (if j ∈ R then signOf (z j) else 0) + signOf (z j) := by split_ifs <;> ring
    simp_rw [he]
    simp [Finset.sum_add_distrib, Finset.sum_ite_mem, A, T]
  have heminus (z : Assign (Fin d)) :
      (∑ j, signOf (z j) * (if j ∈ R then 0 else -1)) = A z - T z := by
    have he (j : Fin d) : signOf (z j) * (if j ∈ R then 0 else -1) =
        (if j ∈ R then signOf (z j) else 0) - signOf (z j) := by split_ifs <;> ring
    simp_rw [he]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_mem, A, T]
  simp_rw [heplus] at hplus
  simp_rw [heminus] at hminus
  norm_num [ite_pow, reverse_two_level_sum] at hplus hminus
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hT
  change (∫ z, A z ^ 4 ∂halfBernoulli (Fin d)) = _ at hA
  change (∫ z, T z ^ 4 ∂halfBernoulli (Fin d)) = _ at hT
  have hpol : (∫ z, (A z + T z) ^ 4 ∂halfBernoulli (Fin d)) +
      (∫ z, (A z - T z) ^ 4 ∂halfBernoulli (Fin d)) =
      2 * (∫ z, A z ^ 4 ∂halfBernoulli (Fin d)) +
      12 * (∫ z, A z ^ 2 * T z ^ 2 ∂halfBernoulli (Fin d)) +
      2 * (∫ z, T z ^ 4 ∂halfBernoulli (Fin d)) := by
    rw [← integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _)]
    have he (z : Assign (Fin d)) :
        (A z + T z) ^ 4 + (A z - T z) ^ 4 =
          2 * A z ^ 4 + 12 * (A z ^ 2 * T z ^ 2) + 2 * T z ^ 4 := by ring
    simp_rw [he]
    rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _)]
    simp only [integral_const_mul]
  change (∫ z, A z ^ 2 * T z ^ 2 ∂halfBernoulli (Fin d)) = _
  rw [hplus, hminus, hA, hT] at hpol
  nlinarith only [hpol]

/-- The mixed row moment is at most 3rd, including the empty revealed set.  [For the stated data and conditions](hyp:d,R), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_total_mixed_moment_le
lemma reverse_revealed_total_mixed_moment_le (d : ℕ) (R : Finset (Fin d)) :
    (∫ z, (∑ j ∈ R, signOf (z j)) ^ 2 * (∑ j : Fin d, signOf (z j)) ^ 2
      ∂halfBernoulli (Fin d)) ≤ 3 * R.card * d := by
  rw [reverse_revealed_total_mixed_moment]
  have hr : (R.card : ℝ) ≤ d := by
    exact_mod_cast (show R.card ≤ d by simpa using R.card_le_univ)
  nlinarith [mul_nonneg (Nat.cast_nonneg R.card) (sub_nonneg.mpr hr)]

/-- The independent reveal count in a size-d row has expectation dp.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_reveal_count_mean
lemma reverse_reveal_count_mean (d : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r : Fin d → Bool, ((Finset.univ.filter (fun j => r j = true)).card : ℝ)
      ∂Measure.pi (fun _ : Fin d => bernoulliLaw p)) = d * p := by
  let := bernoulliLaw_probability p hp
  have he (r : Fin d → Bool) :
      ((Finset.univ.filter (fun j => r j = true)).card : ℝ) =
        ∑ j : Fin d, treatment (r j) := by
    simp [treatment, Finset.sum_boole]
  simp_rw [he]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hc (j : Fin d) :
      (∫ r : Fin d → Bool, treatment (r j)
        ∂Measure.pi (fun _ : Fin d => bernoulliLaw p)) = p := by
    rw [integral_comp_eval (by fun_prop : AEStronglyMeasurable treatment (bernoulliLaw p))]
    rw [show bernoulliLaw p = Causalean.Mathlib.Probability.bernoulliBool p by
      unfold bernoulliLaw Causalean.Mathlib.Probability.bernoulliBool
      exact add_comm _ _]
    rw [Causalean.Mathlib.Probability.bernoulliBool_integral hp.1 hp.2]
    simp [treatment]
  simp [hc]

/-- Averaging the conditional sign second moment gives E A² = dp.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_second_moment_average
lemma reverse_revealed_second_moment_average (d : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r : Fin d → Bool, (∫ z, (∑ j ∈ Finset.univ.filter (fun j => r j = true),
      signOf (z j)) ^ 2 ∂halfBernoulli (Fin d))
        ∂Measure.pi (fun _ : Fin d => bernoulliLaw p)) = d * p := by
  simp_rw [reverse_revealed_second_moment]
  exact reverse_reveal_count_mean d p hp

/-- Averaging the revealed/total sign product gives E[AT] = dp.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_total_product_mean_average
lemma reverse_revealed_total_product_mean_average (d : ℕ) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (∫ r : Fin d → Bool, (∫ z, (∑ j ∈ Finset.univ.filter (fun j => r j = true),
      signOf (z j)) * (∑ j : Fin d, signOf (z j)) ∂halfBernoulli (Fin d))
        ∂Measure.pi (fun _ : Fin d => bernoulliLaw p)) = d * p := by
  simp_rw [reverse_revealed_total_product_mean]
  exact reverse_reveal_count_mean d p hp

/-- Independent reveals and exact sign moments give E[A²T²] ≤ 3d²p.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_revealed_total_mixed_moment_average_le
lemma reverse_revealed_total_mixed_moment_average_le (d : ℕ) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (∫ r : Fin d → Bool, (∫ z, (∑ j ∈ Finset.univ.filter (fun j => r j = true),
      signOf (z j)) ^ 2 * (∑ j : Fin d, signOf (z j)) ^ 2 ∂halfBernoulli (Fin d))
        ∂Measure.pi (fun _ : Fin d => bernoulliLaw p)) ≤ 3 * (d : ℝ) ^ 2 * p := by
  let := bernoulliLaw_probability p hp
  calc
    _ ≤ ∫ r : Fin d → Bool, 3 *
        ((Finset.univ.filter (fun j => r j = true)).card : ℝ) * d
          ∂Measure.pi (fun _ : Fin d => bernoulliLaw p) :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite)
        (fun r => reverse_revealed_total_mixed_moment_le d _)
    _ = 3 * (d : ℝ) ^ 2 * p := by
      rw [integral_mul_const, integral_const_mul, reverse_reveal_count_mean d p hp]
      ring

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

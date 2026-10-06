module
public import Causalean.Mathlib.Probability.Birthday.Finite

/-!
# Binomial count moments for birthday averaging

The binomial weights have unit mass, expected count equal to the trial mean,
and expected unordered pair count equal to the pair scale.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

/-- The [binomial weights for a trial count](hyp:T) and
[success probability](hyp:eta) [sum to one](goal). -/
theorem binomialAverage_one (T : ℕ) (eta : ℝ) :
    binomialAverage T eta (fun _ => 1) = 1 := by
  unfold binomialAverage
  simp only [mul_one]
  calc
    (∑ r ∈ Finset.range (T + 1),
      Causalean.Mathlib.Probability.binomialWeight T eta r) =
        (eta + (1 - eta)) ^ T := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Causalean.Mathlib.Probability.binomialWeight]
      ring
    _ = 1 := by ring

/-- The [binomial average for a trial count](hyp:T) and
[success probability](hyp:eta) of the [count](goal) equals its mean. -/
theorem binomialAverage_count (T : ℕ) (eta : ℝ) :
    binomialAverage T eta (fun r => (r : ℝ)) = mean T eta := by
  by_cases hT : T = 0
  · subst T
    simp [binomialAverage, mean]
  · have hpos : 0 < T := Nat.pos_of_ne_zero hT
    unfold binomialAverage mean
    calc
      (∑ r ∈ Finset.range (T + 1),
        Causalean.Mathlib.Probability.binomialWeight T eta r * (r : ℝ)) =
          ∑ j ∈ Finset.range T,
            (T : ℝ) * eta *
              Causalean.Mathlib.Probability.binomialWeight (T - 1) eta j := by
        rw [Finset.sum_range_succ' (f := fun r =>
          Causalean.Mathlib.Probability.binomialWeight T eta r * (r : ℝ))]
        simp only [Nat.cast_zero, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < T := Finset.mem_range.mp hj
        have hchoose : (T.choose (j + 1) : ℝ) * (j + 1 : ℕ) =
            (T : ℝ) * ((T - 1).choose j : ℝ) := by
          rw [show T = (T - 1) + 1 by omega]
          exact_mod_cast (Nat.add_one_mul_choose_eq (T - 1) j).symm
        have hsub : T - (j + 1) = (T - 1) - j := by omega
        simp only [Causalean.Mathlib.Probability.binomialWeight, hsub, pow_succ]
        push_cast
        rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by norm_num]
        calc
          (T.choose (j + 1) : ℝ) * (eta ^ j * eta) *
              (1 - eta) ^ (T - 1 - j) * ((j + 1 : ℕ) : ℝ) =
              ((T.choose (j + 1) : ℝ) * (j + 1 : ℕ)) * eta *
                (eta ^ j * (1 - eta) ^ (T - 1 - j)) := by ring
          _ = _ := by rw [hchoose]; ring
      _ = (T : ℝ) * eta *
          binomialAverage (T - 1) eta (fun _ => 1) := by
        simp only [binomialAverage, mul_one]
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega), Finset.mul_sum]
      _ = (T : ℝ) * eta := by rw [binomialAverage_one]; ring

/-- The [binomial average for a trial count](hyp:T) and
[success probability](hyp:eta) of the [unordered pair count](goal) is the
expected pair scale. -/
theorem binomialAverage_pairs (T : ℕ) (eta : ℝ) :
    binomialAverage T eta (fun r => (r.choose 2 : ℝ)) = pairScale T eta := by
  by_cases hT : T < 2
  · interval_cases T <;> norm_num [binomialAverage, pairScale,
      Causalean.Mathlib.Probability.binomialWeight, Finset.sum_range_succ]
  · have hT2 : 2 ≤ T := by omega
    unfold binomialAverage pairScale
    calc
      (∑ r ∈ Finset.range (T + 1),
        Causalean.Mathlib.Probability.binomialWeight T eta r *
          (r.choose 2 : ℝ)) =
          ∑ j ∈ Finset.range (T - 1),
            (T.choose 2 : ℝ) * eta ^ 2 *
              Causalean.Mathlib.Probability.binomialWeight (T - 2) eta j := by
        rw [Finset.sum_range_succ' (f := fun r =>
          Causalean.Mathlib.Probability.binomialWeight T eta r *
            (r.choose 2 : ℝ))]
        simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, add_zero]
        rw [show T = (T - 1) + 1 by omega,
          Finset.sum_range_succ' (f := fun j =>
            Causalean.Mathlib.Probability.binomialWeight (T - 1 + 1) eta (j + 1) *
              ((j + 1).choose 2 : ℝ))]
        simp only [Nat.sub_add_cancel (show 1 ≤ T by omega)]
        simp only [Nat.zero_add, show (1 : ℕ).choose 2 = 0 by decide,
          Nat.cast_zero, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < T - 1 := Finset.mem_range.mp hj
        have hchoose : (T.choose (j + 2) : ℝ) * ((j + 2).choose 2 : ℝ) =
            (T.choose 2 : ℝ) * ((T - 2).choose j : ℝ) := by
          have h := Nat.choose_mul (n := T) (k := j + 2) (s := 2) (by omega)
          have h' : T.choose (j + 2) * (j + 2).choose 2 =
              T.choose 2 * (T - 2).choose j := by
            simpa [show j + 2 - 2 = j by omega] using h
          exact_mod_cast h'
        have hsub : T - (j + 2) = (T - 2) - j := by omega
        simp only [Causalean.Mathlib.Probability.binomialWeight, hsub,
          show j + 1 + 1 = j + 2 by omega, pow_add]
        calc
          (T.choose (j + 2) : ℝ) * (eta ^ j * eta ^ 2) *
              (1 - eta) ^ (T - 2 - j) * ((j + 2).choose 2 : ℝ) =
              ((T.choose (j + 2) : ℝ) * ((j + 2).choose 2 : ℝ)) *
                eta ^ 2 * (eta ^ j * (1 - eta) ^ (T - 2 - j)) := by ring
          _ = _ := by rw [hchoose]; ring
      _ = (T.choose 2 : ℝ) * eta ^ 2 *
          binomialAverage (T - 2) eta (fun _ => 1) := by
        simp only [binomialAverage, mul_one]
        rw [show T - 1 = (T - 2) + 1 by omega, Finset.mul_sum]
      _ = (T.choose 2 : ℝ) * eta ^ 2 := by rw [binomialAverage_one]; ring

end Causalean.Mathlib.Probability.Birthday

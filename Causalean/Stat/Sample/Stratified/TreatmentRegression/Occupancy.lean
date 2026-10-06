module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.OccupancyScalar

/-! # Uniform repeat-count expectation

Under an arbitrary categorical iid law, the expected repeat count is n minus
the expected number of occupied cells. Convexity of the empty-cell probability
shows that the uniform law minimizes repetitions among laws with at most n
available cells. For n at least two this gives n/4; at n=1 repetitions are
identically zero. Null cells are included throughout.
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set
open scoped BigOperators

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

omit [Fintype κ] in
/-- In [an iid sample of size n from a probability law Q on cells](hyp:n,Q),
[the probability that a cell k is empty](hyp:k) [equals (1 − q)ⁿ, where q is the mass Q gives to
k](goal). -/
lemma probability_empty_cell (n : ℕ) (Q : Measure κ) [IsProbabilityMeasure Q] (k : κ) :
    ((Measure.pi (fun _ : Fin n => Q)) {x | cellCount x k = 0}).toReal =
      (1 - (Q {k}).toReal) ^ n := by
  classical
  have hevent : {x : Fin n → κ | cellCount x k = 0} =
      Set.univ.pi (fun _ : Fin n => ({k} : Set κ)ᶜ) := by
    ext x
    simp [cellCount, Set.mem_pi]
  rw [hevent, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  have hc := probReal_add_probReal_compl (μ := Q) (measurableSet_singleton k)
  have hreal : (Q ({k}ᶜ)).toReal = 1 - (Q {k}).toReal := by
    change (Q.real {k}ᶜ) = 1 - Q.real {k}
    linarith
  rw [hreal]

/-- In [an iid sample of size n from any probability law Q on cells](hyp:n,Q), [the expected
repeat count equals n minus the sum over cells of the occupancy probabilities 1 − (1 − q)ⁿ, where
q is the cell's mass](goal); zero-mass cells are included. -/
theorem integral_repeatCount (n : ℕ) (Q : Measure κ) [IsProbabilityMeasure Q] :
    (∫ x : Fin n → κ, (repeatCount x : ℝ) ∂Measure.pi (fun _ : Fin n => Q)) =
      (n : ℝ) - ∑ k, (1 - (1 - (Q {k}).toReal) ^ n) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => Q)
  have hidentity (x : Fin n → κ) : (repeatCount x : ℝ) =
      (n : ℝ) - ∑ k, (1 - if cellCount x k = 0 then (1 : ℝ) else 0) := by
    have hcell (k : κ) : ((cellCount x k - 1 : ℕ) : ℝ) =
        (cellCount x k : ℝ) - (1 - if cellCount x k = 0 then (1 : ℝ) else 0) := by
      by_cases h : cellCount x k = 0
      · simp [h]
      · simp only [h, if_false, sub_zero]
        rw [Nat.cast_sub (by omega : 1 ≤ cellCount x k), Nat.cast_one]
    simp only [repeatCount, Nat.cast_sum, hcell, Finset.sum_sub_distrib]
    rw [← Nat.cast_sum, sum_cellCount]
  have hempty (k : κ) :
      (∫ x : Fin n → κ, (if cellCount x k = 0 then (1 : ℝ) else 0) ∂μ) =
        (1 - (Q {k}).toReal) ^ n := by
    have hm : MeasurableSet {x : Fin n → κ | cellCount x k = 0} :=
      Set.to_countable _ |>.measurableSet
    have hf : (fun x : Fin n → κ => if cellCount x k = 0 then (1 : ℝ) else 0) =
        {x : Fin n → κ | cellCount x k = 0}.indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp [Set.indicator]
    rw [hf, integral_indicator_const 1 hm]
    simpa [μ, Measure.real] using probability_empty_cell n Q k
  simp_rw [hidentity]
  rw [integral_sub (integrable_const _) Integrable.of_finite,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_sub (integrable_const _) Integrable.of_finite, hempty]
  simp

/-- In [an iid sample of size n from any probability law Q on cells](hyp:n,Q), if [there are at
least two observations](hyp:hn) and [the number of cells is at most n](hyp:hcard), then
[the expected repeat count is at least n/4](goal).

When at most n cells are available and n is at least two, the expected
repeat count is at least n/4, uniformly over arbitrary categorical masses. -/
theorem integral_repeatCount_lower (n : ℕ) (Q : Measure κ) [IsProbabilityMeasure Q]
    (hn : 2 ≤ n) (hcard : Fintype.card κ ≤ n) :
    (n : ℝ) / 4 ≤ ∫ x : Fin n → κ, (repeatCount x : ℝ)
      ∂Measure.pi (fun _ : Fin n => Q) := by
  rw [integral_repeatCount]
  apply occupancy_polynomial_lower n (fun k => (Q {k}).toReal) hn hcard
  · intro k
    exact ENNReal.toReal_nonneg
  · have hsum : ∑ k, Q {k} = 1 := by
      simp
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top Q {k}), hsum]
    simp

end Causalean.Stat.Sample.Stratified.TreatmentRegression

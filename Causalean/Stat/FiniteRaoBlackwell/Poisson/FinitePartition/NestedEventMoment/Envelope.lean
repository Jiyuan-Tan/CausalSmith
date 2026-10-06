module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.Basic

/-!
# Measurability and scalar bound for nested-event counts

These lemmas provide the pointwise and measurable envelope needed to integrate
weighted factorial counts under a finite Poisson sample law.
-/

public section

open MeasureTheory

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

variable {X : Type*} [MeasurableSpace X]

/-- An [event](hyp:A) with [measurable membership](hyp:hA) has a [measurable
finite-sample event count](goal). -/
theorem measurable_eventCount (A : Set X) (hA : MeasurableSet A) :
    Measurable (fun s : FiniteSample X => eventCount s A) := by
  classical
  apply measurable_to_countable'
  intro k
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {x : Fin n → X | eventCount (fixedSizeEmbed n x) A = k}
  have hcount : Measurable (fun x : Fin n → X =>
      ∑ i : Fin n, if x i ∈ A then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite ((measurable_pi_apply i) hA)
      measurable_const measurable_const
  have heq : (fun x : Fin n → X => eventCount (fixedSizeEmbed n x) A) =
      (fun x => ∑ i : Fin n, if x i ∈ A then (1 : ℕ) else 0) := by
    funext x
    simp [eventCount, FiniteSample.points, fixedSizeEmbed]
    rfl
  change MeasurableSet ((fun x : Fin n → X => eventCount (fixedSizeEmbed n x) A) ⁻¹' {k})
  rw [heq]
  exact hcount (measurableSet_singleton k)

/-- Two [events](hyp:A,B) with [measurable membership](hyp:hA,hB) and an [order](hyp:v)
give a [measurable weighted nested-event factorial count](goal). -/
theorem measurable_weightedFactorial (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (v : ℕ) :
    Measurable (weightedFactorial A B v) := by
  unfold weightedFactorial
  have hA' : Measurable (fun s : FiniteSample X => (eventCount s A : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_eventCount A hA)
  have hB' : Measurable (fun s : FiniteSample X =>
      (eventCount s B - 1).descFactorial (v - 1)) :=
    (measurable_of_countable (fun n : ℕ => n.descFactorial (v - 1))).comp
      ((measurable_eventCount B hB).sub
        (measurable_const : Measurable (fun _ : FiniteSample X => (1 : ℕ))))
  exact hA'.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hB')

/-- Two [events](hyp:A,B) with [the first contained in the second](hyp:hAB), an
[order](hyp:v) with [positive order](hyp:hv), and a [finite sample](hyp:s) have a
[nonnegative weighted factorial count bounded by the sample-size falling factorial](goal). -/
theorem weightedFactorial_nonneg_le_countFactorial (A B : Set X)
    (hAB : A ⊆ B) (v : ℕ) (hv : 1 ≤ v) (s : FiniteSample X) :
    0 ≤ weightedFactorial A B v s ∧
      weightedFactorial A B v s ≤ (s.count.descFactorial v : ℝ) := by
  classical
  rcases s with ⟨n, x⟩
  change 0 ≤ weightedFactorial A B v (fixedSizeEmbed n x) ∧
    weightedFactorial A B v (fixedSizeEmbed n x) ≤ (n.descFactorial v : ℝ)
  rw [weightedFactorial_eq_injectiveTupleSum A B hAB v n hv x]
  have hkernel (t : Fin v → Fin n) :
      0 ≤ nestedEventKernel A B v hv (fun j => x (t j)) ∧
        nestedEventKernel A B v hv (fun j => x (t j)) ≤ 1 := by
    unfold nestedEventKernel
    split_ifs <;> norm_num
  constructor
  · exact Finset.sum_nonneg fun t ht => hkernel t |>.1
  · calc
      (∑ t ∈ injectiveTuples v n,
        nestedEventKernel A B v hv (fun j => x (t j))) ≤
          ∑ _t ∈ injectiveTuples v n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            exact (hkernel t).2
      _ = (n.descFactorial v : ℝ) := by
        simp [injectiveTuples_card_eq_descFactorial]

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

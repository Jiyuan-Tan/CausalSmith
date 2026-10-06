module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Total success fractions in finite samples

Real event counts are sums of zero-one indicators. The success fraction is zero
when the containing-event count is zero. This module supplies pointwise bounds,
measurability, and integrability without any positivity assumption on event mass.
-/

@[expose] public section

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

noncomputable section

/-- An [event](hyp:A) and [a fixed observation tuple](hyp:x) determine its [real-valued
count](goal), given by summing the membership indicators (step:1). -/
def iidEventCount (A : Set X) {n : ℕ} (x : Fin n → X) : ℝ := by
  classical
  exact ∑ i : Fin n, if x i ∈ A then (1 : ℝ) else 0

/-- An [event](hyp:A) and [a finite sample](hyp:s) determine its [real-valued event
count](goal), given by the count in the sample's observation tuple (step:1). -/
def eventCount (A : Set X) (s : FiniteSample X) : ℝ :=
  iidEventCount A s.points

/-- Two [events](hyp:A,B) and [a finite sample](hyp:s) determine the [total success
fraction](goal), given by the smaller-event count divided by the containing-event count
when that count is nonzero and by zero otherwise (step:1). -/
def successFraction (A B : Set X) (s : FiniteSample X) : ℝ := by
  classical
  exact if eventCount B s = 0 then 0 else eventCount A s / eventCount B s

/-- An [event](hyp:A) and [a finite sample](hyp:s) have an [event count between zero and
the sample size](goal). -/
theorem eventCount_bounds (A : Set X) (s : FiniteSample X) :
    0 ≤ eventCount A s ∧ eventCount A s ≤ (s.count : ℝ) := by
  classical
  unfold eventCount iidEventCount
  constructor
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  · calc
      (∑ i : Fin s.count, if s.points i ∈ A then (1 : ℝ) else 0) ≤
          ∑ _i : Fin s.count, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = (s.count : ℝ) := by simp

/-- [Containment of one event in another](hyp:hAB) and [a finite sample](hyp:s) imply that
[the smaller-event count is no larger than the containing-event count](goal). -/
theorem eventCount_mono {A B : Set X} (hAB : A ⊆ B) (s : FiniteSample X) :
    eventCount A s ≤ eventCount B s := by
  classical
  unfold eventCount iidEventCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases hA : s.points i ∈ A
  · simp [hA, hAB hA]
  · simp only [hA, ite_false]
    split_ifs <;> norm_num

/-- [Containment of one event in another](hyp:hAB) and [a finite sample](hyp:s) imply that
[the total success fraction lies between zero and one](goal). -/
theorem successFraction_bounds {A B : Set X} (hAB : A ⊆ B) (s : FiniteSample X) :
    0 ≤ successFraction A B s ∧ successFraction A B s ≤ 1 := by
  classical
  unfold successFraction
  split_ifs with hB
  · exact ⟨le_rfl, zero_le_one⟩
  · have hBpos : 0 < eventCount B s :=
      lt_of_le_of_ne (eventCount_bounds B s).1 (Ne.symm hB)
    exact ⟨div_nonneg (eventCount_bounds A s).1 hBpos.le,
      (div_le_one hBpos).2 (eventCount_mono hAB s)⟩

/-- [Measurable membership of an event](hyp:hA) and [a tuple size](hyp:n) make [the
real-valued event count on tuples measurable](goal). -/
@[fun_prop]
theorem measurable_iidEventCount {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    Measurable (iidEventCount A : (Fin n → X) → ℝ) := by
  -- Write each summand as a measurable indicator of a coordinate preimage.
  classical
  unfold iidEventCount
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (hA.preimage (measurable_pi_apply i))
    measurable_const measurable_const

/-- [Measurable membership of an event](hyp:hA) makes [the real-valued event count on
finite samples measurable](goal). -/
@[fun_prop]
theorem measurable_eventCount {A : Set X} (hA : MeasurableSet A) :
    Measurable (eventCount A : FiniteSample X → ℝ) := by
  -- Use the measurable sigma-space criterion and measurable_iidEventCount.
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact measurable_iidEventCount hA n ht

/-- [Measurable membership of the two events](hyp:hA,hB) makes [their total success
fraction measurable](goal). -/
@[fun_prop]
theorem measurable_successFraction {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (successFraction A B : FiniteSample X → ℝ) := by
  -- The zero-count branch is a measurable piecewise real quotient.
  classical
  unfold successFraction
  exact Measurable.ite
    ((measurable_eventCount hB) (measurableSet_singleton 0))
    measurable_const ((measurable_eventCount hA).div (measurable_eventCount hB))

/-- Under [a finite measure on finite samples](hyp:μ), [measurable membership of two
events](hyp:hA,hB), and [their containment relation](hyp:hAB), [the total success fraction
is integrable](goal). -/
theorem integrable_successFraction (μ : Measure (FiniteSample X)) [IsFiniteMeasure μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    Integrable (successFraction A B) μ := by
  exact Integrable.of_mem_Icc 0 1
    (measurable_successFraction hA hB).aemeasurable
    (Filter.Eventually.of_forall fun s => successFraction_bounds hAB s)

/-- An [event](hyp:A), [a tuple size](hyp:n), and [a fixed observation tuple](hyp:x) have
[the same real-valued event count before and after finite-sample embedding](goal). -/
@[simp]
theorem eventCount_fixedSizeEmbed (A : Set X) (n : ℕ) (x : Fin n → X) :
    eventCount A (fixedSizeEmbed n x) = iidEventCount A x := by
  rfl

end

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

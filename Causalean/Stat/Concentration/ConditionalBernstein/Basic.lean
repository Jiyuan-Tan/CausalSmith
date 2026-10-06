module
public import Causalean.Stat.Minimax.MarkovKernelTransport
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite design-cell and outcome-bin histogram statistics

The design partition is represented by a key map with measurable fibres. Outcome bins
are an arbitrary finite measurable family: disjointness is unnecessary for concentration.
Counts are natural numbers; conditional means and deviations are real numbers. All
statistics include the empty sample and empty cells, with no division by cell counts.
-/

@[expose] public section

noncomputable section
namespace Causalean.Stat.Concentration.ConditionalBernstein

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {D Y C : Type*} {n : ℕ}

/-- The [indicator](goal) of the [cell selected by a key map](hyp:key,c) at a
[design point](hyp:d) takes real values zero and one. -/
def cellIndicator (key : D → C) (c : C) (d : D) : ℝ := by
  classical
  exact if key d = c then 1 else 0

/-- The [real bin indicator](goal) for an [outcome set](hyp:bin) at an
[outcome](hyp:y) takes values zero and one. -/
def binIndicator (bin : Set Y) (y : Y) : ℝ :=
  bin.indicator (fun _ => 1) y

/-- The [cell count](goal) counts coordinates of a [design vector](hyp:x) in the
[cell specified by the key](hyp:key,c). -/
def cellCount (key : D → C) (c : C) (x : Fin n → D) : ℕ := by
  classical
  exact ∑ i, if key (x i) = c then 1 else 0

/-- The [joint count](goal) counts coordinates in the [design cell](hyp:key,c)
whose [outcome vector](hyp:y) lies in the [bin](hyp:bin), for the [design vector](hyp:x). -/
def jointCount (key : D → C) (bin : Set Y) (c : C)
    (x : Fin n → D) (y : Fin n → Y) : ℕ := by
  classical
  exact ∑ i, if key (x i) = c ∧ y i ∈ bin then 1 else 0

variable [MeasurableSpace D] [MeasurableSpace Y]

/-- The [bin probability](goal) is the real probability of an [outcome bin](hyp:bin)
under the [conditional outcome kernel](hyp:K) at a [design point](hyp:d). -/
def binProbability (K : Kernel D Y) (bin : Set Y) (d : D) : ℝ :=
  (K d).real bin

/-- The [conditional joint-count mean](goal) sums the [kernel bin probabilities](hyp:K,bin)
over coordinates of the [design vector](hyp:x) in the [chosen cell](hyp:key,c). -/
def conditionalMean (key : D → C) (K : Kernel D Y) (bin : Set Y)
    (c : C) (x : Fin n → D) : ℝ :=
  ∑ i, cellIndicator key c (x i) * binProbability K bin (x i)

/-- A [centered count summand](goal) for the [coordinate](hyp:i) of the [design and outcome
vectors](hyp:x,y) subtracts its [conditional bin mean](hyp:K,bin), retaining only the
[selected design cell](hyp:key,c). -/
def centeredSummand (key : D → C) (K : Kernel D Y) (bin : Set Y)
    (c : C) (x : Fin n → D) (i : Fin n) (y : Fin n → Y) : ℝ :=
  cellIndicator key c (x i) * (binIndicator bin (y i) - binProbability K bin (x i))

/-- A [measurable cell fibre](hyp:hcell) has a [measurable real indicator](goal). -/
@[fun_prop] theorem measurable_cellIndicator {key : D → C} {c : C}
    (hcell : MeasurableSet {d | key d = c}) : Measurable (cellIndicator key c) := by
  classical
  exact measurable_const.ite hcell measurable_const

/-- A [measurable outcome bin](hyp:hbin) has a [measurable real indicator](goal). -/
@[fun_prop] theorem measurable_binIndicator {bin : Set Y} (hbin : MeasurableSet bin) :
    Measurable (binIndicator bin) :=
  measurable_const.indicator hbin

/-- A [measurable bin](hyp:hbin) has a [measurable conditional probability](goal) under
the [outcome kernel](hyp:K). -/
@[fun_prop] theorem measurable_binProbability (K : Kernel D Y)
    {bin : Set Y} (hbin : MeasurableSet bin) : Measurable (binProbability K bin) := by
  exact (K.measurable_coe hbin).ennreal_toReal

omit [MeasurableSpace D] in
/-- Casting the [cell count](hyp:key,c,x) to the reals gives
[the sum of real cell indicators](goal). -/
theorem cellCount_cast (key : D → C) (c : C) (x : Fin n → D) :
    (cellCount key c x : ℝ) = ∑ i, cellIndicator key c (x i) := by
  classical
  simp [cellCount, cellIndicator]

omit [MeasurableSpace D] [MeasurableSpace Y] in
/-- Casting the [joint count](hyp:key,bin,c,x,y) to the reals gives
[the sum of products of its cell and bin indicators](goal). -/
theorem jointCount_cast (key : D → C) (bin : Set Y) (c : C)
    (x : Fin n → D) (y : Fin n → Y) :
    (jointCount key bin c x y : ℝ) =
      ∑ i, cellIndicator key c (x i) * binIndicator bin (y i) := by
  classical
  simp only [jointCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : key (x i) = c <;> by_cases hy : y i ∈ bin <;>
    simp [cellIndicator, binIndicator, hc, hy]

/-- A [measurable cell fibre](hyp:hcell) gives a [measurable real cell count](goal). -/
@[fun_prop] theorem measurable_cellCount_real {key : D → C} {c : C}
    (hcell : MeasurableSet {d | key d = c}) :
    Measurable (fun x : Fin n → D => (cellCount key c x : ℝ)) := by
  simp_rw [cellCount_cast]
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_cellIndicator hcell).comp (measurable_pi_apply i))

/-- A [measurable cell fibre and bin](hyp:hcell,hbin) give
[a jointly measurable real joint count](goal). -/
@[fun_prop] theorem measurable_jointCount_real {key : D → C} {c : C} {bin : Set Y}
    (hcell : MeasurableSet {d | key d = c}) (hbin : MeasurableSet bin) :
    Measurable (fun p : (Fin n → D) × (Fin n → Y) =>
      (jointCount key bin c p.1 p.2 : ℝ)) := by
  simp_rw [jointCount_cast]
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_cellIndicator hcell).comp
      ((measurable_pi_apply i).comp measurable_fst)).mul
    ((measurable_binIndicator hbin).comp
      ((measurable_pi_apply i).comp measurable_snd)))

/-- A [measurable cell fibre and bin](hyp:hcell,hbin) under an [outcome kernel](hyp:K)
give [a measurable conditional count mean](goal). -/
@[fun_prop] theorem measurable_conditionalMean (K : Kernel D Y)
    {key : D → C} {c : C} {bin : Set Y}
    (hcell : MeasurableSet {d | key d = c}) (hbin : MeasurableSet bin) :
    Measurable (conditionalMean (n := n) key K bin c) := by
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_cellIndicator hcell).comp (measurable_pi_apply i)).mul
    ((measurable_binProbability K hbin).comp (measurable_pi_apply i)))

/-- The [joint-count deviation](hyp:key,K,bin,c,x,y) is
[the sum of its centered coordinate summands](goal). -/
theorem jointCount_sub_conditionalMean (key : D → C) (K : Kernel D Y)
    (bin : Set Y) (c : C) (x : Fin n → D) (y : Fin n → Y) :
    (jointCount key bin c x y : ℝ) - conditionalMean key K bin c x =
      ∑ i, centeredSummand key K bin c x i y := by
  classical
  simp only [jointCount, Nat.cast_sum, conditionalMean, centeredSummand,
    mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : key (x i) = c <;> by_cases hy : y i ∈ bin <;>
    simp [cellIndicator, binIndicator, hc, hy]

end Causalean.Stat.Concentration.ConditionalBernstein

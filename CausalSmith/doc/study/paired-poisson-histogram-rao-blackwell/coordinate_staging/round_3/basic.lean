/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite histogram fibres and paired conditional averages

This module turns an estimator of paired fixed samples into an estimator of two
count histograms. The construction averages the two histogram fibres independently,
then pairs the retained prefixes coordinatewise.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Given [a finite ordered sample](hyp:x) and [an alphabet symbol](hyp:a), its
[finite-sample histogram count](goal) is the number of sample positions equal to that symbol. -/
def finiteSampleHistogram {m : ℕ} {X : Type*} [DecidableEq X]
    (x : Fin m → X) (a : X) : ℕ :=
  Fintype.card {i : Fin m // x i = a}

/-- Given [a finite count histogram](hyp:c), its [histogram total](goal) is the sum of
the counts over the alphabet. -/
def histogramTotal {X : Type*} [Fintype X] (c : X → ℕ) : ℕ :=
  ∑ a, c a

/-- The [histogram of a finite ordered sample](hyp:x) [has total equal to the sample
size](goal). -/
theorem histogramTotal_finiteSampleHistogram
    {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (x : Fin m → X) :
    histogramTotal (finiteSampleHistogram x) = m := by
  classical
  unfold histogramTotal finiteSampleHistogram
  simp_rw [Fintype.card_subtype]
  rw [← Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := x) (by simp)]
  simp

/-- Given [a finite count histogram](hyp:c), its [histogram fibre](goal) is the set of
ordered arrays whose length is the histogram total and whose histogram equals the given one. -/
def HistogramFiber {X : Type*} [Fintype X] [DecidableEq X]
    (c : X → ℕ) :=
  {x : Fin (histogramTotal c) → X // finiteSampleHistogram x = c}

/-- Given [a finite count histogram](hyp:c), its [histogram fibre has a finite
enumeration](goal). -/
noncomputable instance histogramFiberFintype
    {X : Type*} [Fintype X] [DecidableEq X] (c : X → ℕ) :
    Fintype (HistogramFiber c) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every [finite count histogram](hyp:c) [has at least one compatible ordering](goal). -/
theorem histogramFiber_nonempty
    {X : Type*} [Fintype X] [DecidableEq X] (c : X → ℕ) :
    Nonempty (HistogramFiber c) := by
  classical
  let S := Σ a : X, Fin (c a)
  have hcard : Fintype.card S = histogramTotal c := by
    simp [S, histogramTotal]
  let e : Fin (histogramTotal c) ≃ S :=
    (Fintype.equivFinOfCardEq hcard).symm
  let x : Fin (histogramTotal c) → X := fun i => (e i).1
  refine ⟨⟨x, ?_⟩⟩
  funext a
  unfold finiteSampleHistogram
  change Fintype.card {i : Fin (histogramTotal c) // (e i).1 = a} = c a
  calc
    _ = Fintype.card {s : S // s.1 = a} :=
      Fintype.card_congr (Equiv.subtypeEquivOfSubtype e)
    _ = Fintype.card (Σ b : {b : X // b = a}, Fin (c b.1)) :=
      Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun b : X => Fin (c b)) (fun b => b = a))
    _ = c a := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      simpa using Fintype.sum_subsingleton (fun b : {b : X // b = a} => c b.1) ⟨a, rfl⟩

/-- Given [a certificate that the requested length does not exceed the histogram
total](hyp:h) and [a compatible ordering](hyp:x), the [retained histogram prefix](goal)
consists of the ordering's first requested entries. -/
def retainedHistogramPrefix
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    {c : X → ℕ} (h : n ≤ histogramTotal c)
    (x : HistogramFiber c) : Fin n → X :=
  fun i => x.1 (Fin.castLE h i)

/-- Given [one retained array](hyp:x) and [another retained array](hyp:y), their
[coordinatewise pairing](goal) places the entries with each common index into a pair. -/
def pairRetainedArrays {n : ℕ} {X Y : Type*}
    (x : Fin n → X) (y : Fin n → Y) : Fin n → X × Y :=
  fun i => (x i, y i)

/-- Given [a paired-sample estimator](hyp:est), [two finite count histograms](hyp:cX,cY),
and [certificates that both totals contain the requested sample length](hyp:hX,hY), the
[paired conditional histogram average](goal) independently averages the estimator over
all compatible orderings, after retaining and coordinatewise pairing the two prefixes. -/
noncomputable def pairedHistogramAverage
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (cX : X → ℕ) (cY : Y → ℕ)
    (hX : n ≤ histogramTotal cX) (hY : n ≤ histogramTotal cY) : ℝ := by
  classical
  exact
    (∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
      est (pairRetainedArrays (retainedHistogramPrefix hX x)
        (retainedHistogramPrefix hY y))) /
      (Fintype.card (HistogramFiber cX) * Fintype.card (HistogramFiber cY))

/-- Given [a paired-sample estimator](hyp:est), [a fallback value](hyp:fallback), and
[two finite count histograms](hyp:c), the [paired Poisson-histogram estimator](goal)
[uses the independent compatible-ordering average when both totals are large enough and returns
the fallback when either total is too small](step:1). -/
noncomputable def pairedPoissonHistogramEstimator
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (fallback : ℝ)
    (c : (X → ℕ) × (Y → ℕ)) : ℝ :=
  if hX : n ≤ histogramTotal c.1 then
    if hY : n ≤ histogramTotal c.2 then
      pairedHistogramAverage est c.1 c.2 hX hY
    else fallback
  else fallback

/-- Given [a paired-sample estimator](hyp:est), [a fallback value](hyp:fallback),
[two finite count histograms](hyp:cX,cY), and [certificates that both totals contain the
requested sample length](hyp:hX,hY), [the paired count estimator equals the independent
compatible-ordering average](goal). -/
theorem pairedPoissonHistogramEstimator_of_totals_ge
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (fallback : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ)
    (hX : n ≤ histogramTotal cX) (hY : n ≤ histogramTotal cY) :
    pairedPoissonHistogramEstimator est fallback (cX, cY) =
      pairedHistogramAverage est cX cY hX hY := by
  simp only [pairedPoissonHistogramEstimator, hX, hY, dite_true]

/-- Given [a paired-sample estimator](hyp:est), [a fallback value](hyp:fallback),
[two finite count histograms](hyp:cX,cY), and [a certificate that at least one total is
too small](hyp:hfail), [the paired count estimator equals its fallback](goal). -/
theorem pairedPoissonHistogramEstimator_of_total_lt
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (fallback : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ)
    (hfail : histogramTotal cX < n ∨ histogramTotal cY < n) :
    pairedPoissonHistogramEstimator est fallback (cX, cY) = fallback := by
  rcases hfail with hX | hY
  · simp [pairedPoissonHistogramEstimator, Nat.not_le_of_lt hX]
  · by_cases hX : n ≤ histogramTotal cX
    · simp [pairedPoissonHistogramEstimator, hX, Nat.not_le_of_lt hY]
    · simp [pairedPoissonHistogramEstimator, hX]

/-- Given [a paired-sample estimator](hyp:est) and [a fallback value](hyp:fallback),
[the resulting paired count estimator is measurable](goal) on finite measurable alphabets
with measurable singletons. -/
@[fun_prop]
theorem measurable_pairedPoissonHistogramEstimator
    {n : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (fallback : ℝ) :
    Measurable (pairedPoissonHistogramEstimator est fallback) := by
  exact measurable_of_countable _

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

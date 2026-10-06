/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.DeletionLogSobolev
public import Causalean.Stat.Concentration.EntropyMethod.FiniteMaximizer
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Finite empirical suprema and deletion coordinates

This file constructs the finite-class empirical supremum used in Bousquet's inequality in the
same head--tail recursion as `DeletionCoordinateFamily`.  An offset records the contributions of
coordinates already fixed by the recursion.  This makes every deletion comparison independent
of the coordinate being deleted while retaining the ordinary maximum-of-sums statistic.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Concentration.EntropyMethod

universe u v

open Causalean.Mathlib.MeasureTheory

/-- Given [a score class `g`](hyp:g), [a coordinate count `n`](hyp:n), [initial offsets
`offset`](hyp:offset), [an index `i`](hyp:i), and [a sample `s`](hyp:s), the [recursive empirical
score](goal) adds the `n` coordinate scores to the corresponding initial offset. -/
noncomputable def finiteEmpiricalScore {X : Type u} {I : Type v}
    (g : I → X → ℝ) (n : ℕ) (offset : I → ℝ) (i : I) (s : Fin n → X) : ℝ :=
  offset i + ∑ j, g i (s j)

/-- Given [a nonempty finite index type `I`](hyp:I), [a score class `g`](hyp:g), [a coordinate
count `n`](hyp:n), [initial offsets `offset`](hyp:offset), and [a sample `s`](hyp:s), the [finite
empirical supremum](goal) is the largest recursive empirical score in the class, with ties broken
by `finiteClassMaximizer`. -/
noncomputable def finiteEmpiricalSupremum {X : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (s : Fin n → X) : ℝ :=
  finiteEmpiricalScore g n offset
    (finiteClassMaximizer I (finiteEmpiricalScore g n offset) s) s

/-- Given [a nonempty finite index type `I`](hyp:I), [a score class `g`](hyp:g), [a coordinate
count `n`](hyp:n), [initial offsets `offset`](hyp:offset), and [a sample `s`](hyp:s), the [selected
finite empirical maximizer](goal) is the measurably tie-broken index attaining the supremum. -/
noncomputable def finiteEmpiricalMaximizer {X : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (s : Fin n → X) : I :=
  finiteClassMaximizer I (finiteEmpiricalScore g n offset) s

/-- Given [a nonempty finite index type `I`](hyp:I), [a score class `g`](hyp:g), [a coordinate
count `n`](hyp:n), and initial offsets `offset`, the [recursive leave-one-out
family](goal) uses the supremum with the head coordinate omitted and then adds the fixed head
score to the offset before recursing through the tail. -/
noncomputable def finiteEmpiricalDeletionFamily {X : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (g : I → X → ℝ) :
    (n : ℕ) → (I → ℝ) → DeletionCoordinateFamily X n
  | 0, _ => .nil
  | n + 1, offset => .cons
      (finiteEmpiricalSupremum I g n offset)
      (fun x => finiteEmpiricalDeletionFamily I g n (fun i => offset i + g i x))

/-- [The finite empirical supremum](goal) equals the score of [its selected maximizer](hyp:I,g,n,offset,s). -/
theorem finiteEmpiricalSupremum_eq_score {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (s : Fin n → X) :
    finiteEmpiricalSupremum I g n offset s =
      finiteEmpiricalScore g n offset (finiteEmpiricalMaximizer I g n offset s) s := by
  rfl

/-- For [a nonempty finite class](hyp:I), [every empirical score](hyp:g,n,offset,s,i) is at most
the [finite empirical supremum](goal). -/
theorem finiteEmpiricalScore_le_supremum {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (s : Fin n → X) (i : I) :
    finiteEmpiricalScore g n offset i s ≤ finiteEmpiricalSupremum I g n offset s := by
  simpa [finiteEmpiricalSupremum] using
    finiteClassMaximizer_spec (finiteEmpiricalScore g n offset) s i

/-- Adding [an index-dependent constant `c`](hyp:c) to [every initial offset](hyp:offset) adds
that same constant to [each recursive empirical score](goal) for [the score class `g`](hyp:g),
[coordinate count `n`](hyp:n), [index `i`](hyp:i), and [sample `s`](hyp:s). -/
theorem finiteEmpiricalScore_add_offset {X : Type u} {I : Type v}
    (g : I → X → ℝ) (n : ℕ) (offset c : I → ℝ) (i : I) (s : Fin n → X) :
    finiteEmpiricalScore g n (fun j => offset j + c j) i s =
      finiteEmpiricalScore g n offset i s + c i := by
  simp [finiteEmpiricalScore]
  ring

/-- If [every initial offset has absolute value at most `A`](hyp:hoffset) and [every coordinate
score has absolute value at most `B`](hyp:hbound), then [each recursive empirical score](goal)
for [the class `g`](hyp:g), [coordinate count `n`](hyp:n), [index `i`](hyp:i), and [sample
`s`](hyp:s) has absolute value at most `A + n B`. -/
theorem abs_finiteEmpiricalScore_le {X : Type u} {I : Type v}
    (g : I → X → ℝ) {A B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (offset : I → ℝ)
    (hoffset : ∀ i, |offset i| ≤ A) (i : I) (s : Fin n → X) :
    |finiteEmpiricalScore g n offset i s| ≤ A + (n : ℝ) * B := by
  have hsum : |∑ j, g i (s j)| ≤ (n : ℝ) * B := by
    calc
      |∑ j, g i (s j)| ≤ ∑ j, |g i (s j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hbound i (s j)
      _ = (n : ℝ) * B := by simp
  rw [finiteEmpiricalScore]
  exact (abs_add_le _ _).trans (add_le_add (hoffset i) hsum)

/-- If [every initial offset has absolute value at most `A`](hyp:hoffset) and [every coordinate
score has absolute value at most `B`](hyp:hbound),
then [the finite empirical supremum](goal) for [a nonempty finite class](hyp:I), [the score class
`g`](hyp:g), [coordinate count `n`](hyp:n), and [sample `s`](hyp:s) has absolute value at most
`A + n B`. -/
theorem abs_finiteEmpiricalSupremum_le {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ) {A B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (offset : I → ℝ)
    (hoffset : ∀ i, |offset i| ≤ A) (s : Fin n → X) :
    |finiteEmpiricalSupremum I g n offset s| ≤ A + (n : ℝ) * B := by
  rw [finiteEmpiricalSupremum_eq_score]
  exact abs_finiteEmpiricalScore_le g hbound n offset hoffset _ s

/-- Splitting [a positive-length sample `s`](hyp:s) into its head and tail rewrites [the recursive
empirical score](goal) for [the class `g`](hyp:g), [offsets `offset`](hyp:offset), and [index
`i`](hyp:i) as the tail score with the head contribution added to the offset. -/
theorem finiteEmpiricalScore_succ {X : Type u} {I : Type v} [MeasurableSpace X]
    (g : I → X → ℝ) (n : ℕ) (offset : I → ℝ) (i : I) (s : Fin (n + 1) → X) :
    finiteEmpiricalScore g (n + 1) offset i s =
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      finiteEmpiricalScore g n (fun j => offset j + g j (e s).1) i (e s).2 := by
  simp only [finiteEmpiricalScore]
  rw [Fin.sum_univ_succAbove (fun j => g i (s j)) 0]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]
  ring

/-- Splitting [a positive-length sample `s`](hyp:s) into its head and tail rewrites [the finite
empirical supremum](goal) for [the class `g`](hyp:g) and [offsets `offset`](hyp:offset) as the tail
supremum after adding the head score to the offset. -/
theorem finiteEmpiricalSupremum_succ {X : Type u} {I : Type v}
    [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (n : ℕ) (offset : I → ℝ) (s : Fin (n + 1) → X) :
    finiteEmpiricalSupremum I g (n + 1) offset s =
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      finiteEmpiricalSupremum I g n (fun j => offset j + g j (e s).1) (e s).2 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  let leftScore := finiteEmpiricalScore g (n + 1) offset
  let rightScore := finiteEmpiricalScore g n (fun j => offset j + g j (e s).1)
  have hscores : ∀ i, leftScore i s = rightScore i (e s).2 := by
    intro i
    exact finiteEmpiricalScore_succ g n offset i s
  apply le_antisymm
  · rw [finiteEmpiricalSupremum_eq_score]
    change leftScore (finiteEmpiricalMaximizer I g (n + 1) offset s) s ≤ _
    rw [hscores]
    exact finiteEmpiricalScore_le_supremum g n
      (fun j => offset j + g j (e s).1) (e s).2 _
  · rw [finiteEmpiricalSupremum_eq_score]
    let i := finiteEmpiricalMaximizer I g n
      (fun j => offset j + g j (e s).1) (e s).2
    have hle := finiteEmpiricalScore_le_supremum g (n + 1) offset s i
    change leftScore i s ≤ _ at hle
    rw [hscores] at hle
    exact hle

/-- If [every class member is measurable](hyp:hg), then for [each coordinate count `n`](hyp:n),
[measurable offsets `offset`](hyp:offset), and [index `i`](hyp:i), [the recursive empirical score
is measurable](goal). -/
@[fun_prop]
theorem measurable_finiteEmpiricalScore {X : Type u} {I : Type v}
    [MeasurableSpace X] (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    (n : ℕ) (offset : I → ℝ) (i : I) :
    Measurable (finiteEmpiricalScore g n offset i) := by
  unfold finiteEmpiricalScore
  fun_prop

/-- If [every class member is measurable](hyp:hg), then for [each coordinate count `n`](hyp:n)
and [offset family `offset`](hyp:offset), [the finite empirical supremum is measurable](goal). -/
@[fun_prop]
theorem measurable_finiteEmpiricalSupremum {X : Type u} {I : Type v}
    [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    (n : ℕ) (offset : I → ℝ) :
    Measurable (finiteEmpiricalSupremum I g n offset) := by
  letI : MeasurableSpace I := ⊤
  let score : I → (Fin n → X) → ℝ := finiteEmpiricalScore g n offset
  have hscore : ∀ i, Measurable (score i) := fun i =>
    measurable_finiteEmpiricalScore g hg n offset i
  have hselect : Measurable (finiteClassMaximizer I score) :=
    measurable_finiteClassMaximizer hscore
  have hjoint : Measurable (fun p : I × (Fin n → X) => score p.1 p.2) :=
    measurable_from_prod_countable_right hscore
  change Measurable (fun s => finiteEmpiricalScore g n offset
    (finiteClassMaximizer I (finiteEmpiricalScore g n offset) s) s)
  simpa only [Function.comp_def, id_eq, score] using
    hjoint.comp (hselect.prodMk measurable_id)

/-- Given [a nonempty finite class](hyp:I), [scores `g`](hyp:g), [a remaining coordinate count
`n`](hyp:n), [offsets `offset`](hyp:offset), [a fixed remaining sample `rest`](hyp:rest), and
[a deleted observation `x`](hyp:x), the [head deletion increment](goal) is the new supremum after adding the head score minus the
leave-one-out supremum. -/
noncomputable def finiteEmpiricalSliceIncrement {X : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) (x : X) : ℝ :=
  finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest -
    finiteEmpiricalSupremum I g n offset rest

/-- Given [a nonempty finite class](hyp:I), [scores `g`](hyp:g), [a remaining coordinate count
`n`](hyp:n), [offsets `offset`](hyp:offset), [a fixed remaining sample `rest`](hyp:rest), and
[a deleted observation](hyp:x), the [head deletion witness](goal) evaluates that observation at the maximizer of the
leave-one-out score. -/
noncomputable def finiteEmpiricalSliceWitness {X : Type u} (I : Type v)
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) (x : X) : ℝ :=
  g (finiteEmpiricalMaximizer I g n offset rest) x

/-- Given [a nonempty finite class](hyp:I), [scores `g`](hyp:g), [a coordinate count `n`](hyp:n),
initial offsets `offset`, and a sample `s`, the [recursive sum of deletion
increments](goal) is [zero with no coordinates](step:1), while [at positive length it adds the
head deletion increment to the recursive tail sum after fixing the head coordinate](step:2). -/
noncomputable def finiteEmpiricalDeletionIncrementSum {X : Type u} (I : Type v)
    [MeasurableSpace X] [Fintype I] [Nonempty I] (g : I → X → ℝ) :
    (n : ℕ) → (I → ℝ) → (Fin n → X) → ℝ
  | 0, _, _ => 0
  | n + 1, offset, s =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      finiteEmpiricalSliceIncrement I g n offset (e s).2 (e s).1 +
        finiteEmpiricalDeletionIncrementSum I g n
          (fun i => offset i + g i (e s).1) (e s).2

/-- For [a nonempty finite class](hyp:I), [the leave-one-out witness](goal) for [scores `g`](hyp:g),
[remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset), and [remaining sample
`rest`](hyp:rest) is at most its deletion increment at [the deleted observation `x`](hyp:x). -/
theorem finiteEmpiricalSliceWitness_le_increment {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) (x : X) :
    finiteEmpiricalSliceWitness I g n offset rest x ≤
      finiteEmpiricalSliceIncrement I g n offset rest x := by
  let i0 := finiteEmpiricalMaximizer I g n offset rest
  have hnew := finiteEmpiricalScore_le_supremum g n
    (fun i => offset i + g i x) rest i0
  rw [finiteEmpiricalScore_add_offset g n offset (fun i => g i x) i0 rest] at hnew
  unfold finiteEmpiricalSliceWitness finiteEmpiricalSliceIncrement
  rw [finiteEmpiricalSupremum_eq_score]
  change g i0 x ≤ finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest -
    finiteEmpiricalScore g n offset i0 rest
  linarith

/-- If [every score is at most one](hyp:hupper), then [each deletion increment](goal) for [a
nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset),
[remaining sample `rest`](hyp:rest), and [deleted observation `x`](hyp:x) is at most one. -/
theorem finiteEmpiricalSliceIncrement_le_one {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ)
    (hupper : ∀ i x, g i x ≤ 1) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) (x : X) :
    finiteEmpiricalSliceIncrement I g n offset rest x ≤ 1 := by
  let i1 := finiteEmpiricalMaximizer I g n (fun i => offset i + g i x) rest
  have hold := finiteEmpiricalScore_le_supremum g n offset rest i1
  have hnew := finiteEmpiricalSupremum_eq_score g n
    (fun i => offset i + g i x) rest
  rw [finiteEmpiricalScore_add_offset g n offset (fun i => g i x) i1 rest] at hnew
  unfold finiteEmpiricalSliceIncrement
  change finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest -
      finiteEmpiricalSupremum I g n offset rest ≤ 1
  change finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest =
    finiteEmpiricalScore g n offset i1 rest + g i1 x at hnew
  linarith [hupper i1 x]

/-- If [every score is at most one](hyp:hupper), then [each leave-one-out witness](goal) for [a
nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset),
[remaining sample `rest`](hyp:rest), and [deleted observation `x`](hyp:x) is at most one. -/
theorem finiteEmpiricalSliceWitness_le_one {X : Type u} {I : Type v}
    [Fintype I] [Nonempty I] (g : I → X → ℝ)
    (hupper : ∀ i x, g i x ≤ 1) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) (x : X) :
    finiteEmpiricalSliceWitness I g n offset rest x ≤ 1 := by
  exact hupper _ _

/-- If [an index `i`](hyp:i) attains [the finite empirical supremum](hyp:hmax) for [a nonempty
finite class](hyp:I), [scores `g`](hyp:g), [coordinate count `n`](hyp:n), [offsets
`offset`](hyp:offset), and [sample `s`](hyp:s), then [the sum of all recursive deletion increments
is at most the selected score minus its initial offset](goal). -/
theorem finiteEmpiricalDeletionIncrementSum_le_score_sub_offset
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (n : ℕ) (offset : I → ℝ) (s : Fin n → X) (i : I)
    (hmax : finiteEmpiricalSupremum I g n offset s =
      finiteEmpiricalScore g n offset i s) :
    finiteEmpiricalDeletionIncrementSum I g n offset s ≤
      finiteEmpiricalScore g n offset i s - offset i := by
  induction n generalizing offset with
  | zero => simp [finiteEmpiricalDeletionIncrementSum, finiteEmpiricalScore]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let x := (e s).1
      let rest := (e s).2
      let updated : I → ℝ := fun j => offset j + g j x
      have hscore : finiteEmpiricalScore g (n + 1) offset i s =
          finiteEmpiricalScore g n updated i rest := by
        simpa [e, x, rest, updated] using finiteEmpiricalScore_succ g n offset i s
      have hsup : finiteEmpiricalSupremum I g (n + 1) offset s =
          finiteEmpiricalSupremum I g n updated rest := by
        simpa [e, x, rest, updated] using finiteEmpiricalSupremum_succ g n offset s
      have hmaxTail : finiteEmpiricalSupremum I g n updated rest =
          finiteEmpiricalScore g n updated i rest := by
        rw [← hsup, ← hscore]
        exact hmax
      have htail := ih updated rest hmaxTail
      have hold := finiteEmpiricalScore_le_supremum g n offset rest i
      have hupdated : finiteEmpiricalScore g n updated i rest =
          finiteEmpiricalScore g n offset i rest + g i x := by
        simpa [updated] using
          finiteEmpiricalScore_add_offset g n offset (fun j => g j x) i rest
      have hhead : finiteEmpiricalSliceIncrement I g n offset rest x ≤ g i x := by
        unfold finiteEmpiricalSliceIncrement
        rw [hmaxTail, hupdated]
        linarith
      change finiteEmpiricalSliceIncrement I g n offset rest x +
          finiteEmpiricalDeletionIncrementSum I g n updated rest ≤
        finiteEmpiricalScore g (n + 1) offset i s - offset i
      rw [hscore, hupdated]
      change _ ≤ finiteEmpiricalScore g n offset i rest + g i x - offset i
      change finiteEmpiricalDeletionIncrementSum I g n updated rest ≤
        finiteEmpiricalScore g n updated i rest - updated i at htail
      dsimp [updated] at htail
      linarith

/-- For [a nonempty finite class](hyp:I), [scores `g`](hyp:g), [coordinate count `n`](hyp:n),
and [sample `s`](hyp:s), [the sum of all recursive deletion increments from zero offset is at
most the finite empirical supremum](goal). -/
theorem finiteEmpiricalDeletionIncrementSum_le_supremum
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (n : ℕ) (s : Fin n → X) :
    finiteEmpiricalDeletionIncrementSum I g n (fun _ => 0) s ≤
      finiteEmpiricalSupremum I g n (fun _ => 0) s := by
  let i := finiteEmpiricalMaximizer I g n (fun _ => 0) s
  have h := finiteEmpiricalDeletionIncrementSum_le_score_sub_offset
    g n (fun _ => 0) s i (finiteEmpiricalSupremum_eq_score g n (fun _ => 0) s)
  rw [finiteEmpiricalSupremum_eq_score]
  simpa [i] using h

/-- If [every score is measurable](hyp:hg) and [every parameterized offset is
measurable](hyp:hoffset), then the [finite empirical supremum is jointly measurable in the
parameter and sample](goal) for a [nonempty finite class](hyp:I), [coordinate count `n`](hyp:n),
and [offset family `offset`](hyp:offset). -/
@[fun_prop]
theorem measurable_finiteEmpiricalSupremum_param
    {X P : Type u} {I : Type v} [MeasurableSpace X] [MeasurableSpace P]
    [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ)
    (offset : P → I → ℝ) (hoffset : ∀ i, Measurable (fun p => offset p i)) :
    Measurable (fun q : P × (Fin n → X) =>
      finiteEmpiricalSupremum I g n (offset q.1) q.2) := by
  letI : MeasurableSpace I := ⊤
  let score : I → P × (Fin n → X) → ℝ := fun i q =>
    finiteEmpiricalScore g n (offset q.1) i q.2
  have hscore : ∀ i, Measurable (score i) := by
    intro i
    dsimp [score, finiteEmpiricalScore]
    fun_prop
  have hselect : Measurable (finiteClassMaximizer I score) :=
    measurable_finiteClassMaximizer hscore
  have hjoint : Measurable (fun q : I × (P × (Fin n → X)) => score q.1 q.2) :=
    measurable_from_prod_countable_right hscore
  have hselected : Measurable (fun q => score (finiteClassMaximizer I score q) q) := by
    simpa only [Function.comp_def, id_eq] using
      hjoint.comp (hselect.prodMk measurable_id)
  rw [show (fun q : P × (Fin n → X) =>
      finiteEmpiricalSupremum I g n (offset q.1) q.2) =
      (fun q => score (finiteClassMaximizer I score q) q) by
    funext q
    apply le_antisymm
    · rw [finiteEmpiricalSupremum_eq_score]
      exact finiteClassMaximizer_spec score q _
    · exact finiteEmpiricalScore_le_supremum g n (offset q.1) q.2 _]
  exact hselected

/-- If [every score is measurable](hyp:hg) and [every parameterized offset is
measurable](hyp:hoffset), then the [recursive deletion-increment sum is jointly measurable in
the parameter and sample](goal) for a [nonempty finite class](hyp:I), [coordinate count
n](hyp:n), and [offset family offset](hyp:offset). -/
@[fun_prop]
theorem measurable_finiteEmpiricalDeletionIncrementSum_param
    {X P : Type u} {I : Type v} [MeasurableSpace X] [MeasurableSpace P]
    [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ)
    (offset : P → I → ℝ) (hoffset : ∀ i, Measurable (fun p => offset p i)) :
    Measurable (fun q : P × (Fin n → X) =>
      finiteEmpiricalDeletionIncrementSum I g n (offset q.1) q.2) := by
  induction n generalizing P with
  | zero => simp [finiteEmpiricalDeletionIncrementSum]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let updated : (P × X) → I → ℝ := fun q i => offset q.1 i + g i q.2
      have hupdated : ∀ i, Measurable (fun q => updated q i) := by
        intro i
        dsimp [updated]
        fun_prop
      have hnew : Measurable (fun q : (P × X) × (Fin n → X) =>
          finiteEmpiricalSupremum I g n (updated q.1) q.2) :=
        measurable_finiteEmpiricalSupremum_param g hg n updated hupdated
      have hold : Measurable (fun q : (P × X) × (Fin n → X) =>
          finiteEmpiricalSupremum I g n (offset q.1.1) q.2) :=
        (measurable_finiteEmpiricalSupremum_param g hg n offset hoffset).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have htail := ih (P := P × X) updated hupdated
      change Measurable (fun q : P × (Fin (n + 1) → X) =>
        finiteEmpiricalSliceIncrement I g n (offset q.1) (e q.2).2 (e q.2).1 +
          finiteEmpiricalDeletionIncrementSum I g n
            (updated (q.1, (e q.2).1)) (e q.2).2)
      have hpair : Measurable (fun q : P × (Fin (n + 1) → X) =>
          ((q.1, (e q.2).1), (e q.2).2)) := by fun_prop
      unfold finiteEmpiricalSliceIncrement
      exact ((hnew.sub hold).add htail).comp hpair

/-- If [every score is measurable](hyp:hg), then the [recursive sum of deletion increments is
measurable](goal) for a [nonempty finite class](hyp:I), [coordinate count `n`](hyp:n), and
[offsets `offset`](hyp:offset). -/
@[fun_prop]
theorem measurable_finiteEmpiricalDeletionIncrementSum
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ) (offset : I → ℝ) :
    Measurable (finiteEmpiricalDeletionIncrementSum I g n offset) := by
  let paramOffset : (Fin n → X) → I → ℝ := fun _ => offset
  have h := measurable_finiteEmpiricalDeletionIncrementSum_param g hg n paramOffset
    (fun _ => measurable_const)
  exact h.comp (measurable_id.prodMk measurable_id)

/-- If [every score is bounded in absolute value by `B`](hyp:hbound) and [above by
one](hyp:hupper), then the [recursive deletion-increment sum has absolute value at most
`n * max B 1`](goal) for a [nonempty finite class](hyp:I), [coordinate count `n`](hyp:n),
[offsets `offset`](hyp:offset), and [sample `s`](hyp:s). -/
theorem abs_finiteEmpiricalDeletionIncrementSum_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) {B : ℝ} (hbound : ∀ i x, |g i x| ≤ B)
    (hupper : ∀ i x, g i x ≤ 1) (n : ℕ) (offset : I → ℝ) (s : Fin n → X) :
    |finiteEmpiricalDeletionIncrementSum I g n offset s| ≤
      (n : ℝ) * max B 1 := by
  induction n generalizing offset with
  | zero => simp [finiteEmpiricalDeletionIncrementSum]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let updated : I → ℝ := fun i => offset i + g i (e s).1
      have hhead : |finiteEmpiricalSliceIncrement I g n offset (e s).2 (e s).1| ≤
          max B 1 := by
        have hw : -B ≤ finiteEmpiricalSliceWitness I g n offset (e s).2 (e s).1 :=
          neg_le_of_abs_le (hbound _ _)
        rw [abs_le]
        exact ⟨(neg_le_neg (le_max_left B 1)).trans
            (hw.trans (finiteEmpiricalSliceWitness_le_increment g n offset _ _)),
          (finiteEmpiricalSliceIncrement_le_one g hupper n offset _ _).trans
            (le_max_right B 1)⟩
      change |finiteEmpiricalSliceIncrement I g n offset (e s).2 (e s).1 +
          finiteEmpiricalDeletionIncrementSum I g n updated (e s).2| ≤ _
      calc
        _ ≤ |finiteEmpiricalSliceIncrement I g n offset (e s).2 (e s).1| +
            |finiteEmpiricalDeletionIncrementSum I g n updated (e s).2| := abs_add_le _ _
        _ ≤ max B 1 + (n : ℝ) * max B 1 := add_le_add hhead (ih updated (e s).2)
        _ = ((n + 1 : ℕ) : ℝ) * max B 1 := by push_cast; ring

/-- If [every class member has mean zero](hyp:hmean), then [the leave-one-out witness has mean
zero](goal) under [the probability law `mu`](hyp:mu) for [a nonempty finite class](hyp:I),
[remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset), and [remaining sample
`rest`](hyp:rest). -/
theorem integral_finiteEmpiricalSliceWitness_eq_zero
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) (g : I → X → ℝ)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    ∫ x, finiteEmpiricalSliceWitness I g n offset rest x ∂mu = 0 := by
  exact hmean _

/-- If [every class member has second moment at most `sigma2`](hyp:hsecond), then [the
leave-one-out witness has second moment at most `sigma2`](goal) under [the law `mu`](hyp:mu) for
[a nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets
`offset`](hyp:offset), and [remaining sample `rest`](hyp:rest). -/
theorem integral_finiteEmpiricalSliceWitness_sq_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) (g : I → X → ℝ) {sigma2 : ℝ}
    (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    (∫ x, (finiteEmpiricalSliceWitness I g n offset rest x) ^ 2 ∂mu) ≤ sigma2 := by
  exact hsecond _

/-- If [every class member is measurable](hyp:hg), then [the leave-one-out witness](goal) for [a
nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset),
and [remaining sample `rest`](hyp:rest) is measurable. -/
@[fun_prop]
theorem measurable_finiteEmpiricalSliceWitness
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    Measurable (finiteEmpiricalSliceWitness I g n offset rest) := by
  exact hg _

/-- If [every class member is measurable](hyp:hg), then [the deletion increment](goal) for [a
nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset),
and [remaining sample `rest`](hyp:rest) is measurable. -/
@[fun_prop]
theorem measurable_finiteEmpiricalSliceIncrement
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    Measurable (finiteEmpiricalSliceIncrement I g n offset rest) := by
  letI : MeasurableSpace I := ⊤
  let score : I → X → ℝ := fun i x =>
    finiteEmpiricalScore g n (fun j => offset j + g j x) i rest
  have hscore : ∀ i, Measurable (score i) := by
    intro i
    dsimp [score, finiteEmpiricalScore]
    fun_prop
  have hselect : Measurable (finiteClassMaximizer I score) :=
    measurable_finiteClassMaximizer hscore
  have hjoint : Measurable (fun p : I × X => score p.1 p.2) :=
    measurable_from_prod_countable_right hscore
  have hnew : Measurable (fun x => score (finiteClassMaximizer I score x) x) := by
    simpa only [Function.comp_def, id_eq] using
      hjoint.comp (hselect.prodMk measurable_id)
  have hnew' : Measurable (fun x =>
      finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest) := by
    rw [show (fun x =>
        finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest) =
        fun x => score (finiteClassMaximizer I score x) x by
      funext x
      apply le_antisymm
      · rw [finiteEmpiricalSupremum_eq_score]
        exact finiteClassMaximizer_spec score x _
      · exact finiteEmpiricalScore_le_supremum g n
          (fun i => offset i + g i x) rest _]
    exact hnew
  exact hnew'.sub measurable_const

private lemma integrable_of_measurable_abs_le
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    {f : X → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f mu := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-- Under [a probability law `mu`](hyp:mu), if [every class member is measurable](hyp:hg) and
[bounded in absolute value by `B`](hyp:hbound), then [the leave-one-out witness is
integrable](goal) for [a nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n),
[offsets `offset`](hyp:offset), and [remaining sample `rest`](hyp:rest). -/
@[fun_prop]
theorem integrable_finiteEmpiricalSliceWitness
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    {mu : Measure X} [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    Integrable (finiteEmpiricalSliceWitness I g n offset rest) mu :=
  integrable_of_measurable_abs_le
    (measurable_finiteEmpiricalSliceWitness g hg n offset rest) (fun x => hbound _ x)

/-- Under [a probability law `mu`](hyp:mu), if [every class member is measurable](hyp:hg),
[bounded in absolute value by `B`](hyp:hbound), and [at most one](hyp:hupper),
then [the deletion increment is integrable](goal) for [a nonempty finite class](hyp:I), [remaining
coordinate count `n`](hyp:n), [offsets `offset`](hyp:offset), and [remaining sample
`rest`](hyp:rest). -/
@[fun_prop]
theorem integrable_finiteEmpiricalSliceIncrement
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    {mu : Measure X} [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    Integrable (finiteEmpiricalSliceIncrement I g n offset rest) mu := by
  refine integrable_of_measurable_abs_le (C := max B 1)
    (measurable_finiteEmpiricalSliceIncrement g hg n offset rest) ?_
  intro x
  have hwBound : -B ≤ finiteEmpiricalSliceWitness I g n offset rest x :=
    (neg_le_of_abs_le (hbound _ x))
  have hlower := finiteEmpiricalSliceWitness_le_increment g n offset rest x
  have hupper' := finiteEmpiricalSliceIncrement_le_one g hupper n offset rest x
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_max_left B 1)).trans (hwBound.trans hlower)
  · exact hupper'.trans (le_max_right B 1)

/-- Under [a probability law `mu`](hyp:mu), if [every class member is measurable](hyp:hg),
[bounded in absolute value by `B`](hyp:hbound), and [at most one](hyp:hupper),
then [the deletion increment has nonnegative mean](goal) whenever [the class is centered](hyp:hmean),
for [a nonempty finite class](hyp:I), [remaining coordinate count `n`](hyp:n), [offsets
`offset`](hyp:offset), and [remaining sample `rest`](hyp:rest). -/
theorem integral_finiteEmpiricalSliceIncrement_nonneg
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    {mu : Measure X} [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0) (n : ℕ)
    (offset : I → ℝ) (rest : Fin n → X) :
    0 ≤ ∫ x, finiteEmpiricalSliceIncrement I g n offset rest x ∂mu := by
  have hY := integrable_finiteEmpiricalSliceWitness (mu := mu) g hg hbound n offset rest
  have hDelta := integrable_finiteEmpiricalSliceIncrement (mu := mu)
    g hg hbound hupper n offset rest
  have hle := integral_mono hY hDelta
    (finiteEmpiricalSliceWitness_le_increment g n offset rest)
  rw [integral_finiteEmpiricalSliceWitness_eq_zero mu g hmean n offset rest] at hle
  exact hle

end Causalean.Stat.Concentration.EntropyMethod
